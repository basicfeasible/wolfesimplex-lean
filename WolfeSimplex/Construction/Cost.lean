import Mathlib

/-!
# Arithmetic resource model

`Computation` records a value, the number of integer arithmetic operations and
maximum operand/result magnitude. `bookkeeping` separately charges control and
materialization in an explicit array-arithmetic model. Resource-monitor evaluation
is outside the model. `bitBudget` charges every operation the quadratic
cost of the largest operand/result. This is an explicit arithmetic bit-cost
model, not a theorem about Lean's compiler or a particular Turing machine.
-/

namespace WolfeSimplex.Construction

structure Computation (α : Type) where
  value : α
  operations : ℕ
  peak : ℕ
  bookkeeping : ℕ := 0

namespace Computation

variable {α β : Type}

instance : Monad Computation where
  pure x := ⟨x, 0, 0, 1⟩
  bind x f := let y := f x.value
              ⟨y.value, x.operations + y.operations, max x.peak y.peak,
                x.bookkeeping + y.bookkeeping + 1⟩

@[simp] theorem value_pure (x : α) : (pure x : Computation α).value = x := rfl
@[simp] theorem operations_pure (x : α) : (pure x : Computation α).operations = 0 := rfl
@[simp] theorem peak_pure (x : α) : (pure x : Computation α).peak = 0 := rfl
@[simp] theorem value_bind (x : Computation α) (f : α → Computation β) :
    (x >>= f).value = (f x.value).value := rfl
@[simp] theorem operations_bind (x : Computation α) (f : α → Computation β) :
    (x >>= f).operations = x.operations + (f x.value).operations := rfl
@[simp] theorem peak_bind (x : Computation α) (f : α → Computation β) :
    (x >>= f).peak = max x.peak (f x.value).peak := rfl

/-- One binary integer arithmetic operation, with both operands and result recorded. -/
def binary (f : ℤ → ℤ → ℤ) (a b : ℤ) : Computation ℤ :=
  let z := f a b
  ⟨z, 1, max a.natAbs (max b.natAbs z.natAbs), 1⟩

def add := binary (· + ·)
def sub := binary (· - ·)
def mul := binary (· * ·)

/-- A scan explicitly performs one absolute value and one maximum per input. -/
def scanMax : List ℤ → Computation ℕ
  | [] => pure 0
  | a :: xs =>
    let r := scanMax xs
    ⟨max a.natAbs r.value, r.operations + 2, max a.natAbs (max r.value r.peak),
      r.bookkeeping + 2⟩

@[simp] theorem scanMax_operations (xs : List ℤ) :
    (scanMax xs).operations = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [scanMax, ih]; omega

@[simp] theorem scanMax_peak (xs : List ℤ) :
    (scanMax xs).peak = (scanMax xs).value := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [scanMax, ih]

@[simp] theorem scanMax_le_iff (xs : List ℤ) (b : ℕ) :
    (scanMax xs).value ≤ b ↔ ∀ a ∈ xs, a.natAbs ≤ b := by
  induction xs with
  | nil => simp [scanMax]
  | cons a xs ih => simp [scanMax, ih]

/-- Start a magnitude scan at one. The extra maximum is charged. -/
def maxAbs (xs : List ℤ) : Computation ℕ :=
  let r := scanMax xs
  ⟨max 1 r.value, r.operations + 1, max 1 r.peak, r.bookkeeping + 1⟩

@[simp] theorem maxAbs_operations (xs : List ℤ) :
    (maxAbs xs).operations = 2 * xs.length + 1 := by simp [maxAbs]
@[simp] theorem maxAbs_peak (xs : List ℤ) :
    (maxAbs xs).peak = (maxAbs xs).value := by simp [maxAbs]
@[simp] theorem maxAbs_le_iff (xs : List ℤ) (b : ℕ) :
    (maxAbs xs).value ≤ b ↔ 1 ≤ b ∧ ∀ a ∈ xs, a.natAbs ≤ b := by
  simp [maxAbs]

/-- Repeated multiplication: the exponent is not a unit-cost primitive. -/
def power (a : ℤ) : ℕ → Computation ℤ
  | 0 => pure 1
  | n + 1 => do
    let r ← power a n
    mul r a

@[simp] theorem power_value (a : ℤ) (n : ℕ) : (power a n).value = a ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, ih, mul, binary, pow_succ]
@[simp] theorem power_operations (a : ℤ) (n : ℕ) : (power a n).operations = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [power, ih, mul, binary]

theorem power_peak_le {a : ℤ} (ha : 1 ≤ a.natAbs) (n : ℕ) :
    (power a n).peak ≤ a.natAbs ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih =>
    simp only [power, peak_bind, power_value, mul, binary, Int.natAbs_mul,
      Int.natAbs_pow, max_le_iff]
    have hpow := Nat.pow_le_pow_right ha (by omega : n ≤ n + 1)
    have hbase : a.natAbs ≤ a.natAbs ^ (n + 1) := by
      calc a.natAbs = a.natAbs ^ 1 := by simp
           _ ≤ _ := Nat.pow_le_pow_right ha (by omega)
    exact ⟨ih.trans hpow, hpow, hbase, by simp [pow_succ]⟩

/-- Materialize a finite table once, charging its cells' arithmetic operations.
Charge four control/cell operations per cell plus one table header. -/
def table {n : ℕ} (f : Fin n → Computation α) : Computation (Vector α n) :=
  let cells := Vector.ofFn f
  ⟨cells.map (·.value), ∑ i : Fin n, (cells[i]).operations,
    Finset.univ.sup fun i : Fin n ↦ (cells[i]).peak,
    1 + 4 * n + ∑ i : Fin n, (cells[i]).bookkeeping⟩

@[simp] theorem table_value {n : ℕ} (f : Fin n → Computation α) (i : Fin n) :
    (table f).value[i] = (f i).value := by simp [table]
@[simp] theorem table_operations {n : ℕ} (f : Fin n → Computation α) :
    (table f).operations = ∑ i : Fin n, (f i).operations := by simp [table]
@[simp] theorem table_peak {n : ℕ} (f : Fin n → Computation α) :
    (table f).peak = Finset.univ.sup fun i ↦ (f i).peak := by simp [table]

/-- An explicit materialization charge; it does not change values or arithmetic. -/
def materialize (charge : ℕ) (x : Computation α) : Computation α :=
  { x with bookkeeping := x.bookkeeping + charge }

@[simp] theorem materialize_value (charge : ℕ) (x : Computation α) :
    (materialize charge x).value = x.value := rfl
@[simp] theorem materialize_operations (charge : ℕ) (x : Computation α) :
    (materialize charge x).operations = x.operations := rfl
@[simp] theorem materialize_peak (charge : ℕ) (x : Computation α) :
    (materialize charge x).peak = x.peak := rfl
@[simp] theorem materialize_bookkeeping (charge : ℕ) (x : Computation α) :
    (materialize charge x).bookkeeping = x.bookkeeping + charge := rfl
@[simp] theorem bookkeeping_pure (x : α) :
    (pure x : Computation α).bookkeeping = 1 := rfl
@[simp] theorem bookkeeping_bind (x : Computation α) (f : α → Computation β) :
    (x >>= f).bookkeeping = x.bookkeeping + (f x.value).bookkeeping + 1 := rfl
@[simp] theorem binary_bookkeeping (f : ℤ → ℤ → ℤ) (a b : ℤ) :
    (binary f a b).bookkeeping = 1 := rfl
@[simp] theorem scanMax_bookkeeping (xs : List ℤ) :
    (scanMax xs).bookkeeping = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [scanMax, ih]; omega
@[simp] theorem maxAbs_bookkeeping (xs : List ℤ) :
    (maxAbs xs).bookkeeping = 2 * xs.length + 2 := by simp [maxAbs]
@[simp] theorem power_bookkeeping (a : ℤ) (n : ℕ) :
    (power a n).bookkeeping = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [power, ih, mul]; omega
@[simp] theorem table_bookkeeping {n : ℕ} (f : Fin n → Computation α) :
    (table f).bookkeeping = 1 + 4 * n + ∑ i : Fin n, (f i).bookkeeping := by
  simp [table]

/-- Arithmetic and control/cell operations, excluding the monitor itself. -/
def work (x : Computation α) : ℕ := x.operations + x.bookkeeping

/-- Conservative bit budget: one sign bit and quadratic arithmetic per operation. -/
def bitBudget (x : Computation α) : ℕ :=
  x.operations * (1 + Nat.size x.peak) ^ 2

end Computation
end WolfeSimplex.Construction

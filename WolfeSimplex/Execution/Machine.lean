import WolfeSimplex.Execution.Scalar

/-!
# A machine for complete, possibly history-dependent procedures

Unlike a report containing freely supplied cost fields, this interface computes
all work and numerical magnitudes by interpreting first-order instructions.
A fixed program can loop, branch, update its state array and emit supports.
Array operations use the indexed-array model documented in `Code`. Integer
quotient and remainder are primitive arithmetic operations, as are the operations
in `Code`; the bit charge is quadratic in the measured numerical width.
-/
namespace WolfeSimplex.Execution
open Code

/-- Largest literal/address in a straight-line instruction. This is part of
its numerical width, including addresses whose read returns a default zero. -/
def Code.addressBound : Code → ℕ
  | .read is => is.foldr Max.max 0
  | .readAt block is => Max.max block (is.foldr Max.max 0)
  | .literal z => z.natAbs
  | .unary _ a => a
  | .binary _ a b => Max.max a b
  | .seq a b | .par a b | .extend a b => Max.max a.addressBound b.addressBound

inductive Instruction where
  | compute (code : Code)
  | constant (destination : ℕ) (value : ℤ)
  | arithmetic (op : Binary) (destination left right : ℕ)
  | division (remainder : Bool) (destination left right : ℕ)
  | load (block addressRegister destination : ℕ)
  | store (addressRegister valueRegister : ℕ)
  | emit (block : ℕ)
  | positive (cell yes no : ℕ)
  | jump (address : ℕ)
  | halt
  deriving Repr

abbrev Program := Array Instruction

structure State where
  env : Env
  pc : ℕ := 0
  output : List (List ℤ) := []
  work : ℕ := 0
  peak : ℕ := 0
  deriving Repr

/-- An indexed state update, allocating zero cells when needed. The interpreter
charges every copied/allocated cell in this conservative array implementation. -/
def setCell (xs : List ℤ) (i : ℕ) (v : ℤ) : List ℤ :=
  (List.range (Max.max xs.length (i + 1))).map fun j ↦ if j = i then v else xs[j]?.getD 0

def replaceCurrent (s : State) (i : ℕ) (v : ℤ) : Env :=
  setCell (current s.env) i v :: s.env.drop 1

/-- One executed instruction, including control and array copying. The emitted
trace is accumulated in reverse order using constant-time list cons. -/
def advance (p : Program) (s : State) : State :=
  let control := Max.max s.peak (Max.max s.pc s.env.length)
  match p[s.pc]?.getD .halt with
  | .compute c =>
    let r := c.run s.env
    { s with
      env := r.values :: (s.env.drop 1)
      pc := s.pc + 1
      work := s.work + r.work + 4
      peak := Max.max control (Max.max c.addressBound r.peak) }
  | .constant destination value =>
    { s with
      env := replaceCurrent s destination value
      pc := s.pc + 1
      work := s.work + (current s.env).length + destination + 5
      peak := Max.max control (Max.max destination value.natAbs) }
  | .arithmetic op destination left right =>
    let x := (current s.env)[left]?.getD 0
    let y := (current s.env)[right]?.getD 0
    let z := binaryValue op x y
    { s with
      env := replaceCurrent s destination z
      pc := s.pc + 1
      work := s.work + (current s.env).length + destination + 10
      peak := Max.max control (Max.max destination (Max.max left (Max.max right
        (Max.max x.natAbs (Max.max y.natAbs z.natAbs))))) }
  | .division remainder destination left right =>
    let x := (current s.env)[left]?.getD 0
    let y := (current s.env)[right]?.getD 0
    let z := if remainder then x % y else x / y
    { s with
      env := replaceCurrent s destination z
      pc := s.pc + 1
      work := s.work + (current s.env).length + destination + 10
      peak := Max.max control (Max.max destination (Max.max left (Max.max right
        (Max.max x.natAbs (Max.max y.natAbs z.natAbs))))) }
  | .load block addressRegister destination =>
    let a := (current s.env)[addressRegister]?.getD 0
    let z := (s.env[block]?.getD [])[a.toNat]?.getD 0
    { s with
      env := replaceCurrent s destination z
      pc := s.pc + 1
      work := s.work + s.env.length + (current s.env).length + destination + 10
      peak := Max.max control (Max.max block (Max.max addressRegister
        (Max.max destination (Max.max a.natAbs z.natAbs)))) }
  | .store addressRegister valueRegister =>
    let a := (current s.env)[addressRegister]?.getD 0
    let z := (current s.env)[valueRegister]?.getD 0
    { s with
      env := replaceCurrent s a.toNat z
      pc := s.pc + 1
      work := s.work + (current s.env).length + a.toNat + 10
      peak := Max.max control (Max.max addressRegister (Max.max valueRegister
        (Max.max a.natAbs z.natAbs))) }
  | .emit block =>
    let row := s.env[block]?.getD []
    { s with
      pc := s.pc + 1
      output := row :: s.output
      work := s.work + s.env.length + 2 * row.length + 4
      peak := Max.max control (Max.max block (magnitude row)) }
  | .positive cell yes no =>
    let z := (current s.env)[cell]?.getD 0
    { s with
      pc := (if 0 < z then yes else no)
      work := s.work + s.env.length + 5
      peak := Max.max control (Max.max z.natAbs (Max.max cell (Max.max yes no))) }
  | .jump address =>
    { s with
      pc := address
      work := s.work + 2
      peak := Max.max control address }
  | .halt => { s with work := s.work + 1, peak := control }

/-- Falling off the program halts. Fuel is an external evaluator bound, not an
algorithm-provided cost: every executed instruction increments `State.work`. -/
def execute (p : Program) : ℕ → State → Option State
  | 0, _ => none
  | fuel + 1, s =>
    match p[s.pc]?.getD .halt with
    | .halt => some (advance p s)
    | _ => execute p fuel (advance p s)

/-- All completed executions have the same result, independently of fuel. -/
theorem execute_stable (p : Program) (fuel extra : ℕ) (s t : State)
    (h : execute p fuel s = some t) : execute p (fuel + extra) s = some t := by
  induction fuel generalizing s with
  | zero => simp [execute] at h
  | succ fuel ih =>
    simp only [execute] at h
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega, execute]
    split at h <;> simp_all

theorem execute_unique (p : Program) (f g : ℕ) (s t u : State)
    (ht : execute p f s = some t) (hu : execute p g s = some u) : t = u := by
  have hf := execute_stable p f g s t ht
  have hg := execute_stable p g f s u hu
  rw [Nat.add_comm g f, hf] at hg
  exact Option.some.inj hg

/-- Every executed instruction has a positive work charge. -/
theorem advance_work (p : Program) (s : State) : s.work + 1 ≤ (advance p s).work := by
  unfold advance
  split <;> dsimp <;> omega

theorem execute_work (p : Program) (fuel : ℕ) (s t : State)
    (h : execute p fuel s = some t) : s.work + 1 ≤ t.work := by
  induction fuel generalizing s with
  | zero => simp [execute] at h
  | succ fuel ih =>
    simp only [execute] at h
    split at h
    · cases h; exact advance_work p s
    · exact (advance_work p s).trans ((by omega : (advance p s).work ≤
        (advance p s).work + 1).trans (ih _ h))

end WolfeSimplex.Execution

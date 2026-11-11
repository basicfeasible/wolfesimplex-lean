import Mathlib

/-!
# First-order array/arithmetic code

The interpreter is the cost semantics. Programs have no arbitrary-function
primitive, no numeric continuation and no reported work/width fields. `extend`
materializes a cache once; subsequent instructions read its cells. `seq`, `par`
and `extend` charge control and all materialized array cells. Integer arithmetic
is primitive; bit work is the uniform quadratic charge on represented widths.
-/

namespace WolfeSimplex.Execution

inductive Unary where
  | neg | abs | sign
  deriving Repr, DecidableEq
inductive Binary where
  | add | sub | mul | max
  deriving Repr, DecidableEq

inductive Code where
  | read (indices : List ℕ)
  | readAt (block : ℕ) (indices : List ℕ)
  | literal (z : ℤ)
  | unary (op : Unary) (a : ℕ)
  | binary (op : Binary) (a b : ℕ)
  | seq (a b : Code)
  | par (a b : Code)
  | extend (cache body : Code)
  deriving Repr

/-- Interpreted results; metrics are produced exclusively by `Code.run`. -/
structure Result where
  values : List ℤ
  work : ℕ
  peak : ℕ
  deriving Repr

namespace Code

abbrev Env := List (List ℤ)

def current (env : Env) : List ℤ := env[0]?.getD []

def magnitude (xs : List ℤ) : ℕ := (xs.map Int.natAbs).foldl Max.max 0

def unaryValue : Unary → ℤ → ℤ
  | .neg, a => -a
  | .abs, a => |a|
  | .sign, a => a.sign

def binaryValue : Binary → ℤ → ℤ → ℤ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .max, a, b => Max.max a b

/-- Array semantics: list indices denote constant-time indexed cells in the
specified model. The list is its mathematical representation, not a claim about
Lean's compiled list indexing. All copies and array allocation are charged. -/
def run : Code → Env → Result
  | .read indices, xs =>
    let ys := indices.map fun i ↦ (current xs)[i]?.getD 0
    ⟨ys, 2 * indices.length + xs.length + 1, magnitude ys⟩
  | .readAt block indices, xs =>
    let ys := indices.map fun i ↦ (xs[block]?.getD [])[i]?.getD 0
    ⟨ys, 2 * indices.length + xs.length + 1, magnitude ys⟩
  | .literal z, _ => ⟨[z], 2, z.natAbs⟩
  | .unary op a, xs =>
    let x := (current xs)[a]?.getD 0
    let y := unaryValue op x
    ⟨[y], 4, Max.max x.natAbs y.natAbs⟩
  | .binary op a b, xs =>
    let x := (current xs)[a]?.getD 0
    let y := (current xs)[b]?.getD 0
    let z := binaryValue op x y
    ⟨[z], 5, Max.max x.natAbs (Max.max y.natAbs z.natAbs)⟩
  | .seq a b, xs =>
    let r := a.run xs
    let s := b.run (r.values :: xs)
    ⟨s.values, r.work + s.work + 1, Max.max r.peak s.peak⟩
  | .par a b, xs =>
    let r := a.run xs
    let s := b.run xs
    ⟨r.values ++ s.values, r.work + s.work + 2 * (r.values.length + s.values.length) + 1,
      Max.max r.peak s.peak⟩
  | .extend a b, xs =>
    let r := a.run xs
    let s := b.run (r.values :: xs)
    ⟨s.values, r.work + s.work + 1, Max.max r.peak s.peak⟩

def eval (c : Code) (xs : Env) : List ℤ := (c.run xs).values

def outputs : Code → ℕ
  | .read is | .readAt _ is => is.length
  | .literal _ | .unary _ _ | .binary _ _ _ => 1
  | .seq _ b | .extend _ b => b.outputs
  | .par a b => a.outputs + b.outputs

/-- Syntax size, including all explicitly listed input/output indices. -/
def size : Code → ℕ
  | .read is | .readAt _ is => is.length + 1
  | .literal _ | .unary _ _ | .binary _ _ _ => 1
  | .seq a b | .par a b | .extend a b => a.size + b.size + 1

@[simp] theorem length_eval (c : Code) (xs : Env) : (c.eval xs).length = c.outputs := by
  induction c generalizing xs <;> simp_all [eval, run, outputs]

theorem outputs_le_size (c : Code) : c.outputs ≤ c.size := by
  induction c <;> simp_all [outputs, size] <;> omega

theorem size_pos (c : Code) : 1 ≤ c.size := by cases c <;> simp [size] <;> omega

/-- Work follows the executed syntax; it cannot be replaced by a report. -/
theorem work_bound (c : Code) (xs : Env) :
    (c.run xs).work ≤ 10 * c.size * (xs.length + c.size + 1) := by
  induction c generalizing xs with
  | read is => simp [run, size]; nlinarith
  | readAt block is => simp [run, size]; nlinarith
  | literal z => simp [run, size]; omega
  | unary op a => simp [run, size]; omega
  | binary op a b => simp [run, size]; omega
  | seq a b ia ib =>
    have ha := ia xs
    have hb := ib (a.eval xs :: xs)
    simp only [List.length_cons] at hb
    change (a.run xs).work + (b.run (a.eval xs :: xs)).work + 1 ≤ _
    dsimp [size]
    nlinarith
  | par a b ia ib =>
    have ha := ia xs
    have hb := ib xs
    have hla := a.outputs_le_size
    have hlb := b.outputs_le_size
    change (a.run xs).work + (b.run xs).work +
      2 * ((a.eval xs).length + (b.eval xs).length) + 1 ≤ _
    simp only [length_eval]
    dsimp [size]
    nlinarith
  | extend a b ia ib =>
    have ha := ia xs
    have hb := ib (a.eval xs :: xs)
    simp only [List.length_cons] at hb
    change (a.run xs).work + (b.run (a.eval xs :: xs)).work + 1 ≤ _
    dsimp [size]
    nlinarith

/-- A table of scalar or vector subprograms. Earlier cached arrays are shared;
only the concatenation of the returned cells is copied. -/
def table (cs : List Code) : Code := cs.foldr Code.par (.read [])

@[simp] theorem table_eval (cs : List Code) (xs : Env) :
    (table cs).eval xs = cs.flatMap (fun c ↦ c.eval xs) := by
  induction cs <;> simp_all [table, eval, run]

@[simp] theorem table_size (cs : List Code) :
    (table cs).size = (cs.map (fun c ↦ c.size + 1)).sum + 1 := by
  induction cs <;> simp_all [table, size]; omega

/-- Primitive scalar expressions refer to cells of the current array. -/
def copy (i : ℕ) : Code := .read [i]
def slot (block i : ℕ) : Code := .readAt block [i]
def add (a b : Code) : Code := .seq (.par a b) (.binary .add 0 1)
def sub (a b : Code) : Code := .seq (.par a b) (.binary .sub 0 1)
def mul (a b : Code) : Code := .seq (.par a b) (.binary .mul 0 1)
def max (a b : Code) : Code := .seq (.par a b) (.binary .max 0 1)
def neg (a : Code) : Code := .seq a (.unary .neg 0)
def abs (a : Code) : Code := .seq a (.unary .abs 0)
def sign (a : Code) : Code := .seq a (.unary .sign 0)

end Code
end WolfeSimplex.Execution

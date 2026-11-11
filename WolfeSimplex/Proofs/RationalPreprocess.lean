import WolfeSimplex.Proofs.Scaling
import WolfeSimplex.Construction.Cost

/-!
# Explicit rational preprocessing

The input contains rational numbers, rather than existential witnesses that real
coefficients happen to be rational. Products of denominators clear whole rows
and the whole objective. No capacity-slack column is scaled on its own.
-/

namespace WolfeSimplex

open Finset Matrix

structure RatLP (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℚ
  b : Fin m → ℚ
  c : Fin n → ℚ

namespace RatLP

variable {m n : ℕ} (R : RatLP m n)

private theorem lp_ext {P Q : LP m n} (hA : P.A = Q.A) (hb : P.b = Q.b)
    (hc : P.c = Q.c) : P = Q := by
  cases P; cases Q; cases hA; cases hb; cases hc; rfl

private theorem intLP_ext {P Q : IntLP m n} (hA : P.A = Q.A) (hb : P.b = Q.b)
    (hc : P.c = Q.c) : P = Q := by
  cases P; cases Q; cases hA; cases hb; cases hc; rfl

def toLP : LP m n :=
  ⟨fun i j ↦ (R.A i j : ℝ), fun i ↦ (R.b i : ℝ), fun j ↦ (R.c j : ℝ)⟩

def rowFactor (i : Fin m) : ℕ := (∏ j, (R.A i j).den) * (R.b i).den
def objectiveFactor : ℕ := ∏ j, (R.c j).den

def integerize : IntLP m n where
  A := fun i j ↦ (R.A i j).num *
    (((∏ k ∈ univ.erase j, (R.A i k).den) * (R.b i).den : ℕ) : ℤ)
  b := fun i ↦ (R.b i).num * ((∏ j, (R.A i j).den : ℕ) : ℤ)
  c := fun j ↦ (R.c j).num * ((∏ k ∈ univ.erase j, (R.c k).den : ℕ) : ℤ)

theorem rowFactor_pos (i : Fin m) : 0 < R.rowFactor i :=
  Nat.mul_pos (Finset.prod_pos fun j _ ↦ (R.A i j).den_pos) (R.b i).den_pos

theorem objectiveFactor_pos : 0 < R.objectiveFactor :=
  Finset.prod_pos fun j _ ↦ (R.c j).den_pos

private theorem clear_den (q : ℚ) (t : ℕ) :
    (((q.den * t : ℕ) : ℝ) * (q : ℝ)) = ((q.num * (t : ℤ) : ℤ) : ℝ) := by
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [Rat.cast_def, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  field_simp

theorem integerize_eq_scale :
    R.integerize.toLP = R.toLP.scale (fun i ↦ (R.rowFactor i : ℝ))
      (R.objectiveFactor : ℝ) := by
  apply lp_ext
  · funext i j
    change (R.integerize.A i j : ℝ) = (R.rowFactor i : ℝ) * (R.A i j : ℝ)
    have hp := Finset.mul_prod_erase univ (fun k ↦ (R.A i k).den) (mem_univ j)
    have hrow : R.rowFactor i = (R.A i j).den *
        ((∏ k ∈ univ.erase j, (R.A i k).den) * (R.b i).den) := by
      rw [rowFactor, ← hp, Nat.mul_assoc]
    rw [hrow, clear_den]
    rfl
  · funext i
    change (R.integerize.b i : ℝ) = (R.rowFactor i : ℝ) * (R.b i : ℝ)
    rw [show R.rowFactor i = (R.b i).den * (∏ j, (R.A i j).den) by
      simp only [rowFactor, Nat.mul_comm], clear_den]
    rfl
  · funext j
    change (R.integerize.c j : ℝ) = (R.objectiveFactor : ℝ) * (R.c j : ℝ)
    have hp := Finset.mul_prod_erase univ (fun k ↦ (R.c k).den) (mem_univ j)
    rw [show R.objectiveFactor = (R.c j).den * (∏ k ∈ univ.erase j, (R.c k).den)
      from hp.symm, clear_den]
    rfl

theorem integerize_run (f : ℕ) (B : ℕ → Finset (Fin n)) :
    R.integerize.toLP.IsSimplexRunWith R.integerize.toLP.IsDantzigChoice f B ↔
      R.toLP.IsSimplexRunWith R.toLP.IsDantzigChoice f B := by
  rw [R.integerize_eq_scale]
  exact (scale_runs_main R.toLP (fun i ↦ Nat.cast_pos.mpr (R.rowFactor_pos i))
    (Nat.cast_pos.mpr R.objectiveFactor_pos)).1 f B

theorem integerize_nondegenerate (B : Finset (Fin n)) :
    R.integerize.toLP.IsNondegenerate B ↔ R.toLP.IsNondegenerate B := by
  rw [R.integerize_eq_scale]
  simp only [LP.IsNondegenerate, LP.scale_basicSol R.toLP
    (fun i ↦ Nat.cast_pos.mpr (R.rowFactor_pos i))]

theorem integerize_choice (B : Finset (Fin n)) (hB : R.toLP.IsFeasibleBasis B) (j : Fin n) :
    R.integerize.toLP.IsDantzigChoice B j ↔ R.toLP.IsDantzigChoice B j := by
  rw [R.integerize_eq_scale]
  exact R.toLP.scale_dantzig_iff (fun i ↦ Nat.cast_pos.mpr (R.rowFactor_pos i))
    (Nat.cast_pos.mpr R.objectiveFactor_pos) hB j

namespace Executed

open Construction.Computation

private theorem prod_skip (f : Fin n → ℕ) (j : Fin n) :
    (∏ k, if k = j then 1 else f k) = ∏ k ∈ univ.erase j, f k := by
  symm
  calc
    _ = ∏ k ∈ univ.erase j, (if k = j then 1 else f k) := by
      apply Finset.prod_congr rfl
      intro k hk
      simp only [ite_eq_right (Finset.mem_erase.mp hk).1]
    _ = ∏ k, (if k = j then 1 else f k) := by
      apply Finset.prod_subset (Finset.subset_univ _)
      intro k _ hk
      have hkj : k = j := by simpa using hk
      simp only [ite_eq_left hkj]

private theorem int_prod_skip (f : Fin n → ℕ) (j : Fin n) :
    (∏ k, Int.ofNat (if k = j then 1 else f k)) =
      ((∏ k ∈ univ.erase j, f k : ℕ) : ℤ) := by
  have h := congrArg (fun t : ℕ ↦ (t : ℤ)) (prod_skip f j)
  simpa only [Nat.cast_prod, Int.ofNat_eq_natCast] using h

def product : List ℤ → Construction.Computation ℤ
  | [] => pure 1
  | a :: xs => do
    let p ← product xs
    mul a p

@[simp] theorem product_value (xs : List ℤ) : (product xs).value = xs.prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [product, ih, mul, binary]

@[simp] theorem product_operations (xs : List ℤ) : (product xs).operations = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [product, ih, mul, binary]

@[simp] theorem product_bookkeeping (xs : List ℤ) :
    (product xs).bookkeeping = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [product, ih, mul]; omega

def aWeights (i : Fin m) (j : Fin n) : List ℤ :=
  (List.ofFn fun k : Fin n ↦ Int.ofNat (if k = j then 1 else (R.A i k).den)) ++
    [((R.b i).den : ℤ)]

def bWeights (i : Fin m) : List ℤ :=
  List.ofFn fun j : Fin n ↦ ((R.A i j).den : ℤ)

def cWeights (j : Fin n) : List ℤ :=
  List.ofFn fun k : Fin n ↦ Int.ofNat (if k = j then 1 else (R.c k).den)

def run : Construction.Computation (IntLP m n) := do
  let A ← table fun i : Fin m ↦ table fun j : Fin n ↦ do
    let p ← product (aWeights R i j)
    mul (R.A i j).num p
  let b ← table fun i : Fin m ↦ do
    let p ← product (bWeights R i)
    mul (R.b i).num p
  let costs ← table fun j : Fin n ↦ do
    let p ← product (cWeights R j)
    mul (R.c j).num p
  pure ⟨fun i j ↦ A[i][j], fun i ↦ b[i], fun j ↦ costs[j]⟩

theorem run_correct : (run R).value = R.integerize := by
  apply intLP_ext
  · funext i j
    simp only [run, value_bind, value_pure, table_value, integerize,
      product_value, aWeights, List.prod_append, List.prod_singleton,
      Fin.prod_ofFn, mul, binary, int_prod_skip, Nat.cast_mul, Nat.cast_prod]
  · funext i
    simp only [run, value_bind, value_pure, table_value, integerize,
      product_value, bWeights, Fin.prod_ofFn, mul, binary, Nat.cast_prod]
  · funext j
    simp only [run, value_bind, value_pure, table_value, integerize,
      product_value, cWeights, Fin.prod_ofFn, mul, binary, int_prod_skip, Nat.cast_prod]

end Executed
end RatLP
end WolfeSimplex

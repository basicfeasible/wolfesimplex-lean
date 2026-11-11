/-
The raw_sum/raw_tail/raw_get/raw_spec adapters below are adapted from
Mathlib/LinearAlgebra/Matrix/Determinant/Bird/Correctness.lean.
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0; see LICENSES/Apache-2.0.txt.
Changes: integer specialization and adapters for the local first-order program.
-/
import WolfeSimplex.Execution.Scalar
import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness

/-! Cached, division-free determinant code. Mathlib proves the mathematical
Bird recurrence. Here every matrix stage is materialized before the next stage;
a matrix lookup never re-executes an earlier stage. -/

namespace WolfeSimplex.Execution

open Code
variable {n : ℕ}

def pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : List ℤ := A.toArray.toList

@[simp] theorem pack_length {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : (pack A).length = m * n := by
  simp [pack]

theorem pack_get {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) (j : Fin n) :
    (pack A)[n * i.val + j.val]?.getD 0 = A i j := by
  have hidx : n * i.val + j.val < A.toArray.size := by
    simpa using (Fin.mkDivMod i j).isLt
  change A.toArray.toList[n * i.val + j.val]?.getD 0 = _
  calc _ = Matrix.ofArray A.toArray A.size_toArray i j := by
         simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hidx,
           Option.getD_some, Matrix.ofArray_apply, Fin.getElem_fin]
         rfl
       _ = A i j := by rw [Matrix.ofArray_toArray]

private theorem left_get (xs ys : List ℤ) (i : ℕ) (hi : i < xs.length) :
    (xs ++ ys)[i]?.getD 0 = xs[i]?.getD 0 := by
  simp [List.getElem?_append, hi]

private theorem right_get (xs ys : List ℤ) (i : ℕ) :
    (xs ++ ys)[xs.length + i]?.getD 0 = ys[i]?.getD 0 := by
  rw [List.getElem?_append_right (by omega)]
  simp

/-- Input is the original matrix followed by the current cached matrix. -/
def birdCell (n : ℕ) (i j : Fin n) : Code :=
  let diagonal := Code.sum ((List.finRange n).map fun k ↦
    if i < k then copy (n * n + n * k.val + k.val) else literal 0)
  let products := Code.sum ((List.finRange n).map fun k ↦
    if i < k then mul (copy (n * n + n * i.val + k.val)) (copy (n * k.val + j.val))
    else literal 0)
  add (mul (neg diagonal) (copy (n * i.val + j.val))) products

def birdStage (n : ℕ) : Code :=
  par (read (List.range (n * n)))
    (table (List.ofFn fun ij : Fin (n * n) ↦ birdCell n ij.divNat ij.modNat))

private theorem tail_sum (i : Fin n) (f : Fin n → ℤ) :
    ((List.finRange n).map fun k ↦ if i < k then f k else 0).sum =
      ∑ k ∈ Finset.Ioi i, f k := by
  rw [← List.sum_toFinset _ (List.nodup_finRange n), List.toFinset_finRange]
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_lt_eq_Ioi]

theorem birdCell_eval (A F : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) (env : Env) :
    (birdCell n i j).eval ((pack A ++ pack F) :: env) = [BirdDet.Spec.stepEntry A F i j] := by
  have ha (a b : Fin n) : (copy (n * a.val + b.val)).eval ((pack A ++ pack F) :: env) = [A a b] := by
    simp only [eval_copy, current, List.getElem?_cons_zero, Option.getD_some]
    rw [left_get _ _ _ (by simpa using (Fin.mkDivMod a b).isLt), pack_get]
  have hf (a b : Fin n) :
      (copy (n * n + n * a.val + b.val)).eval ((pack A ++ pack F) :: env) = [F a b] := by
    simp only [eval_copy, current, List.getElem?_cons_zero, Option.getD_some]
    have hidx : n * n + n * a.val + b.val = (pack A).length + (n * a.val + b.val) := by
      simp; omega
    rw [hidx, right_get, pack_get]
  have hd := Code.sum_eval (List.finRange n)
    (fun k ↦ if i < k then copy (n * n + n * k.val + k.val) else literal 0)
    (fun k ↦ if i < k then F k k else 0) ((pack A ++ pack F) :: env) (by
      intro k _; split <;> simp_all [eval_literal])
  have hp := Code.sum_eval (List.finRange n)
    (fun k ↦ if i < k then mul (copy (n * n + n * i.val + k.val))
      (copy (n * k.val + j.val)) else literal 0)
    (fun k ↦ if i < k then F i k * A k j else 0) ((pack A ++ pack F) :: env) (by
      intro k _
      split
      · exact eval_binary Binary.mul (hf i k) (ha k j)
      · rfl)
  unfold birdCell
  have h := eval_binary Binary.add
    (eval_binary Binary.mul (eval_unary Unary.neg hd) (ha i j)) hp
  simpa only [Code.add, Code.mul, Code.neg, binaryValue, unaryValue, tail_sum, BirdDet.Spec.stepEntry, Matrix.of_apply] using h

/-- All entries of a stage are computed once, then cached as a dense matrix. -/
theorem birdStage_eval (A F : Matrix (Fin n) (Fin n) ℤ) (env : Env) :
    (birdStage n).eval ((pack A ++ pack F) :: env) = pack A ++ pack (BirdDet.Spec.stepEntry A F) := by
  rw [birdStage, eval_par]
  have hl : (read (List.range (n * n))).eval ((pack A ++ pack F) :: env) = pack A := by
    apply List.ext_getElem
    · simp [eval, run]
    · intro k hk hk'
      simp only [eval, run, current, List.getElem?_cons_zero, Option.getD_some,
        List.getElem_map, List.getElem_range]
      rw [left_get _ _ _ (by simpa only [Code.length_eval, Code.outputs, List.length_range, pack_length] using hk)]
      simp only [List.getElem?_eq_getElem hk', Option.getD_some]
  rw [hl]
  congr 1
  have ht := table_eval_values (List.finRange (n * n))
    (fun ij : Fin (n * n) ↦ birdCell n ij.divNat ij.modNat)
    (fun ij : Fin (n * n) ↦ [BirdDet.Spec.stepEntry A F ij.divNat ij.modNat])
    ((pack A ++ pack F) :: env) (by intro ij _; exact birdCell_eval A F _ _ env)
  simpa [List.finRange, List.map_ofFn, List.flatMap_map, Function.comp_def,
    ← List.map_eq_flatMap, pack, Matrix.toArray] using ht

def determinant (n : ℕ) : Code :=
  match n with
  | 0 => literal 1
  | k + 1 =>
    seq (par (read (List.range (n * n))) (read (List.range (n * n))))
      (seq (iterateCode (birdStage n) k)
        (mul (literal ((-1 : ℤ) ^ k)) (copy (n * n))))

theorem birdStage_outputs : (birdStage n).outputs = 2 * (n * n) := by
  have h := length_eval (birdStage n) [pack (0 : Matrix (Fin n) (Fin n) ℤ) ++ pack (0 : Matrix (Fin n) (Fin n) ℤ)]
  rw [birdStage_eval] at h
  simpa [two_mul] using h.symm

theorem bird_iterate (A F : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (env : Env) :
    (iterateCode (birdStage n) k).eval ((pack A ++ pack F) :: env) =
      pack A ++ pack ((BirdDet.Spec.stepEntry A)^[k] F) := by
  induction k generalizing F env with
  | zero =>
    simp only [iterateCode, birdStage_outputs, Function.iterate_zero, id_eq]
    have hl : (pack A ++ pack F).length = 2 * (n * n) := by simp; ring
    rw [← hl, read_range]
  | succ k ih =>
    simp only [iterateCode, eval_seq, birdStage_eval, ih]
    rw [Function.iterate_succ_apply]

private theorem raw_sum (f : ℕ → ℤ) (lo : ℕ) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih =>
    rw [BirdDet.sumFrom_step n lo f hlo, ih, ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo =>
    rw [BirdDet.sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

private theorem raw_tail (i : Fin n) (f : ℕ → ℤ) :
    BirdDet.sumFrom n (i.val + 1) f = ∑ k ∈ Finset.Ioi i, f k.val := by
  rw [raw_sum]
  calc _ = ∑ k ∈ (Finset.range n).filter (i.val < ·), f k := by congr 1; ext; simp; omega
       _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
       _ = ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by
         rw [← Fin.sum_univ_eq_sum_range]
       _ = _ := by simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

private theorem raw_get (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    BirdDet.get n A.toArray i.val j.val = A i j := by
  have h := congrFun (congrFun (Matrix.ofArray_eq_of_getD A.toArray A.size_toArray) i) j
  rw [Matrix.ofArray_toArray] at h
  exact h.symm

private theorem raw_spec (A : Matrix (Fin n) (Fin n) ℤ) (t : ℕ) (i j : Fin n) :
    ((BirdDet.stepEntry n A.toArray)^[t] (BirdDet.get n A.toArray)) i.val j.val =
      ((BirdDet.Spec.stepEntry A)^[t] A) i j := by
  induction t generalizing i j with
  | zero => simpa using raw_get A i j
  | succ t ih =>
    simp_rw [Function.iterate_succ_apply', BirdDet.stepEntry_eq,
      BirdDet.Spec.stepEntry_eq, raw_tail, ih, Matrix.of_apply, raw_get]

/-- Correct determinant values are obtained by executing primitive code, rather
than calling the mathematical determinant as an uncharged operation. -/
theorem determinant_correct (A : Matrix (Fin n) (Fin n) ℤ) (env : Env) :
    (determinant n).eval (pack A :: env) = [A.det] := by
  cases n with
  | zero => simp [determinant]
  | succ k =>
    unfold determinant
    have hr : (read (List.range ((k + 1) * (k + 1)))).eval (pack A :: env) = pack A := by
      simpa using read_range (pack A) env
    simp only [eval_seq, eval_par, hr, bird_iterate]
    have hg : (copy ((k + 1) * (k + 1))).eval
        ((pack A ++ pack ((BirdDet.Spec.stepEntry A)^[k] A)) ::
          ((pack A ++ pack A) :: (pack A :: env))) =
          [((BirdDet.Spec.stepEntry A)^[k] A) 0 0] := by
      simp only [eval_copy, current, List.getElem?_cons_zero, Option.getD_some]
      have heq : (k + 1) * (k + 1) = (pack A).length + ((k + 1) * 0 + 0) := by simp
      rw [heq, right_get]
      simpa using pack_get ((BirdDet.Spec.stepEntry A)^[k] A) 0 0
    have hm := eval_binary Binary.mul (eval_literal ((-1 : ℤ) ^ k) _) hg
    have hd := BirdDet.det_eq_birdDet A.toArray A.size_toArray
    rw [Matrix.ofArray_toArray] at hd
    have hspec : BirdDet.birdDet (k + 1) A.toArray = BirdDet.Spec.birdDet A := by
      rw [BirdDet.birdDet_succ, BirdDet.Spec.birdDetSpec_succ]
      congr 1
      exact raw_spec A k 0 0
    rw [hspec] at hd
    simpa only [Code.mul, binaryValue, ← BirdDet.Spec.birdDetSpec_succ, ← hd] using hm

end WolfeSimplex.Execution

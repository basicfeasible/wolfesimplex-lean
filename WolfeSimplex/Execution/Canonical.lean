import WolfeSimplex.Execution.Atoms
import WolfeSimplex.Defs.Shield

/-! First-order canonicalization. Each determinant uses the cached division-free
program; neither inversion nor adjugation is a free interpreter primitive. -/
namespace WolfeSimplex.Execution
open Code Matrix
variable {m n : ℕ}

def basisCode (e : Fin m → Fin n) : Code :=
  table (List.ofFn fun ij : Fin (m * m) ↦ slot 0 (n * ij.divNat.val + (e ij.modNat).val))

def replaceRow (m : ℕ) (i j : Fin m) : Code :=
  table (List.ofFn fun ab : Fin (m * m) ↦
    if ab.divNat = j then literal (if ab.modNat = i then 1 else 0)
    else slot 1 (m * ab.divNat.val + ab.modNat.val))

def gCode (m : ℕ) : Code :=
  table (List.ofFn fun ij : Fin (m * m) ↦
    mul (sign (slot 0 0)) (seq (replaceRow m ij.divNat ij.modNat) (determinant m)))

def canonicalA (m n : ℕ) : Code :=
  table (List.ofFn fun ij : Fin (m * n) ↦
    Code.sum ((List.finRange m).map fun k ↦
      mul (slot 0 (m * ij.divNat.val + k.val)) (slot 3 (n * k.val + ij.modNat.val))))

def canonicalB (m : ℕ) : Code :=
  table (List.ofFn fun i : Fin m ↦ mul (literal 2)
    (Code.sum ((List.finRange m).map fun k ↦
      mul (slot 1 (m * i.val + k.val)) (slot 5 k.val))))

def canonicalC (e : Fin m → Fin n) : Code :=
  table (List.ofFn fun j : Fin n ↦
    sub (mul (abs (slot 3 0)) (slot 7 j.val))
      (Code.sum ((List.finRange m).map fun i ↦
        mul (slot 1 (n * i.val + j.val)) (slot 7 (e i).val))))

/-- Execute the canonicalization, then the supplied continuation on cache frames
`c', b', A', G, det, basis, A, b, c`. -/
def canonicalCode (e : Fin m → Fin n) (body : Code) : Code :=
  extend (basisCode e) (extend (determinant m) (extend (gCode m)
    (extend (canonicalA m n) (extend (canonicalB m) (extend (canonicalC e) body)))))

theorem basisCode_eval (P : IntLP m n) (e : Fin m → Fin n) (env : Env) :
    (basisCode e).eval (lpInput P ++ env) = pack (P.basisMat e) := by
  unfold basisCode
  rw [show pack (P.basisMat e) = List.ofFn
    (fun ij : Fin (m * m) ↦ P.basisMat e ij.divNat ij.modNat) by
      simp [pack, Matrix.toArray]]
  apply table_ofFn_eval
  intro ij
  simp only [eval_slot, lpInput, List.cons_append, List.getElem?_cons_zero,
    Option.getD_some, IntLP.basisMat, Matrix.of_apply]
  exact congrArg List.singleton (pack_get _ _ _)

theorem replaceRow_eval (A : Matrix (Fin m) (Fin m) ℤ) (d : ℤ)
    (i j : Fin m) (env : Env) :
    (replaceRow m i j).eval ([d] :: pack A :: env) = pack (A.updateRow j (Pi.single i 1)) := by
  unfold replaceRow
  rw [show pack (A.updateRow j (Pi.single i 1)) = List.ofFn
    (fun ab : Fin (m * m) ↦ (A.updateRow j (Pi.single i 1)) ab.divNat ab.modNat) by
      simp [pack, Matrix.toArray]]
  apply table_ofFn_eval
  intro ab
  simp only [Matrix.updateRow_apply, Pi.single_apply]
  split_ifs <;> simp_all only [eval_literal, eval_slot, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some, pack_get]

theorem gCode_eval (P : IntLP m n) (e : Fin m → Fin n) (env : Env) :
    (gCode m).eval ([(P.basisMat e).det] :: pack (P.basisMat e) :: env) =
      pack (P.canonG e) := by
  unfold gCode
  rw [show pack (P.canonG e) = List.ofFn
    (fun ij : Fin (m * m) ↦ P.canonG e ij.divNat ij.modNat) by
      simp [pack, Matrix.toArray]]
  apply table_ofFn_eval
  intro ij
  have hd := determinant_correct ((P.basisMat e).updateRow ij.modNat (Pi.single ij.divNat 1))
    ([(P.basisMat e).det] :: pack (P.basisMat e) :: env)
  have ha : (seq (replaceRow m ij.divNat ij.modNat) (determinant m)).eval
    ([(P.basisMat e).det] :: pack (P.basisMat e) :: env) =
      [(P.basisMat e).adjugate ij.divNat ij.modNat] := by
    rw [eval_seq, replaceRow_eval, hd, Matrix.adjugate_apply]
  have hs : (sign (slot 0 0)).eval
    ([(P.basisMat e).det] :: pack (P.basisMat e) :: env) = [(P.basisMat e).det.sign] :=
      eval_unary Unary.sign (by rfl)
  simpa only [IntLP.canonG, Matrix.smul_apply, smul_eq_mul] using mul_eval hs ha

theorem sum_fin_eval (f : Fin m → Code) (v : Fin m → ℤ) (env : Env)
    (h : ∀ i, (f i).eval env = [v i]) :
    (Code.sum ((List.finRange m).map f)).eval env = [∑ i, v i] := by
  have hs := sum_eval (List.finRange m) f v env (fun i _ ↦ h i)
  simpa [List.finRange, List.map_ofFn, List.sum_ofFn] using hs

theorem canonicalA_eval (P : IntLP m n) (e : Fin m → Fin n) (d b : List ℤ)
    (env : Env) :
    (canonicalA m n).eval (pack (P.canonG e) :: d :: b :: (lpInput P ++ env)) =
      pack (P.canonical e).A := by
  unfold canonicalA
  rw [show pack (P.canonical e).A = List.ofFn
    (fun ij : Fin (m * n) ↦ (P.canonical e).A ij.divNat ij.modNat) by
      simp [pack, Matrix.toArray]]
  apply table_ofFn_eval
  intro ij
  apply sum_fin_eval
  intro k
  apply mul_eval
  · simp only [eval_slot, List.getElem?_cons_zero, Option.getD_some, List.cons_append]
    exact congrArg List.singleton (pack_get _ _ _)
  · simp only [eval_slot, lpInput, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, List.cons_append]
    exact congrArg List.singleton (pack_get _ _ _)

theorem canonicalB_eval (P : IntLP m n) (e : Fin m → Fin n)
    (d b : List ℤ) (env : Env) :
    (canonicalB m).eval (pack (P.canonical e).A :: pack (P.canonG e) :: d :: b ::
      (lpInput P ++ env)) = List.ofFn (P.canonical e).b := by
  apply table_ofFn_eval
  intro i
  apply mul_eval (eval_literal 2 _)
  apply sum_fin_eval
  intro k
  apply mul_eval
  · simp only [eval_slot, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, List.cons_append]
    exact congrArg List.singleton (pack_get _ _ _)
  · simp only [eval_slot, lpInput, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, List.cons_append]
    simp only [List.getElem?_ofFn, dite_eq_left k.isLt, Option.getD_some]

theorem canonicalC_eval (P : IntLP m n) (e : Fin m → Fin n)
    (b : List ℤ) (env : Env) :
    (canonicalC e).eval (List.ofFn (P.canonical e).b :: pack (P.canonical e).A ::
      pack (P.canonG e) :: [(P.basisMat e).det] :: b :: (lpInput P ++ env)) =
      List.ofFn (P.canonical e).c := by
  apply table_ofFn_eval
  intro j
  apply sub_eval
  · apply mul_eval
    · exact abs_eval (by rfl)
    · simp only [eval_slot, lpInput, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some, List.cons_append]
      simp only [List.getElem?_ofFn, dite_eq_left j.isLt, Option.getD_some]
  · apply sum_fin_eval
    intro i
    apply mul_eval
    · simp only [eval_slot, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some, List.cons_append]
      exact congrArg List.singleton (pack_get _ _ _)
    · simp only [eval_slot, lpInput, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some, List.cons_append]
      simp only [List.getElem?_ofFn, dite_eq_left (e i).isLt, Option.getD_some]

/-- Correctness of the complete cached canonicalization, for every continuation. -/
theorem canonicalCode_correct (P : IntLP m n) (e : Fin m → Fin n) (body : Code)
    (env : Env) :
    (canonicalCode e body).eval (lpInput P ++ env) = body.eval
      (List.ofFn (P.canonical e).c :: List.ofFn (P.canonical e).b ::
        pack (P.canonical e).A :: pack (P.canonG e) :: [(P.basisMat e).det] ::
        pack (P.basisMat e) :: (lpInput P ++ env)) := by
  simp only [canonicalCode, eval_extend, basisCode_eval, determinant_correct, gCode_eval,
    canonicalA_eval, canonicalB_eval, canonicalC_eval]

end WolfeSimplex.Execution

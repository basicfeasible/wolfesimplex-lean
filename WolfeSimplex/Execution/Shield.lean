import WolfeSimplex.Execution.Canonical

namespace WolfeSimplex.Execution
open Code Matrix Finset
variable {m n : ℕ}

/-- The positive part implements exactly the paper's natural-valued maximum. -/
def positive (c : Code) := max c (literal 0)

def nonbasicMax (e : Fin m → Fin n) (f : Fin n → Code) : Code :=
  maxList ((List.finRange n).map fun j ↦
    if j ∈ basisOf e then literal 0 else positive (f j))

theorem nonbasicMax_eval (e : Fin m → Fin n) (f : Fin n → Code)
    (v : Fin n → ℤ) (env : Env) (h : ∀ j, (f j).eval env = [v j]) :
    (nonbasicMax e f).eval env =
      [(((univ.filter fun j ↦ j ∉ basisOf e).sup fun j ↦ (v j).toNat : ℕ) : ℤ)] := by
  have hv (j : Fin n) :
      (if j ∈ basisOf e then literal 0 else positive (f j)).eval env =
        [((if j ∈ basisOf e then 0 else (v j).toNat : ℕ) : ℤ)] := by
    split_ifs
    · rfl
    · simpa only [positive, Int.toNat_eq_max] using max_eval (h j) (eval_literal 0 env)
  have he := maxList_eval (List.finRange n)
    (fun j ↦ if j ∈ basisOf e then literal 0 else positive (f j))
    (fun j ↦ ((if j ∈ basisOf e then 0 else (v j).toNat : ℕ) : ℤ)) env (fun j _ ↦ hv j)
  have hs : (univ.sup fun j ↦ if j ∈ basisOf e then 0 else (v j).toNat) =
      (univ.filter fun j ↦ j ∉ basisOf e).sup (fun j ↦ (v j).toNat) := by
    apply Nat.le_antisymm
    · apply Finset.sup_le
      intro j _
      split_ifs with hj
      · exact Nat.zero_le _
      · exact Finset.le_sup (s := univ.filter fun j ↦ j ∉ basisOf e)
          (f := fun j ↦ (v j).toNat) (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
    · apply Finset.sup_le
      intro j hj
      have hn : j ∉ basisOf e := (Finset.mem_filter.mp hj).2
      have hh := Finset.le_sup (f := fun j ↦ if j ∈ basisOf e then 0 else (v j).toNat)
        (Finset.mem_univ j)
      simpa only [ite_eq_right hn] using hh
  apply he.trans
  have hc := fold_max_cast (List.ofFn fun j ↦ if j ∈ basisOf e then 0 else (v j).toNat)
  rw [fold_max_ofFn, hs] at hc
  simpa only [List.finRange, List.map_ofFn, Function.comp_def] using
    congrArg (fun z : ℤ ↦ [z]) hc

def shieldCoefficient (e : Fin m → Fin n) : Code :=
  add (abs (slot 4 0)) (nonbasicMax e fun j ↦
    Code.sum ((List.finRange m).map fun i ↦
      mul (slot 1 i.val) (max (slot 2 (n * i.val + j.val)) (literal 0))))

def shieldWeight (e : Fin m → Fin n) : Code :=
  add (slot 0 0) (nonbasicMax e fun j ↦
    Code.sum ((List.finRange m).map fun i ↦
      mul (slot 3 (n * i.val + j.val)) (slot 3 (n * i.val + j.val))))

def shieldEntry (e : Fin m → Fin n) (i : Fin (m + 1)) (j : Fin (n + 1)) : Code :=
    if hi : i.val < m then
      if hj : j.val < n then slot 4 (n * i.val + j.val)
      else literal 0
    else if hj : j.val < n then
      if (⟨j.val, hj⟩ : Fin n) ∈ basisOf e then literal 0 else neg (slot 1 0)
    else abs (slot 6 0)

def shieldMatrix (e : Fin m → Fin n) : Code :=
  table (List.ofFn fun ij : Fin ((m + 1) * (n + 1)) ↦ shieldEntry e ij.divNat ij.modNat)

def weightedEntry (e : Fin m → Fin n) (σ : Equiv.Perm (Fin n))
    (i : Fin (m + 1)) (j : Fin (n + 1)) : Code :=
    if hi : i.val < m then
      if hj : j.val < n then
        if (⟨j.val, hj⟩ : Fin n) ∈ basisOf e then
          if e ⟨i.val, hi⟩ = ⟨j.val, hj⟩ then
            mul (literal ((σ ⟨j.val, hj⟩).val + 1 : ℕ)) (slot 0 0)
          else literal 0
        else slot 4 (n * i.val + j.val)
      else literal 0
    else if hj : j.val < n then
      if (⟨j.val, hj⟩ : Fin n) ∈ basisOf e then literal 0
      else neg (mul (literal ((σ ⟨j.val, hj⟩).val + 1 : ℕ)) (slot 0 0))
    else mul (literal (n + 1 : ℕ)) (slot 0 0)

def weightedMatrix (e : Fin m → Fin n) (σ : Equiv.Perm (Fin n)) : Code :=
  table (List.ofFn fun ij : Fin ((m + 1) * (n + 1)) ↦ weightedEntry e σ ij.divNat ij.modNat)

/-- Copy the new right-hand side and costs after materializing the new matrix,
then present the three input frames in `A,b,c` order to the atom code. -/
def finishShield (m n : ℕ) : Code :=
  extend (par (readAt 4 (List.range m)) (literal 1))
    (extend (par (readAt 4 (List.range n)) (literal 0))
      (extend (readAt 0 (List.range (n + 1)))
        (extend (readAt 2 (List.range (m + 1)))
          (extend (readAt 4 (List.range ((m + 1) * (n + 1)))) (atomCode (m + 1) (n + 1))))))

/-- Program for the unweighted shortest-atom construction (Lemma 14). -/
def shieldCode (e : Fin m → Fin n) : Code :=
  canonicalCode e (extend (shieldCoefficient e) (extend (shieldWeight e)
    (extend (shieldMatrix e) (finishShield m n))))

/-- Program for the weighted shortest-atom construction (Lemma 17). -/
def weightedCode (e : Fin m → Fin n) (σ : Equiv.Perm (Fin n)) : Code :=
  canonicalCode e (extend (shieldCoefficient e) (extend (shieldWeight e)
    (extend (weightedMatrix e σ) (finishShield m n))))

def canonEnv (P : IntLP m n) (e : Fin m → Fin n) (env : Env) : Env :=
  List.ofFn (P.canonical e).c :: List.ofFn (P.canonical e).b ::
    pack (P.canonical e).A :: pack (P.canonG e) :: [(P.basisMat e).det] ::
    pack (P.basisMat e) :: (lpInput P ++ env)

theorem coefficient_eval (P : IntLP m n) (e : Fin m → Fin n) (env : Env) :
    (shieldCoefficient e).eval (canonEnv P e env) = [P.shieldCoeff e] := by
  apply add_eval
  · exact abs_eval (by rfl)
  · apply nonbasicMax_eval
    intro j
    apply sum_fin_eval
    intro i
    apply mul_eval
    · simp only [eval_slot, canonEnv, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some, List.getElem?_ofFn, dite_eq_left i.isLt]
    · apply max_eval _ (eval_literal 0 _)
      simp only [eval_slot, canonEnv, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
      exact congrArg List.singleton (pack_get _ i j)

theorem weight_eval (P : IntLP m n) (e : Fin m → Fin n) (env : Env) :
    (shieldWeight e).eval ([P.shieldCoeff e] :: canonEnv P e env) = [P.shieldW e] := by
  apply add_eval (by rfl)
  apply nonbasicMax_eval
  intro j
  have hs := sum_fin_eval
    (fun i : Fin m ↦ mul (slot 3 (n * i.val + j.val)) (slot 3 (n * i.val + j.val)))
    (fun i : Fin m ↦ (P.canonical e).A i j * (P.canonical e).A i j)
    ([P.shieldCoeff e] :: canonEnv P e env) (by
      intro i
      have h : (slot 3 (n * i.val + j.val)).eval
        ([P.shieldCoeff e] :: canonEnv P e env) = [(P.canonical e).A i j] := by
        simp only [eval_slot, canonEnv, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.getD_some]
        exact congrArg List.singleton (pack_get _ i j)
      exact mul_eval h h)
  simpa only [pow_two] using hs

theorem shieldEntry_eval (P : IntLP m n) (e : Fin m → Fin n) (i : Fin (m + 1))
    (j : Fin (n + 1)) (env : Env) :
    (shieldEntry e i j).eval ([P.shieldW e] :: [P.shieldCoeff e] :: canonEnv P e env) =
      [(P.shieldLP e).A i j] := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simpa [shieldEntry, IntLP.shieldLP, IntLP.Delta0] using abs_eval (by rfl)
    | cast j =>
      by_cases hj : j ∈ basisOf e
      · simp [shieldEntry, IntLP.shieldLP, hj, j.isLt]
      · simpa [shieldEntry, IntLP.shieldLP, hj, j.isLt] using neg_eval (by rfl)
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [shieldEntry, IntLP.shieldLP, i.isLt]
    | cast j =>
      simp only [shieldEntry, Fin.val_castSucc, dite_eq_left i.isLt, dite_eq_left j.isLt,
        eval_slot, canonEnv, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
      simpa [IntLP.shieldLP] using pack_get (P.canonical e).A i j

theorem weightedEntry_eval (P : IntLP m n) (e : Fin m → Fin n)
    (σ : Equiv.Perm (Fin n)) (i : Fin (m + 1)) (j : Fin (n + 1)) (env : Env) :
    (weightedEntry e σ i j).eval ([P.shieldW e] :: [P.shieldCoeff e] :: canonEnv P e env) =
      [(P.weightedLP e σ).A i j] := by
  have hw : (slot 0 0).eval
      ([P.shieldW e] :: [P.shieldCoeff e] :: canonEnv P e env) = [P.shieldW e] := rfl
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simpa [weightedEntry, IntLP.weightedLP, IntLP.shieldRank] using
        mul_eval (eval_literal ((n + 1 : ℕ) : ℤ) _) hw
    | cast j =>
      by_cases hj : j ∈ basisOf e
      · simp [weightedEntry, IntLP.weightedLP, hj, j.isLt]
      · simpa [weightedEntry, IntLP.weightedLP, IntLP.shieldRank, hj, j.isLt] using
          neg_eval (mul_eval (eval_literal (((σ j).val + 1 : ℕ) : ℤ) _) hw)
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [weightedEntry, IntLP.weightedLP, i.isLt]
    | cast j =>
      by_cases hj : j ∈ basisOf e
      · by_cases hij : e i = j
        · simpa [weightedEntry, IntLP.weightedLP, IntLP.shieldRank, hj, hij, i.isLt,
            j.isLt] using mul_eval (eval_literal (((σ j).val + 1 : ℕ) : ℤ) _) hw
        · simp [weightedEntry, IntLP.weightedLP, hj, hij, i.isLt, j.isLt]
      · simp only [weightedEntry, Fin.val_castSucc, dite_eq_left i.isLt, dite_eq_left j.isLt,
          ite_eq_right hj, eval_slot, canonEnv, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.getD_some]
        simpa [IntLP.weightedLP, hj] using
          pack_get (P.canonical e).A i j

theorem table_matrix {a b : ℕ} (f : Fin a → Fin b → Code)
    (M : Matrix (Fin a) (Fin b) ℤ) (env : Env) (h : ∀ i j, (f i j).eval env = [M i j]) :
    (table (List.ofFn fun ij : Fin (a * b) ↦ f ij.divNat ij.modNat)).eval env = pack M := by
  rw [show pack M = List.ofFn (fun ij : Fin (a * b) ↦ M ij.divNat ij.modNat) by
    simp [pack, Matrix.toArray]]
  exact table_ofFn_eval _ _ _ (fun ij ↦ h ij.divNat ij.modNat)

theorem finishShield_eval (M : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    (b : Fin m → ℤ) (c : Fin n → ℤ) (w a : List ℤ) (env : Env) :
    (finishShield m n).eval (pack M :: w :: a :: List.ofFn c :: List.ofFn b :: env) =
      pack (integerAtoms (⟨M, Fin.snoc b 1, Fin.snoc c 0⟩ : IntLP (m + 1) (n + 1))) := by
  let Q : IntLP (m + 1) (n + 1) := ⟨M, Fin.snoc b 1, Fin.snoc c 0⟩
  have hb : (par (readAt 4 (List.range m)) (literal 1)).eval
      (pack M :: w :: a :: List.ofFn c :: List.ofFn b :: env) = List.ofFn Q.b := by
    rw [eval_par, readAt_range 4 m (List.ofFn b) _ (by rfl) (by simp), eval_literal]
    simp only [Q, List.ofFn_succ_last, Fin.snoc_castSucc, Fin.snoc_last]
  have hc : (par (readAt 4 (List.range n)) (literal 0)).eval
      (List.ofFn Q.b :: pack M :: w :: a :: List.ofFn c :: List.ofFn b :: env) =
      List.ofFn Q.c := by
    rw [eval_par, readAt_range 4 n (List.ofFn c) _ (by rfl) (by simp), eval_literal]
    simp only [Q, List.ofFn_succ_last, Fin.snoc_castSucc, Fin.snoc_last]
  simp only [finishShield, eval_extend, hb, hc]
  rw [readAt_range 0 (n + 1) (List.ofFn Q.c) _ (by rfl) (by simp)]
  rw [readAt_range 2 (m + 1) (List.ofFn Q.b) _ (by rfl) (by simp)]
  rw [readAt_range 4 ((m + 1) * (n + 1)) (pack M) _ (by rfl) (by simp)]
  exact atomCode_correct Q _

/-- The unweighted preparation program computes the paper's shortest-start atoms. -/
theorem shieldCode_correct (P : IntLP m n) (e : Fin m → Fin n) (env : Env) :
    (shieldCode e).eval (lpInput P ++ env) = pack (integerAtoms (P.shieldLP e)) := by
  rw [shieldCode, canonicalCode_correct]
  change (extend (shieldCoefficient e) (extend (shieldWeight e)
    (extend (shieldMatrix e) (finishShield m n)))).eval (canonEnv P e env) = _
  rw [eval_extend, coefficient_eval, eval_extend, weight_eval, eval_extend]
  have hm := table_matrix (shieldEntry e) (P.shieldLP e).A _
    (fun i j ↦ shieldEntry_eval P e i j env)
  change (shieldMatrix e).eval _ = _ at hm
  rw [hm]
  exact finishShield_eval _ _ _ _ _ _

/-- The weighted program computes the atoms used for minnorm initialization. -/
theorem weightedCode_correct (P : IntLP m n) (e : Fin m → Fin n)
    (σ : Equiv.Perm (Fin n)) (env : Env) :
    (weightedCode e σ).eval (lpInput P ++ env) = pack (integerAtoms (P.weightedLP e σ)) := by
  rw [weightedCode, canonicalCode_correct]
  change (extend (shieldCoefficient e) (extend (shieldWeight e)
    (extend (weightedMatrix e σ) (finishShield m n)))).eval (canonEnv P e env) = _
  rw [eval_extend, coefficient_eval, eval_extend, weight_eval, eval_extend]
  have hm := table_matrix (weightedEntry e σ) (P.weightedLP e σ).A _
    (fun i j ↦ weightedEntry_eval P e σ i j env)
  change (weightedMatrix e σ).eval _ = _ at hm
  rw [hm]
  exact finishShield_eval _ _ _ _ _ _

end WolfeSimplex.Execution

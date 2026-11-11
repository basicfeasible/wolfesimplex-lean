import WolfeSimplex.Proofs.NNLSBasic

/-!
# Lawson–Hanson simulates Wolfe's method (paper: Lemma 20 (`lem:lh-wolfe`))

* `lh_wolfe_major_main`: one major cycle.
* The trace of a partial execution (`trace`): the outer states are `(S_g, ζ^{S_g})` for a
  partial Wolfe run `S_0, …, S_g` with the linopt rule, the inner states are `(S', cλ)`
  for the states `(S', λ)` reached by minor cycles; with a bound on the number of steps.
* The construction of an execution from a Wolfe run.
* `lh_wolfe_main`.
-/

namespace WolfeSimplex

open Finset Matrix Wolfe

namespace NNLS

variable {N D : ℕ} {p : Fin N → Fin D → ℝ}

/-! ### One major cycle -/

/-- `m` minor cycles. -/
def MinorIter (p : Fin N → Fin D → ℝ) : ℕ → Wolfe.State N → Wolfe.State N → Prop
  | 0, a, b => a = b
  | m + 1, a, b => ∃ c, MinorIter p m a c ∧ MinorCycle p c b

lemma MinorIter.reach {m : ℕ} {a b : Wolfe.State N} (h : MinorIter p m a b) :
    Relation.ReflTransGen (MinorCycle p) a b := by
  induction m generalizing b with
  | zero => cases h; exact Relation.ReflTransGen.refl
  | succ m ih =>
    obtain ⟨c, h1, h2⟩ := h
    exact (ih h1).tail h2

lemma MinorIter.card {m : ℕ} {a b : Wolfe.State N} (h : MinorIter p m a b) :
    b.S.card + m = a.S.card := by
  induction m generalizing b with
  | zero => cases h; rfl
  | succ m ih =>
    obtain ⟨c, h1, -, -, i, hi, -, hS⟩ := h
    have := ih h1
    rw [hS, card_erase_of_mem hi]
    have : 1 ≤ c.S.card := card_pos.2 ⟨i, hi⟩
    omega

variable {S : Finset (Fin N)} {j : Fin N}

/-- The hypothesis of Lemma 20 (`lem:lh-wolfe`) for one major cycle. -/
def HS (p : Fin N → Fin D → ℝ) (W0 : Wolfe.State N) : Prop :=
  ∀ s s', Relation.ReflTransGen (MinorCycle p) W0 s →
    MinorCycle p s s' → ∀ i ∈ s.S, ∀ i' ∈ s.S, s'.lam i = 0 → s'.lam i' = 0 → i = i'

lemma reach_inv (hS : IsCorral p S) (hj : j ∈ improving p (affineMin p S))
    (hs : HS p ⟨insert j S, affineCoeffs p S⟩) {w : Wolfe.State N}
    (h : Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ w) :
    WInv p w ∧ SZ p w := by
  refine ⟨?_, fun s' hmc ↦ hs w s' h hmc⟩
  induction h with
  | refl => exact winv_start hS hj
  | tail hab hbc ih => exact minor_inv ih (fun s' hmc ↦ hs _ s' hab hmc) hbc

lemma start_eq (hS : IsCorral p S) :
    (⟨.inner, insert j S, LH.lsSol (nnlsMatrix p) (nnlsRhs D) S⟩ : LH.State N) =
      ⟨.inner, (⟨insert j S, affineCoeffs p S⟩ : Wolfe.State N).S,
        (1 + normSq (affineMin p S))⁻¹ • (⟨insert j S, affineCoeffs p S⟩ : Wolfe.State N).lam⟩ := by
  rw [lsSol_eq hS.1 hS.2.1]

/-- Lemma 20 (`lem:lh-wolfe`) for one major cycle, LH to Wolfe. -/
lemma major_fwd (hS : IsCorral p S) (hj : j ∈ improving p (affineMin p S))
    (hs : HS p ⟨insert j S, affineCoeffs p S⟩) (s' : LH.State N)
    (h : Relation.ReflTransGen (LH.InnerStep (nnlsMatrix p) (nnlsRhs D))
        ⟨.inner, insert j S, LH.lsSol (nnlsMatrix p) (nnlsRhs D) S⟩ s') :
    ∃ (w : Wolfe.State N) (c : ℝ), 0 < c ∧
      Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ w ∧
      s' = ⟨.inner, w.S, c • w.lam⟩ := by
  induction h with
  | refl => exact ⟨_, _, c_pos S, Relation.ReflTransGen.refl, start_eq hS⟩
  | tail _ hbc ih =>
    obtain ⟨w, c, hc, hw, rfl⟩ := ih
    obtain ⟨hinv, hsz⟩ := reach_inv hS hj hs hw
    obtain ⟨w', hmc, c', hc', rfl⟩ := inner_fwd hinv hsz hc hbc
    exact ⟨w', c', hc', hw.tail hmc, rfl⟩

/-- Lemma 20 (`lem:lh-wolfe`) for one major cycle, Wolfe to LH. -/
lemma major_bwd (hS : IsCorral p S) (hj : j ∈ improving p (affineMin p S))
    (hs : HS p ⟨insert j S, affineCoeffs p S⟩) (w : Wolfe.State N)
    (h : Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ w) :
    ∃ c : ℝ, 0 < c ∧ Relation.ReflTransGen (LH.InnerStep (nnlsMatrix p) (nnlsRhs D))
      ⟨.inner, insert j S, LH.lsSol (nnlsMatrix p) (nnlsRhs D) S⟩ ⟨.inner, w.S, c • w.lam⟩ := by
  induction h with
  | refl => exact ⟨_, c_pos S, by rw [← start_eq hS]⟩
  | @tail b c' hab hbc ih =>
    obtain ⟨c, hc, hreach⟩ := ih
    obtain ⟨hinv, hsz⟩ := reach_inv hS hj hs hab
    obtain ⟨c'', hc'', hstep⟩ := inner_bwd hinv hsz hc hbc
    exact ⟨c'', hc'', hreach.tail hstep⟩

end NNLS

open NNLS in
/-- Lemma 20 (`lem:lh-wolfe`), one major cycle. -/
theorem lh_wolfe_major_main {N D : ℕ} (p : Fin N → Fin D → ℝ) (S : Finset (Fin N))
    (hS : IsCorral p S) (j : Fin N) (hj : j ∈ improving p (affineMin p S))
    (hsingle : ∀ s s', Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ s →
      MinorCycle p s s' → ∀ i ∈ s.S, ∀ i' ∈ s.S, s'.lam i = 0 → s'.lam i' = 0 → i = i') :
    (∀ s' : LH.State N, Relation.ReflTransGen (LH.InnerStep (nnlsMatrix p) (nnlsRhs D))
        ⟨.inner, insert j S, LH.lsSol (nnlsMatrix p) (nnlsRhs D) S⟩ s' →
      ∃ (w : Wolfe.State N) (c : ℝ), 0 < c ∧
        Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ w ∧
        s' = ⟨.inner, w.S, c • w.lam⟩) ∧
    (∀ w : Wolfe.State N, Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ w →
      ∃ c : ℝ, 0 < c ∧ Relation.ReflTransGen (LH.InnerStep (nnlsMatrix p) (nnlsRhs D))
        ⟨.inner, insert j S, LH.lsSol (nnlsMatrix p) (nnlsRhs D) S⟩ ⟨.inner, w.S, c • w.lam⟩) ∧
    ∀ S' : Finset (Fin N),
      (∃ s' : LH.State N, Relation.ReflTransGen (LH.InnerStep (nnlsMatrix p) (nnlsRhs D))
          ⟨.inner, insert j S, LH.lsSol (nnlsMatrix p) (nnlsRhs D) S⟩ s' ∧
        LH.AcceptStep (nnlsMatrix p) (nnlsRhs D) s'
          ⟨.outer, S', LH.lsSol (nnlsMatrix p) (nnlsRhs D) S'⟩) ↔
      MajorCycle p S j S' := by
  refine ⟨major_fwd hS hj hsingle, major_bwd hS hj hsingle, fun S' ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨s', hreach, hacc⟩
    obtain ⟨w, c, -, hw, rfl⟩ := major_fwd hS hj hsingle s' hreach
    obtain ⟨hinv, -⟩ := reach_inv hS hj hsingle hw
    obtain ⟨hcor, heq⟩ := (accept_iff hinv.ne hinv.ai _ _).1 hacc
    simp only [LH.State.mk.injEq, true_and] at heq
    obtain ⟨rfl, -⟩ := heq
    exact ⟨hS, hj, w.lam, hw, hcor⟩
  · rintro ⟨-, -, lam', hw, hcor⟩
    obtain ⟨c, -, hreach⟩ := major_bwd hS hj hsingle _ hw
    exact ⟨_, hreach, (accept_iff hcor.1 hcor.2.1 _ _).2 ⟨hcor, rfl⟩⟩

namespace NNLS

/-! ### Executions -/

section LHFacts

variable {N d : ℕ} {E : Matrix (Fin d) (Fin N) ℝ} {f : Fin d → ℝ}

lemma pe_succ {T : ℕ} {s : ℕ → LH.State N} :
    LH.IsPartialExecution E f (T + 1) s ↔
      LH.IsPartialExecution E f T s ∧ LH.Step E f (s T) (s (T + 1)) := by
  constructor
  · rintro ⟨h0, h⟩; exact ⟨⟨h0, fun k hk ↦ h k (by omega)⟩, h T (by omega)⟩
  · rintro ⟨⟨h0, h⟩, hT⟩
    refine ⟨h0, fun k hk ↦ ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact h k hk
    · exact hT

lemma pe_mono {T T' : ℕ} {s : ℕ → LH.State N} (h : LH.IsPartialExecution E f T s)
    (hT : T' ≤ T) : LH.IsPartialExecution E f T' s :=
  ⟨h.1, fun k hk ↦ h.2 k (by omega)⟩

lemma step_of_outer {a b : LH.State N} (ha : a.phase = .outer) (h : LH.Step E f a b) :
    ∃ j, LH.AddStep E f j a b := by
  rcases h with h | h | h
  · exact h
  · rw [h.1] at ha; cases ha
  · rw [h.1] at ha; cases ha

lemma step_of_inner {a b : LH.State N} (ha : a.phase = .inner) (h : LH.Step E f a b) :
    LH.AcceptStep E f a b ∨ LH.InnerStep E f a b := by
  rcases h with ⟨j, h⟩ | h | h
  · rw [h.1] at ha; cases ha
  · exact Or.inl h
  · exact Or.inr h

lemma outerSets_zero (s : ℕ → LH.State N) :
    LH.outerSets 0 s = if (s 0).phase = .outer then [(s 0).F] else [] := by
  unfold LH.outerSets
  split_ifs with h <;> simp [h]

lemma outerSets_succ (t : ℕ) (s : ℕ → LH.State N) :
    LH.outerSets (t + 1) s = LH.outerSets t s ++
      (if (s (t + 1)).phase = .outer then [(s (t + 1)).F] else []) := by
  unfold LH.outerSets
  rw [List.range_succ, List.filter_append, List.map_append]
  congr 1
  split_ifs with h <;> simp [h]

lemma addedSets_zero (s : ℕ → LH.State N) : LH.addedSets 0 s = [] := by
  simp [LH.addedSets]

lemma addedSets_succ (t : ℕ) (s : ℕ → LH.State N) :
    LH.addedSets (t + 1) s = LH.addedSets t s ++
      (if (s t).phase = .outer then [(s (t + 1)).F \ (s t).F] else []) := by
  unfold LH.addedSets
  rw [List.range_succ, List.filter_append, List.map_append]
  congr 1
  split_ifs with h <;> simp [h]

lemma numAdds_succ (t : ℕ) (s : ℕ → LH.State N) :
    LH.numAdds (t + 1) s = LH.numAdds t s + (if (s t).phase = .outer then 1 else 0) := by
  unfold LH.numAdds
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

lemma numAdds_eq (t : ℕ) (s : ℕ → LH.State N) : LH.numAdds t s = (LH.addedSets t s).length := by
  induction t with
  | zero => simp [LH.numAdds, addedSets_zero]
  | succ t ih =>
    rw [numAdds_succ, addedSets_succ, List.length_append, ih]
    split_ifs <;> simp

lemma outerSets_congr {t : ℕ} {s s' : ℕ → LH.State N} (h : ∀ i ≤ t, s i = s' i) :
    LH.outerSets t s = LH.outerSets t s' := by
  induction t with
  | zero => rw [outerSets_zero, outerSets_zero, h 0 le_rfl]
  | succ t ih =>
    rw [outerSets_succ, outerSets_succ, ih (fun i hi ↦ h i (by omega)), h (t + 1) le_rfl]

lemma addedSets_congr {t : ℕ} {s s' : ℕ → LH.State N} (h : ∀ i ≤ t, s i = s' i) :
    LH.addedSets t s = LH.addedSets t s' := by
  induction t with
  | zero => rw [addedSets_zero, addedSets_zero]
  | succ t ih =>
    rw [addedSets_succ, addedSets_succ, ih (fun i hi ↦ h i (by omega)), h (t + 1) le_rfl,
      h t (by omega)]

end LHFacts

variable {N D : ℕ} {p : Fin N → Fin D → ℝ} {S : Finset (Fin N)}

lemma resid_zero (j : Fin N) : LH.resid (nnlsMatrix p) (nnlsRhs D) 0 j = 1 := by
  rw [resid_eq]; simp

lemma insert_sdiff_self {j : Fin N} (hj : j ∉ S) : insert j S \ S = {j} := by
  ext x; simp only [mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact h1
    · exact absurd h1 h2
  · rintro rfl; exact ⟨Or.inl rfl, hj⟩

/-- At an outer state `(S, ζ^S)` for a corral `S`, Lawson–Hanson may add `j` iff the
linopt rule may insert `j` (from Lemma 19 (`lem:nnls-ls`)). -/
lemma add_iff (hS : IsCorral p S) (j : Fin N) (b : LH.State N) :
    LH.AddStep (nnlsMatrix p) (nnlsRhs D) j ⟨.outer, S, LH.lsSol (nnlsMatrix p) (nnlsRhs D) S⟩ b ↔
      IsLinoptChoice p S j ∧ b = ⟨.inner, insert j S, LH.lsSol (nnlsMatrix p) (nnlsRhs D) S⟩ := by
  have hr := resid_lsSol hS.1 hS.2.1
  have hc := c_pos (p := p) S
  set c := (1 + normSq (affineMin p S))⁻¹
  set w := affineMin p S
  have himp : ∀ i, i ∈ improving p w ↔ gap p i w < 0 := fun i ↦ by simp [improving]
  have key : (j ∉ S ∧ 0 < -gap p j w * c ∧ ∀ k ∉ S, -gap p k w * c ≤ -gap p j w * c) ↔
      IsLinoptChoice p S j := by
    constructor
    · rintro ⟨-, h2, h3⟩
      have hg : gap p j w < 0 := by
        by_contra h; push Not at h; nlinarith
      refine ⟨(himp j).2 hg, fun i hi ↦ ?_⟩
      have := h3 i (not_mem_of_improving hS.1 hS.2.1 hi)
      have h4 : gap p j w ≤ gap p i w := by nlinarith
      unfold gap at h4; linarith
    · rintro ⟨hj, hmin⟩
      have hg := (himp j).1 hj
      refine ⟨not_mem_of_improving hS.1 hS.2.1 hj, by nlinarith, fun k _ ↦ ?_⟩
      have : gap p j w ≤ gap p k w := by
        by_cases hk : k ∈ improving p w
        · have := hmin k hk; unfold gap; linarith
        · rw [himp] at hk; push Not at hk; linarith
      nlinarith
  simp only [LH.AddStep, true_and, hr]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨key.1 ⟨h1, h2, h3⟩, h4⟩
  · rintro ⟨h, h4⟩
    obtain ⟨h1, h2, h3⟩ := key.2 h
    exact ⟨h1, h2, h3, h4⟩

lemma stopped_iff (hS : IsCorral p S) :
    LH.IsStopped (nnlsMatrix p) (nnlsRhs D)
        ⟨.outer, S, LH.lsSol (nnlsMatrix p) (nnlsRhs D) S⟩ ↔ improving p (affineMin p S) = ∅ := by
  have hr := resid_lsSol hS.1 hS.2.1
  have hc := c_pos (p := p) S
  simp only [LH.IsStopped, true_and, hr]
  constructor
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    have h1 := h j (not_mem_of_improving hS.1 hS.2.1 hj)
    simp only [improving, mem_filter, mem_univ, true_and] at hj
    nlinarith
  · intro h j _
    have : j ∉ improving p (affineMin p S) := by rw [h]; exact notMem_empty j
    simp only [improving, mem_filter, mem_univ, true_and, not_lt] at this
    nlinarith

/-- The first two steps of an execution whose first added label is `k`. -/
lemma first_two {k : Fin N} {T : ℕ} {s : ℕ → LH.State N}
    (h : LH.IsPartialExecution (nnlsMatrix p) (nnlsRhs D) T s) (hT : 1 ≤ T)
    (h1 : (s 1).F = {k}) :
    s 1 = ⟨.inner, {k}, 0⟩ ∧
      (2 ≤ T → s 2 = ⟨.outer, {k}, LH.lsSol (nnlsMatrix p) (nnlsRhs D) {k}⟩) := by
  have hst0 := h.2 0 (by omega)
  rw [h.1] at hst0
  obtain ⟨j, -, -, -, -, hb⟩ := step_of_outer rfl hst0
  have hF : insert j (∅ : Finset (Fin N)) = {k} := by rw [← h1, hb]; rfl
  have hs1 : s 1 = ⟨.inner, {k}, 0⟩ := by
    rw [hb]; show (⟨.inner, insert j ∅, 0⟩ : LH.State N) = _; rw [hF]
  refine ⟨hs1, fun hT2 ↦ ?_⟩
  have hst1 := h.2 1 (by omega)
  rw [hs1] at hst1
  rcases step_of_inner rfl hst1 with hacc | hinn
  · exact ((accept_iff (singleton_nonempty k) (corral_singleton k).2.1 _ _).1 hacc).2
  · exact absurd hinn (no_inner_of_corral (corral_singleton k) _ _)

/-! ### The trace of a partial execution -/

/-- The hypothesis of Lemma 20 (`lem:lh-wolfe`) (runs). -/
def HSingle (p : Fin N → Fin D → ℝ) (k : Fin N) : Prop :=
  ∀ f S, IsPartialWolfeRunWith p (IsLinoptChoice p) f S → S 0 = {k} →
    ∀ j, IsLinoptChoice p (S f) j → HS p ⟨insert j (S f), affineCoeffs p (S f)⟩

/-- Every major cycle of a partial linopt run from `{k}` has at most `M` minor cycles. -/
def HBound (p : Fin N → Fin D → ℝ) (k : Fin N) (M : ℕ) : Prop :=
  ∀ g R, IsPartialWolfeRunWith p (IsLinoptChoice p) g R → R 0 = {k} →
    ∀ j, IsLinoptChoice p (R g) j → ∀ m w,
      MinorIter p m ⟨insert j (R g), affineCoeffs p (R g)⟩ w → m ≤ M

lemma hbound_N (k : Fin N) : HBound p k N := by
  intro g R _ _ j _ m w h
  have h1 := h.card
  have h2 := card_le_univ (insert j (R g))
  simp only [Fintype.card_fin] at h2
  simp only at h1
  omega

/-- The state of a partial execution at step `t` (see the module doc). -/
def Trace (p : Fin N → Fin D → ℝ) (k : Fin N) (M : ℕ) (s : ℕ → LH.State N) (t : ℕ) : Prop :=
  ∃ (g : ℕ) (R : ℕ → Finset (Fin N)) (js : ℕ → Fin N),
    IsPartialWolfeRunWith p (IsLinoptChoice p) g R ∧ R 0 = {k} ∧
    (∀ l < g, IsLinoptChoice p (R l) (js l) ∧ MajorCycle p (R l) (js l) (R (l + 1))) ∧
    LH.outerSets t s = ∅ :: (List.range (g + 1)).map R ∧
    ((s t = ⟨.outer, R g, LH.lsSol (nnlsMatrix p) (nnlsRhs D) (R g)⟩ ∧
        LH.addedSets t s = {k} :: (List.range g).map (fun l ↦ {js l}) ∧
        t ≤ 2 + (M + 2) * g) ∨
      (IsLinoptChoice p (R g) (js g) ∧
        LH.addedSets t s = {k} :: (List.range (g + 1)).map (fun l ↦ {js l}) ∧
        ∃ (m : ℕ) (w : Wolfe.State N) (c : ℝ),
          MinorIter p m ⟨insert (js g) (R g), affineCoeffs p (R g)⟩ w ∧
          0 < c ∧ s t = ⟨.inner, w.S, c • w.lam⟩ ∧ t ≤ 2 + (M + 2) * g + 1 + m))

lemma trace_start {k : Fin N} {M T : ℕ} {s : ℕ → LH.State N}
    (h : LH.IsPartialExecution (nnlsMatrix p) (nnlsRhs D) T s) (hT : 2 ≤ T)
    (h1 : (s 1).F = {k}) : Trace p k M s 2 := by
  obtain ⟨hs1, hs2⟩ := first_two h (by omega) h1
  have hs2 := hs2 hT
  refine ⟨0, fun _ ↦ {k}, fun _ ↦ k,
    ⟨fun _ _ ↦ corral_singleton k, fun l hl ↦ absurd hl (Nat.not_lt_zero _)⟩, rfl,
    fun l hl ↦ absurd hl (Nat.not_lt_zero _), ?_, Or.inl ⟨hs2, ?_, by omega⟩⟩
  · rw [outerSets_succ, outerSets_succ, outerSets_zero, h.1, hs1, hs2]
    simp [LH.init]
  · rw [addedSets_succ, addedSets_succ, addedSets_zero, h.1, hs1]
    simp [LH.init]

lemma trace_step {k : Fin N} {M t : ℕ} {s : ℕ → LH.State N} (hs : HSingle p k)
    (hb : HBound p k M) (htr : Trace p k M s t)
    (hstep : LH.Step (nnlsMatrix p) (nnlsRhs D) (s t) (s (t + 1))) :
    Trace p k M s (t + 1) := by
  obtain ⟨g, R, js, hR, hR0, hmaj, hout, hcase⟩ := htr
  have hcor : IsCorral p (R g) := hR.1 g le_rfl
  set G := (M + 2) * g with hG
  rcases hcase with ⟨hst, hadd, hbd⟩ | ⟨hjs, hadd, m, w, c, hmi, hc, hst, hbd⟩
  · rw [hst] at hstep
    obtain ⟨j, hj⟩ := step_of_outer rfl hstep
    obtain ⟨hlin, hnext⟩ := (add_iff hcor j _).1 hj
    set js' : ℕ → Fin N := fun l ↦ if l = g then j else js l with hjs'def
    have hjs' : ∀ l < g, js' l = js l := fun l hl ↦ by simp [js', hl.ne]
    have hjg : js' g = j := by simp [js']
    have hjR : j ∉ R g := not_mem_of_improving hcor.1 hcor.2.1 hlin.1
    refine ⟨g, R, js', hR, hR0, fun l hl ↦ by rw [hjs' l hl]; exact hmaj l hl, ?_,
      Or.inr ⟨by rw [hjg]; exact hlin, ?_, 0, ⟨insert j (R g), affineCoeffs p (R g)⟩, _,
        by rw [hjg]; rfl, c_pos (p := p) (R g), ?_, ?_⟩⟩
    · rw [outerSets_succ, hout, hnext]; simp
    · rw [addedSets_succ, hadd, hst, hnext]
      simp only [↓reduceIte, insert_sdiff_self hjR, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, hjg, List.cons_append, List.cons.injEq, true_and]
      congr 1
      exact List.map_congr_left fun l hl ↦ by rw [hjs' l (List.mem_range.1 hl)]
    · rw [hnext, lsSol_eq hcor.1 hcor.2.1]
    · omega
  · have hreach := hmi.reach
    obtain ⟨hinv, hsz⟩ := reach_inv hcor hjs.1 (hs g R hR hR0 (js g) hjs) hreach
    rw [hst] at hstep
    rcases step_of_inner rfl hstep with hacc | hinn
    · obtain ⟨hwc, hnext⟩ := (accept_iff hinv.ne hinv.ai _ _).1 hacc
      have hmM := hb g R hR hR0 (js g) hjs m w hmi
      set R' : ℕ → Finset (Fin N) := fun l ↦ if l ≤ g then R l else w.S with hR'def
      have hR'le : ∀ l ≤ g, R' l = R l := fun l hl ↦ by simp [R', hl]
      have hR'g1 : R' (g + 1) = w.S := by simp [R']
      have hmajc : MajorCycle p (R g) (js g) w.S := ⟨hcor, hjs.1, w.lam, hreach, hwc⟩
      have hmaj' : ∀ l < g + 1,
          IsLinoptChoice p (R' l) (js l) ∧ MajorCycle p (R' l) (js l) (R' (l + 1)) := by
        intro l hl
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
        · rw [hR'le l hl.le, hR'le (l + 1) hl]; exact hmaj l hl
        · rw [hR'le l le_rfl, hR'g1]; exact ⟨hjs, hmajc⟩
      have hR' : IsPartialWolfeRunWith p (IsLinoptChoice p) (g + 1) R' := by
        refine ⟨fun l hl ↦ ?_, fun l hl ↦ ⟨js l, hmaj' l hl⟩⟩
        rcases Nat.lt_or_ge g l with hgl | hlg
        · rw [show l = g + 1 by omega, hR'g1]; exact hwc
        · rw [hR'le l hlg]; exact hR.1 l hlg
      refine ⟨g + 1, R', js, hR', by rw [hR'le 0 (Nat.zero_le _)]; exact hR0, hmaj', ?_,
        Or.inl ⟨?_, ?_, ?_⟩⟩
      · rw [outerSets_succ, hout, hnext]
        have e1 : (List.range (g + 1)).map R' = (List.range (g + 1)).map R :=
          List.map_congr_left fun l hl ↦ hR'le l (Nat.lt_succ_iff.1 (List.mem_range.1 hl))
        rw [List.range_succ (n := g + 1), List.map_append, e1]
        simp [hR'g1]
      · rw [hnext, hR'g1]
      · rw [addedSets_succ, hadd, hst]; simp
      · have : (M + 2) * (g + 1) = G + M + 2 := by rw [hG]; ring
        rw [this]; omega
    · obtain ⟨w', hmc, c', hc', hnext⟩ := inner_fwd hinv hsz hc hinn
      refine ⟨g, R, js, hR, hR0, hmaj, ?_, Or.inr ⟨hjs, ?_, m + 1, w', c', ⟨w, hmi, hmc⟩, hc',
        hnext, by omega⟩⟩
      · rw [outerSets_succ, hout, hnext]; simp
      · rw [addedSets_succ, hadd, hst]; simp

lemma trace {k : Fin N} {M T : ℕ} {s : ℕ → LH.State N} (hs : HSingle p k) (hb : HBound p k M)
    (h : LH.IsPartialExecution (nnlsMatrix p) (nnlsRhs D) T s) (h1 : (s 1).F = {k}) :
    ∀ t, 2 ≤ t → t ≤ T → Trace p k M s t := by
  intro t ht2 htT
  induction t, ht2 using Nat.le_induction with
  | base => exact trace_start h htT h1
  | succ t ht ih => exact trace_step hs hb (ih (by omega)) (h.2 t (by omega))

lemma init_not_stopped (k : Fin N) :
    ¬ LH.IsStopped (nnlsMatrix p) (nnlsRhs D) LH.init := by
  rintro ⟨-, h⟩
  have := h k (notMem_empty k)
  simp only [LH.init] at this
  rw [resid_zero] at this
  norm_num at this

/-- Lemma 20 (`lem:lh-wolfe`): from an execution to a Wolfe run. -/
lemma exec_fwd {k : Fin N} (hs : HSingle p k) {T : ℕ} {s : ℕ → LH.State N}
    (h : LH.IsExecution (nnlsMatrix p) (nnlsRhs D) T s) (h1 : (s 1).F = {k}) :
    ∃ (f : ℕ) (R : ℕ → Finset (Fin N)) (js : ℕ → Fin N),
      IsWolfeRunWith p (IsLinoptChoice p) f R ∧ R 0 = {k} ∧
      (∀ l < f, IsLinoptChoice p (R l) (js l) ∧ MajorCycle p (R l) (js l) (R (l + 1))) ∧
      LH.outerSets T s = ∅ :: (List.range (f + 1)).map R ∧
      LH.addedSets T s = {k} :: (List.range f).map (fun l ↦ {js l}) ∧
      LH.numAdds T s = f + 1 := by
  obtain ⟨hpe, hstop⟩ := h
  have hT1 : 1 ≤ T := by
    by_contra h0
    obtain rfl : T = 0 := by omega
    rw [hpe.1] at hstop
    exact init_not_stopped k hstop
  have hT2 : 2 ≤ T := by
    by_contra h0
    obtain rfl : T = 1 := by omega
    rw [(first_two hpe le_rfl h1).1] at hstop
    exact absurd hstop.1 (by simp)
  obtain ⟨g, R, js, hR, hR0, hmaj, hout, hcase⟩ :=
    trace hs (hbound_N k) hpe h1 T hT2 le_rfl
  rcases hcase with ⟨hst, hadd, -⟩ | ⟨-, -, m, w, c, -, -, hst, -⟩
  · rw [hst] at hstop
    refine ⟨g, R, js, ⟨hR, (stopped_iff (hR.1 g le_rfl)).1 hstop⟩, hR0, hmaj, hout, hadd, ?_⟩
    rw [numAdds_eq, hadd]; simp
  · rw [hst] at hstop
    exact absurd hstop.1 (by simp)

/-! ### From a Wolfe run to an execution -/

/-- `X` is reachable by a partial execution whose first added label is `k`, with the
lists `L` of outer sets and `A` of added sets. -/
def Reach (p : Fin N → Fin D → ℝ) (k : Fin N) (X : LH.State N) (L A : List (Finset (Fin N))) :
    Prop :=
  ∃ t s, LH.IsPartialExecution (nnlsMatrix p) (nnlsRhs D) t s ∧ 1 ≤ t ∧ (s 1).F = {k} ∧
    LH.outerSets t s = L ∧ LH.addedSets t s = A ∧ s t = X

lemma reach_extend {k : Fin N} {X Y : LH.State N} {L A : List (Finset (Fin N))}
    (h : Reach p k X L A) (hstep : LH.Step (nnlsMatrix p) (nnlsRhs D) X Y) :
    Reach p k Y (L ++ if Y.phase = .outer then [Y.F] else [])
      (A ++ if X.phase = .outer then [Y.F \ X.F] else []) := by
  obtain ⟨t, s, hpe, ht1, hs1, hL, hA, hX⟩ := h
  set s' : ℕ → LH.State N := fun i ↦ if i ≤ t then s i else Y with hs'def
  have hs' : ∀ i ≤ t, s' i = s i := fun i hi ↦ by simp [s', hi]
  have hY : s' (t + 1) = Y := by simp [s']
  refine ⟨t + 1, s', pe_succ.2 ⟨⟨by rw [hs' 0 (Nat.zero_le _)]; exact hpe.1, fun i hi ↦ ?_⟩, ?_⟩,
    by omega, by rw [hs' 1 ht1]; exact hs1, ?_, ?_, hY⟩
  · rw [hs' i hi.le, hs' (i + 1) hi]; exact hpe.2 i hi
  · rw [hs' t le_rfl, hY, hX]; exact hstep
  · rw [outerSets_succ, outerSets_congr hs', hL, hY]
  · rw [addedSets_succ, addedSets_congr hs', hA, hY, hs' t le_rfl, hX]

lemma reach_base (k : Fin N) :
    Reach p k ⟨.outer, {k}, LH.lsSol (nnlsMatrix p) (nnlsRhs D) {k}⟩ [∅, {k}] [{k}] := by
  have h0 : Reach p k ⟨.inner, {k}, 0⟩ [∅] [{k}] := by
    set s : ℕ → LH.State N := fun i ↦ if i = 0 then LH.init else ⟨.inner, {k}, 0⟩ with hsdef
    have hs0 : s 0 = LH.init := by simp [s]
    have hs1 : s 1 = ⟨.inner, {k}, 0⟩ := by simp [s]
    refine ⟨1, s, ⟨hs0, fun i hi ↦ ?_⟩, le_rfl, by rw [hs1], ?_, ?_, hs1⟩
    · obtain rfl : i = 0 := by omega
      rw [hs0, hs1]
      refine Or.inl ⟨k, rfl, notMem_empty k, ?_, fun j _ ↦ ?_, ?_⟩
      · simp only [LH.init]; rw [resid_zero]; exact one_pos
      · simp only [LH.init]; rw [resid_zero, resid_zero]
      · simp [LH.init]
    · rw [outerSets_succ, outerSets_zero, hs0, hs1]; simp [LH.init]
    · rw [addedSets_succ, addedSets_zero, hs0, hs1]; simp [LH.init]
  have := reach_extend h0 (Or.inr (Or.inl ((accept_iff (singleton_nonempty k)
    (corral_singleton k).2.1 _ _).2 ⟨corral_singleton k, rfl⟩)))
  simpa using this

lemma reach_major {k : Fin N} {S S' : Finset (Fin N)} {j : Fin N} {L A : List (Finset (Fin N))}
    (h : Reach p k ⟨.outer, S, LH.lsSol (nnlsMatrix p) (nnlsRhs D) S⟩ L A)
    (hlin : IsLinoptChoice p S j) (hs : HS p ⟨insert j S, affineCoeffs p S⟩)
    (hmaj : MajorCycle p S j S') :
    Reach p k ⟨.outer, S', LH.lsSol (nnlsMatrix p) (nnlsRhs D) S'⟩ (L ++ [S']) (A ++ [{j}]) := by
  obtain ⟨hcor, hj, lam', hw, hcor'⟩ := hmaj
  have hjS := not_mem_of_improving hcor.1 hcor.2.1 hj
  have h1 := reach_extend h (Or.inl ⟨j, (add_iff hcor j _).2 ⟨hlin, rfl⟩⟩)
  simp only [↓reduceIte, insert_sdiff_self hjS] at h1
  have claim : ∀ w, Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ w →
      ∃ c : ℝ, 0 < c ∧ Reach p k ⟨.inner, w.S, c • w.lam⟩ L (A ++ [{j}]) := by
    intro w hw
    induction hw with
    | refl => exact ⟨_, c_pos (p := p) S, by rw [← start_eq hcor]; simpa using h1⟩
    | @tail b c' hab hbc ih =>
      obtain ⟨c, hc, hr⟩ := ih
      obtain ⟨hinv, hsz⟩ := reach_inv hcor hj hs hab
      obtain ⟨c'', hc'', hstep⟩ := inner_bwd hinv hsz hc hbc
      exact ⟨c'', hc'', by simpa using reach_extend hr (Or.inr (Or.inr hstep))⟩
  obtain ⟨c, -, hr⟩ := claim _ hw
  have := reach_extend hr (Or.inr (Or.inl ((accept_iff hcor'.1 hcor'.2.1 _ _).2 ⟨hcor', rfl⟩)))
  simpa using this

/-- Lemma 20 (`lem:lh-wolfe`): from a Wolfe run to an execution. -/
lemma exec_bwd {k : Fin N} (hs : HSingle p k) {f : ℕ} {R : ℕ → Finset (Fin N)}
    {js : ℕ → Fin N} (hrun : IsWolfeRunWith p (IsLinoptChoice p) f R) (hR0 : R 0 = {k})
    (hjs : ∀ l < f, IsLinoptChoice p (R l) (js l) ∧ MajorCycle p (R l) (js l) (R (l + 1))) :
    ∃ T s, LH.IsExecution (nnlsMatrix p) (nnlsRhs D) T s ∧ (s 1).F = {k} ∧
      LH.outerSets T s = ∅ :: (List.range (f + 1)).map R ∧
      LH.addedSets T s = {k} :: (List.range f).map (fun l ↦ {js l}) ∧
      LH.numAdds T s = f + 1 := by
  have key : ∀ g ≤ f, Reach p k ⟨.outer, R g, LH.lsSol (nnlsMatrix p) (nnlsRhs D) (R g)⟩
      (∅ :: (List.range (g + 1)).map R) ({k} :: (List.range g).map (fun l ↦ {js l})) := by
    intro g
    induction g with
    | zero => intro _; simpa [hR0] using reach_base (p := p) k
    | succ g ih =>
      intro hg
      have hpart : IsPartialWolfeRunWith p (IsLinoptChoice p) g R :=
        ⟨fun l hl ↦ hrun.1.1 l (by omega), fun l hl ↦ ⟨js l, hjs l (by omega)⟩⟩
      have := reach_major (ih (by omega)) (hjs g (by omega)).1
        (hs g R hpart hR0 (js g) (hjs g (by omega)).1) (hjs g (by omega)).2
      convert this using 1
      · rw [List.range_succ (n := g + 1), List.map_append]; rfl
      · rw [List.range_succ (n := g), List.map_append]; rfl
  obtain ⟨T, s, hpe, -, hs1, hL, hA, hX⟩ := key f le_rfl
  refine ⟨T, s, ⟨hpe, ?_⟩, hs1, hL, hA, ?_⟩
  · rw [hX]; exact (stopped_iff (hrun.1.1 f le_rfl)).2 hrun.2
  · rw [numAdds_eq, hA]; simp

end NNLS

open NNLS in
/-- Lemma 20 (`lem:lh-wolfe`), runs. -/
theorem lh_wolfe_main {N D : ℕ} (p : Fin N → Fin D → ℝ) (k : Fin N)
    (hsingle : ∀ f S, IsPartialWolfeRunWith p (IsLinoptChoice p) f S → S 0 = {k} →
      ∀ j, IsLinoptChoice p (S f) j → ∀ s s',
        Relation.ReflTransGen (MinorCycle p) ⟨insert j (S f), affineCoeffs p (S f)⟩ s →
        MinorCycle p s s' → ∀ i ∈ s.S, ∀ i' ∈ s.S, s'.lam i = 0 → s'.lam i' = 0 → i = i') :
    (∀ T s, LH.IsExecution (nnlsMatrix p) (nnlsRhs D) T s → (s 1).F = {k} →
      ∃ (f : ℕ) (S : ℕ → Finset (Fin N)) (js : ℕ → Fin N),
        IsWolfeRunWith p (IsLinoptChoice p) f S ∧ S 0 = {k} ∧
        (∀ l < f, IsLinoptChoice p (S l) (js l) ∧ MajorCycle p (S l) (js l) (S (l + 1))) ∧
        LH.outerSets T s = ∅ :: (List.range (f + 1)).map S ∧
        LH.addedSets T s = {k} :: (List.range f).map (fun l ↦ {js l}) ∧
        LH.numAdds T s = f + 1) ∧
    (∀ f (S : ℕ → Finset (Fin N)) (js : ℕ → Fin N),
      IsWolfeRunWith p (IsLinoptChoice p) f S → S 0 = {k} →
      (∀ l < f, IsLinoptChoice p (S l) (js l) ∧ MajorCycle p (S l) (js l) (S (l + 1))) →
      ∃ T s, LH.IsExecution (nnlsMatrix p) (nnlsRhs D) T s ∧ (s 1).F = {k} ∧
        LH.outerSets T s = ∅ :: (List.range (f + 1)).map S ∧
        LH.addedSets T s = {k} :: (List.range f).map (fun l ↦ {js l}) ∧
        LH.numAdds T s = f + 1) :=
  ⟨fun _ _ h h1 ↦ exec_fwd hsingle h h1, fun _ _ _ hrun hR0 hjs ↦ exec_bwd hsingle hrun hR0 hjs⟩

end WolfeSimplex

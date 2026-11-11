import WolfeSimplex.Proofs.NNLSRuns

/-!
# Lawson–Hanson on the Klee–Minty atoms (paper: Corollary 3 (`cor:intro-nnls`))

* Major cycles exist under the single-zero hypothesis (`exists_major`).
* Major cycles with at most one minor cycle (`PropOne`), as in Theorem 1 (`thm:equivalence`)(b):
bounds and the single-zero property.
* Scaling the column of the label `k` by `2` (`Et`): executions on `Et` correspond to the
  executions on `E` whose first added label is `k` (`pe_tr`).
* Corollary 3 (`cor:intro-nnls`) (`nnls_main`).
-/

namespace WolfeSimplex

open Finset Matrix Wolfe

namespace NNLS

variable {N D : ℕ} {p : Fin N → Fin D → ℝ}

/-! ### Existence of major cycles -/

lemma exists_major {S : Finset (Fin N)} {j : Fin N} (hS : IsCorral p S)
    (hj : j ∈ improving p (affineMin p S)) (hs : HS p ⟨insert j S, affineCoeffs p S⟩) :
    ∃ S', MajorCycle p S j S' := by
  have key : ∀ m, ∀ w, Relation.ReflTransGen (MinorCycle p) ⟨insert j S, affineCoeffs p S⟩ w →
      w.S.card ≤ m → ∃ S' lam', Relation.ReflTransGen (MinorCycle p)
        ⟨insert j S, affineCoeffs p S⟩ ⟨S', lam'⟩ ∧ IsCorral p S' := by
    intro m
    induction m with
    | zero =>
      intro w hw hc
      have := (reach_inv hS hj hs hw).1.ne
      rw [← Finset.card_pos] at this; omega
    | succ m ih =>
      intro w hw hc
      by_cases hcor : IsCorral p w.S
      · exact ⟨w.S, w.lam, hw, hcor⟩
      · obtain ⟨hinv, -⟩ := reach_inv hS hj hs hw
        obtain ⟨i0, hi0, -, -, -, -, -, hz, -, -⟩ := step_calc hinv hcor one_pos
        have hmc : MinorCycle p w ⟨w.S.erase i0,
            w.lam + stepLength w.lam (affineCoeffs p w.S - w.lam) •
              (affineCoeffs p w.S - w.lam)⟩ := ⟨hcor, rfl, i0, hi0, hz, rfl⟩
        refine ih _ (hw.tail hmc) ?_
        simp only
        rw [card_erase_of_mem hi0]; omega
  obtain ⟨S', lam', hw, hc⟩ := key _ _ Relation.ReflTransGen.refl le_rfl
  exact ⟨S', hS, hj, lam', hw, hc⟩

/-! ### Major cycles with at most one minor cycle -/

/-- Every minor cycle from `W0` ends at a corral, and all of them give the same support
(as in Theorem 1 (`thm:equivalence`)(b)). This holds vacuously if `W0.S` is a corral. -/
def PropOne (p : Fin N → Fin D → ℝ) (W0 : Wolfe.State N) : Prop :=
  ∀ s', MinorCycle p W0 s' → IsCorral p s'.S ∧ ∀ s'', MinorCycle p W0 s'' → s''.S = s'.S

lemma reach_one {W0 w : Wolfe.State N} (h1 : PropOne p W0)
    (h : Relation.ReflTransGen (MinorCycle p) W0 w) : w = W0 ∨ IsCorral p w.S := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hbc ih =>
    rcases ih with rfl | hcor
    · exact Or.inr (h1 _ hbc).1
    · exact absurd hcor hbc.1

lemma iter_le_one {W0 w : Wolfe.State N} (h1 : PropOne p W0) {m : ℕ}
    (h : MinorIter p m W0 w) : m ≤ 1 := by
  match m, h with
  | 0, _ => omega
  | 1, _ => omega
  | m + 2, h =>
    obtain ⟨c, ⟨d, hd, hdc⟩, hcb⟩ := h
    rcases reach_one h1 hd.reach with rfl | hdcor
    · exact absurd (h1 c hdc).1 hcb.1
    · exact absurd hdcor hdc.1

lemma hs_of_one {W0 : Wolfe.State N} (h1 : PropOne p W0) : HS p W0 := by
  intro s s' hreach hmc i hi i' hi' hz hz'
  rcases reach_one h1 hreach with rfl | hcor
  · obtain ⟨hnc, hlam, -⟩ := hmc
    have m1 : MinorCycle p s ⟨s.S.erase i, s'.lam⟩ := ⟨hnc, hlam, i, hi, hz, rfl⟩
    have m2 : MinorCycle p s ⟨s.S.erase i', s'.lam⟩ := ⟨hnc, hlam, i', hi', hz', rfl⟩
    have he : s.S.erase i' = s.S.erase i := (h1 _ m1).2 _ m2
    by_contra hne
    have : i ∈ s.S.erase i' := mem_erase.2 ⟨hne, hi⟩
    rw [he] at this
    exact (notMem_erase i s.S) this
  · exact absurd hcor hmc.1

/-! ### Scaling the column of `k` -/

section Scale

variable (k : Fin N)

/-- The weights `η`: `2` for the label `k`, `1` otherwise. -/
def eta (j : Fin N) : ℝ := if j = k then 2 else 1

lemma eta_pos (j : Fin N) : 0 < eta k j := by unfold eta; split_ifs <;> norm_num

lemma eta_of_ne {j : Fin N} (h : j ≠ k) : eta k j = 1 := by simp [eta, h]

variable (p) in
/-- The matrix `Ẽ = E diag(η)`: the column of `k` is doubled. -/
def Et : Matrix (Fin (D + 1)) (Fin N) ℝ := Matrix.of fun r j ↦ eta k j * nnlsMatrix p r j

/-- `Φ`: from states for `Ẽ` to states for `E` (`ν ↦ diag(η) ν`). -/
def Phi (s : LH.State N) : LH.State N := ⟨s.phase, s.F, fun i ↦ eta k i * s.nu i⟩

/-- `Ψ`: the inverse of `Φ`. -/
noncomputable def Psi (s : LH.State N) : LH.State N := ⟨s.phase, s.F, fun i ↦ s.nu i / eta k i⟩

lemma Phi_Psi (s : LH.State N) : Phi k (Psi k s) = s := by
  obtain ⟨ph, F, ν⟩ := s
  simp only [Phi, Psi, LH.State.mk.injEq, true_and]
  funext i; have := (eta_pos k i).ne'; field_simp

lemma Psi_Phi (s : LH.State N) : Psi k (Phi k s) = s := by
  obtain ⟨ph, F, ν⟩ := s
  simp only [Phi, Psi, LH.State.mk.injEq, true_and]
  funext i; have := (eta_pos k i).ne'; field_simp

lemma Phi_inj {a b : LH.State N} : Phi k a = Phi k b ↔ a = b :=
  ⟨fun h ↦ by rw [← Psi_Phi k a, h, Psi_Phi], fun h ↦ h ▸ rfl⟩

lemma Phi_init : Phi k (LH.init : LH.State N) = LH.init := by
  simp only [Phi, LH.init, LH.State.mk.injEq, true_and]
  funext i; simp

lemma Et_mulVec (ν : Fin N → ℝ) :
    Et p k *ᵥ ν = nnlsMatrix p *ᵥ (fun i ↦ eta k i * ν i) := by
  funext r
  simp only [mulVec, dotProduct, Et, of_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

lemma Et_resSq (ν : Fin N → ℝ) :
    LH.resSq (Et p k) (nnlsRhs D) ν = LH.resSq (nnlsMatrix p) (nnlsRhs D) (fun i ↦ eta k i * ν i) := by
  unfold LH.resSq; rw [Et_mulVec]

lemma Et_resid (ν : Fin N → ℝ) (j : Fin N) :
    LH.resid (Et p k) (nnlsRhs D) ν j =
      eta k j * LH.resid (nnlsMatrix p) (nnlsRhs D) (fun i ↦ eta k i * ν i) j := by
  unfold LH.resid
  rw [Et_mulVec]
  simp only [mulVec, dotProduct, transpose_apply, Et, of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

lemma Et_isLsSol (F : Finset (Fin N)) (ζ : Fin N → ℝ) :
    LH.IsLsSolOf (Et p k) (nnlsRhs D) F ζ ↔
      LH.IsLsSolOf (nnlsMatrix p) (nnlsRhs D) F (fun i ↦ eta k i * ζ i) := by
  constructor
  · rintro ⟨hout, hmin⟩
    refine ⟨fun i hi ↦ by simp [hout i hi], fun ζ' h' ↦ ?_⟩
    have := hmin (fun i ↦ ζ' i / eta k i) (fun i hi ↦ by simp [h' i hi])
    rw [Et_resSq, Et_resSq] at this
    convert this using 2
    funext i; have := (eta_pos k i).ne'; field_simp
  · rintro ⟨hout, hmin⟩
    refine ⟨fun i hi ↦ ?_, fun ζ' h' ↦ ?_⟩
    · have := hout i hi
      exact (mul_eq_zero.1 this).resolve_left (eta_pos k i).ne'
    · rw [Et_resSq, Et_resSq]
      exact hmin _ (fun i hi ↦ by simp [h' i hi])

lemma Et_lsSol {F : Finset (Fin N)}
    (huniq : ∀ ζ, LH.IsLsSolOf (nnlsMatrix p) (nnlsRhs D) F ζ ↔
      ζ = LH.lsSol (nnlsMatrix p) (nnlsRhs D) F) :
    LH.lsSol (Et p k) (nnlsRhs D) F = fun i ↦ LH.lsSol (nnlsMatrix p) (nnlsRhs D) F i / eta k i := by
  set Z := LH.lsSol (nnlsMatrix p) (nnlsRhs D) F
  have hex : LH.IsLsSolOf (Et p k) (nnlsRhs D) F (fun i ↦ Z i / eta k i) := by
    rw [Et_isLsSol]
    convert (huniq Z).2 rfl using 1
    funext i; have := (eta_pos k i).ne'; field_simp
  have hspec := Classical.epsilon_spec (p := LH.IsLsSolOf (Et p k) (nnlsRhs D) F) ⟨_, hex⟩
  rw [Et_isLsSol, huniq] at hspec
  change LH.lsSol (Et p k) (nnlsRhs D) F = _
  funext i
  have := congrFun hspec i
  have hη := (eta_pos k i).ne'
  rw [← this]; field_simp; rfl

lemma ratio_eq (η ν z : ℝ) (hη : η ≠ 0) : ν / (ν - z / η) = η * ν / (η * ν - z) := by
  have : η * ν - z = η * (ν - z / η) := by field_simp
  rw [this, mul_div_mul_left _ _ hη]

/-- One step for `Ẽ` is one step for `E` (under `Φ`), at a state whose set `F` has a
unique least-squares vector for `E` and contains `k` if the phase is `outer`. -/
lemma step_tr (a b : LH.State N)
    (huniq : ∀ ζ, LH.IsLsSolOf (nnlsMatrix p) (nnlsRhs D) a.F ζ ↔
      ζ = LH.lsSol (nnlsMatrix p) (nnlsRhs D) a.F)
    (hk : a.phase = .outer → k ∈ a.F) :
    LH.Step (Et p k) (nnlsRhs D) a b ↔ LH.Step (nnlsMatrix p) (nnlsRhs D) (Phi k a) (Phi k b) := by
  obtain ⟨ph, F, ν⟩ := a
  simp only at huniq hk
  set Z := LH.lsSol (nnlsMatrix p) (nnlsRhs D) F
  have hZ := Et_lsSol (k := k) huniq
  unfold LH.Step
  refine or_congr ?_ (or_congr ?_ ?_)
  · -- add
    refine exists_congr fun j ↦ ?_
    simp only [LH.AddStep, Phi]
    constructor
    · rintro ⟨hph, hj, hpos, hmax, rfl⟩
      have hkF := hk hph
      have hjk : j ≠ k := fun h ↦ hj (h ▸ hkF)
      rw [Et_resid, eta_of_ne k hjk, one_mul] at hpos
      refine ⟨hph, hj, hpos, fun k' hk' ↦ ?_, rfl⟩
      have := hmax k' hk'
      rw [Et_resid, Et_resid, eta_of_ne k hjk, eta_of_ne k (fun h ↦ hk' (by rw [h]; exact hkF)), one_mul,
        one_mul] at this
      exact this
    · rintro ⟨hph, hj, hpos, hmax, hb⟩
      have hkF := hk hph
      have hjk : j ≠ k := fun h ↦ hj (h ▸ hkF)
      refine ⟨hph, hj, by rw [Et_resid, eta_of_ne k hjk, one_mul]; exact hpos, fun k' hk' ↦ ?_, ?_⟩
      · rw [Et_resid, Et_resid, eta_of_ne k hjk, eta_of_ne k (fun h ↦ hk' (by rw [h]; exact hkF)), one_mul,
          one_mul]
        exact hmax k' hk'
      · rw [← Phi_inj k]; exact hb
  · -- accept
    simp only [LH.AcceptStep, Phi, hZ]
    have hpos : (∀ i ∈ F, 0 < Z i / eta k i) ↔ ∀ i ∈ F, 0 < Z i :=
      forall₂_congr fun i _ ↦ div_pos_iff_of_pos_right (eta_pos k i)
    rw [hpos]
    apply and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
    rw [← Phi_inj k]
    simp only [Phi, LH.State.mk.injEq]
    constructor
    · rintro ⟨h1, h2, h3⟩; refine ⟨h1, h2, ?_⟩; rw [h3]; funext i
      have := (eta_pos k i).ne'; field_simp
    · rintro ⟨h1, h2, h3⟩; refine ⟨h1, h2, ?_⟩; rw [h3]; funext i
      have := (eta_pos k i).ne'; field_simp
  · -- inner
    simp only [LH.InnerStep, Phi, hZ]
    have hneg : (∃ i ∈ F, Z i / eta k i ≤ 0) ↔ ∃ i ∈ F, Z i ≤ 0 :=
      exists_congr fun i ↦ and_congr_right fun _ ↦ by rw [div_le_iff₀ (eta_pos k i), zero_mul]
    rw [hneg]
    apply and_congr_right fun _ ↦ and_congr_right fun _ ↦ exists_congr fun ϑ ↦ ?_
    have hstep : LH.IsInnerStep F ν (fun i ↦ Z i / eta k i) ϑ ↔
        LH.IsInnerStep F (fun i ↦ eta k i * ν i) Z ϑ := by
      unfold LH.IsInnerStep
      simp only [ratio_eq _ _ _ (eta_pos k _).ne']
      constructor
      · rintro ⟨⟨i, hi, h1, h2⟩, h3⟩
        refine ⟨⟨i, hi, by rwa [div_le_iff₀ (eta_pos k i), zero_mul] at h1, h2⟩, fun i hi h ↦ ?_⟩
        exact h3 i hi (by rw [div_le_iff₀ (eta_pos k i), zero_mul]; exact h)
      · rintro ⟨⟨i, hi, h1, h2⟩, h3⟩
        refine ⟨⟨i, hi, by rw [div_le_iff₀ (eta_pos k i), zero_mul]; exact h1, h2⟩,
          fun i hi h ↦ ?_⟩
        exact h3 i hi (by rwa [div_le_iff₀ (eta_pos k i), zero_mul] at h)
    rw [hstep]
    apply and_congr_right fun _ ↦ ?_
    rw [← Phi_inj k]
    simp only [Phi, LH.State.mk.injEq]
    have hfil : F.filter (fun i ↦ ν i + ϑ * (Z i / eta k i - ν i) ≠ 0) =
        F.filter (fun i ↦ eta k i * ν i + ϑ * (Z i - eta k i * ν i) ≠ 0) := by
      apply Finset.filter_congr
      intro i _
      have hη := (eta_pos k i).ne'
      have : eta k i * ν i + ϑ * (Z i - eta k i * ν i) =
          eta k i * (ν i + ϑ * (Z i / eta k i - ν i)) := by field_simp
      rw [this]
      simp only [ne_eq, mul_eq_zero, hη, false_or]
    have hvec : (fun i ↦ eta k i * (ν + ϑ • ((fun i ↦ Z i / eta k i) - ν)) i) =
        (fun i ↦ eta k i * ν i) + ϑ • (Z - fun i ↦ eta k i * ν i) := by
      funext i
      have hη := (eta_pos k i).ne'
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
    rw [hfil, hvec]
    exact Iff.rfl

lemma stopped_tr (a : LH.State N) :
    LH.IsStopped (Et p k) (nnlsRhs D) a ↔ LH.IsStopped (nnlsMatrix p) (nnlsRhs D) (Phi k a) := by
  simp only [LH.IsStopped, Phi, Et_resid]
  apply and_congr_right fun _ ↦ forall₂_congr fun j _ ↦ ?_
  constructor
  · intro h; by_contra h'; push Not at h'; nlinarith [eta_pos k j]
  · intro h; nlinarith [eta_pos k j]

/-- The first step for `Ẽ`: the label `k` is added. -/
lemma step_init_Et (b : LH.State N) :
    LH.Step (Et p k) (nnlsRhs D) LH.init b ↔ b = ⟨.inner, {k}, 0⟩ := by
  have hr : ∀ j, LH.resid (Et p k) (nnlsRhs D) (LH.init : LH.State N).nu j = eta k j := by
    intro j
    rw [Et_resid]
    simp only [LH.init, Pi.zero_apply, mul_zero]
    rw [show (fun _ : Fin N ↦ (0 : ℝ)) = 0 from rfl, resid_zero, mul_one]
  constructor
  · intro h
    obtain ⟨j, -, -, -, hmax, hb⟩ := step_of_outer rfl h
    have hjk : j = k := by
      by_contra hjk
      have := hmax k (notMem_empty k)
      rw [hr, hr, eta_of_ne k hjk] at this
      simp [eta] at this
    subst hjk
    rw [hb]; simp [LH.init]
  · rintro rfl
    refine Or.inl ⟨k, rfl, notMem_empty k, by rw [hr]; exact eta_pos k k, fun j _ ↦ ?_, ?_⟩
    · rw [hr, hr]; unfold eta; split_ifs <;> simp_all
    · simp [LH.init]

lemma step_init_E (b : LH.State N) :
    (LH.Step (nnlsMatrix p) (nnlsRhs D) LH.init b ∧ b.F = {k}) ↔ b = ⟨.inner, {k}, 0⟩ := by
  constructor
  · rintro ⟨h, hF⟩
    obtain ⟨j, -, -, -, -, hb⟩ := step_of_outer rfl h
    rw [hb] at hF ⊢
    simp only [LH.init] at hF ⊢
    rw [hF]
  · rintro rfl
    refine ⟨Or.inl ⟨k, rfl, notMem_empty k, by simp only [LH.init]; rw [resid_zero]; exact one_pos,
      fun j _ ↦ by simp only [LH.init]; rw [resid_zero, resid_zero], by simp [LH.init]⟩, rfl⟩

/-- At every state (from step `1` on) of a partial execution on `E` whose first added
label is `k`, the set `F` is nonempty and affinely independent, and contains `k` in the
phase `outer` (if every partial linopt run from `{k}` keeps `k`). -/
lemma good {T : ℕ} {s : ℕ → LH.State N} (hs : HSingle p k)
    (hslack : ∀ g R, IsPartialWolfeRunWith p (IsLinoptChoice p) g R → R 0 = {k} → k ∈ R g)
    (h : LH.IsPartialExecution (nnlsMatrix p) (nnlsRhs D) T s) (hT : 1 ≤ T)
    (h1 : (s 1).F = {k}) :
    (s T).F.Nonempty ∧ IsAffinelyIndependent p (s T).F ∧ ((s T).phase = .outer → k ∈ (s T).F) := by
  rcases Nat.lt_or_ge T 2 with hT2 | hT2
  · obtain rfl : T = 1 := by omega
    rw [(first_two h le_rfl h1).1]
    exact ⟨singleton_nonempty k, (corral_singleton k).2.1, fun h ↦ by cases h⟩
  · obtain ⟨g, R, js, hR, hR0, -, -, hcase⟩ := trace hs (hbound_N k) h h1 T hT2 le_rfl
    rcases hcase with ⟨hst, -, -⟩ | ⟨hjs, -, m, w, c, hmi, -, hst, -⟩
    · rw [hst]
      exact ⟨(hR.1 g le_rfl).1, (hR.1 g le_rfl).2.1, fun _ ↦ hslack g R hR hR0⟩
    · have hcor := hR.1 g le_rfl
      obtain ⟨hinv, -⟩ := reach_inv hcor hjs.1 (hs g R hR hR0 (js g) hjs) hmi.reach
      rw [hst]
      exact ⟨hinv.ne, hinv.ai, fun h ↦ by cases h⟩

/-- Partial executions on `Ẽ` are exactly the `Ψ`-images of the partial executions on `E`
whose first added label is `k`. -/
lemma pe_tr (hs : HSingle p k)
    (hslack : ∀ g R, IsPartialWolfeRunWith p (IsLinoptChoice p) g R → R 0 = {k} → k ∈ R g)
    (T : ℕ) (s : ℕ → LH.State N) :
    LH.IsPartialExecution (Et p k) (nnlsRhs D) T s ↔
      LH.IsPartialExecution (nnlsMatrix p) (nnlsRhs D) T (fun t ↦ Phi k (s t)) ∧
        (1 ≤ T → (Phi k (s 1)).F = {k}) := by
  induction T with
  | zero =>
    simp only [LH.IsPartialExecution, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true,
      and_true, Nat.le_zero, one_ne_zero]
    constructor
    · intro h; rw [h, Phi_init]
    · intro h; rw [← Phi_init k] at h; exact (Phi_inj k).1 h
  | succ T ih =>
    rw [pe_succ, pe_succ, ih]
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · constructor
      · rintro ⟨⟨h0, -⟩, hst⟩
        have hs0 : s 0 = LH.init := by rw [← Phi_inj k, Phi_init]; exact h0.1
        change LH.Step _ _ (s 0) (s 1) at hst
        rw [hs0] at hst
        have hb := (step_init_Et k _).1 hst
        have hPb : Phi k (s 1) = ⟨.inner, {k}, 0⟩ := by
          rw [hb]; simp only [Phi, LH.State.mk.injEq, true_and]; funext i; simp
        have := (step_init_E (p := p) k (Phi k (s 1))).2 hPb
        refine ⟨⟨h0, ?_⟩, fun _ ↦ this.2⟩
        change LH.Step _ _ (Phi k (s 0)) (Phi k (s 1))
        rw [hs0, Phi_init]; exact this.1
      · rintro ⟨⟨h0, hst⟩, h1⟩
        refine ⟨⟨h0, fun h ↦ absurd h (by omega)⟩, ?_⟩
        have hs0 : s 0 = LH.init := by rw [← Phi_inj k, Phi_init]; exact h0.1
        change LH.Step _ _ (Phi k (s 0)) (Phi k (s 1)) at hst
        rw [hs0, Phi_init] at hst
        have := (step_init_E (p := p) k (Phi k (s 1))).1 ⟨hst, h1 le_rfl⟩
        change LH.Step _ _ (s 0) (s 1)
        rw [hs0, step_init_Et, ← Phi_inj k, this]
        simp only [Phi, LH.State.mk.injEq, true_and]; funext i; simp
    · constructor
      · rintro ⟨⟨h0, h1⟩, hst⟩
        have hg := good k hs hslack h0 hT (h1 hT)
        have huniq := (nnls_ls_main p _ hg.1 hg.2.1).2.1
        rw [← lsSol_eq hg.1 hg.2.1] at huniq
        exact ⟨⟨h0, (step_tr k (s T) (s (T + 1)) huniq hg.2.2).1 hst⟩, fun _ ↦ h1 hT⟩
      · rintro ⟨⟨h0, hst⟩, h1⟩
        have h1' : (Phi k (s 1)).F = {k} := h1 (by omega)
        have hg := good k hs hslack h0 hT h1'
        have huniq := (nnls_ls_main p _ hg.1 hg.2.1).2.1
        rw [← lsSol_eq hg.1 hg.2.1] at huniq
        exact ⟨⟨h0, fun _ ↦ h1'⟩, (step_tr k (s T) (s (T + 1)) huniq hg.2.2).2 hst⟩

end Scale

/-! ### The Klee–Minty atoms -/

section KM

variable {n : ℕ}

/-- The structure of the partial linopt runs from the slack atom on the atoms of
Lemma 18 (`lem:km-start`) ((LP⁺) for the Klee–Minty LP): every corral contains the slack label, and
every major cycle has at most one minor cycle, all of whose possible supports agree
(Lemma 13 (`lem:init`) in the initial phase, Theorem 1 (`thm:equivalence`)(b) afterwards). -/
lemma km_struct (hn : 1 ≤ n) {g : ℕ} {R : ℕ → Finset (Fin (2 * n + 2))}
    (hR : IsPartialWolfeRunWith ((kleeMinty n).shieldLP (kmSlack n)).atom
      (IsLinoptChoice ((kleeMinty n).shieldLP (kmSlack n)).atom) g R)
    (h0 : R 0 = {Fin.last (2 * n + 1)}) :
    Fin.last (2 * n + 1) ∈ R g ∧ ∀ j, IsLinoptChoice ((kleeMinty n).shieldLP (kmSlack n)).atom (R g) j →
      PropOne ((kleeMinty n).shieldLP (kmSlack n)).atom
        ⟨insert j (R g), affineCoeffs ((kleeMinty n).shieldLP (kmSlack n)).atom (R g)⟩ := by
  obtain ⟨hP, hB₀⟩ := KM.admissible n hn
  have h := InitRuns.shield_hyp_linopt hP hB₀
  rcases Nat.lt_or_ge g (n + 1) with hg | hg
  · have hinv := (InitRuns.init_invariant h.setup hR h0 g (by omega)).1
    refine ⟨hinv.1, fun j hj ↦ ?_⟩
    have himp := h.setup.imp (R g) hinv.1 hinv.2.1 (hinv.2.2.2 (by omega))
    have hjR : j ∈ (hat (basisOf (kmSlack n))).map Fin.castSuccEmb \ R g := himp ▸ hj.1
    rw [mem_sdiff] at hjR
    have hcor := h.setup.corral (insert j (R g)) (mem_insert_of_mem hinv.1)
      (insert_subset (by rw [InitRuns.hat_hat_eq]; exact mem_insert_of_mem hjR.1) hinv.2.1)
    intro s' hmc
    exact absurd hcor hmc.1
  · obtain ⟨B, hBrun, -, hSB⟩ := InitRuns.forward_partial h hR h0 hg
    have hRg : R g = hat (hat (B (g - (n + 1)))) := by
      have := hSB (g - (n + 1)) le_rfl
      rwa [show n + 1 + (g - (n + 1)) = g by omega] at this
    have hB := hBrun.1 (g - (n + 1)) le_rfl
    have hQB : ((kleeMinty n).shieldLP (kmSlack n)).toLP.IsFeasibleBasis
        (hat (B (g - (n + 1)))) := (h.hfeas _).2 ⟨_, hB, rfl⟩
    refine ⟨by rw [hRg]; exact IntLP.last_mem_hat, fun j hj ↦ ?_⟩
    rw [hRg] at hj ⊢
    have hj1 := hj.1
    rw [IntLP.improving_hat hQB (by omega), Finset.mem_map] at hj1
    obtain ⟨j', hj', rfl⟩ := hj1
    obtain ⟨i, hi⟩ := LP.exists_leavingLabel h.hQ.2.2.1 hQB hj'
    have hb := IntLP.thm_b h.hQ hQB hj' hi
    intro s' hmc
    refine ⟨?_, fun s'' hmc'' ↦ ?_⟩
    · rw [hb.2.2.1 s' hmc]; exact hb.2.2.2.1
    · rw [hb.2.2.1 s'' hmc'', hb.2.2.1 s' hmc]

end KM

end NNLS

open NNLS in
/-- Corollary 3 (`cor:intro-nnls`). -/
theorem nnls_main (n : ℕ) (hn : 1 ≤ n) :
    ∃ E : Matrix (Fin (n + 3)) (Fin (2 * n + 2)) ℤ,
      (∀ r j, |E r j| ≤ 2 * 10 ^ (600 * (n + 2) ^ 4)) ∧
      (∃ T s, LH.IsExecution (E.map fun z : ℤ ↦ (z : ℝ)) (nnlsRhs (n + 2)) T s) ∧
      (∀ T s, LH.IsExecution (E.map fun z : ℤ ↦ (z : ℝ)) (nnlsRhs (n + 2)) T s →
        LH.numAdds T s = 2 ^ n + n + 1) ∧
      (∀ T s, LH.IsPartialExecution (E.map fun z : ℤ ↦ (z : ℝ)) (nnlsRhs (n + 2)) T s →
        T ≤ 3 * (2 ^ n + n + 1)) := by
  obtain ⟨hP, hB₀⟩ := KM.admissible n hn
  obtain ⟨hint, hsz0, -, -, -⟩ := InitRuns.init_linopt_main (kleeMinty n) hP (kmSlack n) hB₀
  set p := ((kleeMinty n).shieldLP (kmSlack n)).atom with hpdef
  set k : Fin (2 * n + 2) := Fin.last (2 * n + 1) with hkdef
  -- the size bound (as in the proof of Lemma 18 (`lem:km-start`))
  have hsz : ∀ j r, |p j r| ≤ (10 : ℝ) ^ (600 * (n + 2) ^ 4) := by
    intro j r
    refine (hsz0 j r).trans ?_
    have hW := InitRuns.km_maxEntry n hn
    have h1 : (n + 1) * (kleeMinty n).maxEntry ≤ 10 ^ (4 * n) := by
      have : n + 1 ≤ 100 ^ n := by
        have := Nat.lt_pow_self (show 1 < 100 by norm_num) (n := n); omega
      calc (n + 1) * (kleeMinty n).maxEntry ≤ 100 ^ n * 100 ^ n := Nat.mul_le_mul this hW
        _ = 10 ^ (4 * n) := by rw [← mul_pow, pow_mul]; norm_num
    have h2 : ((n + 1) * (kleeMinty n).maxEntry) ^ (100 * (n + 2) ^ 3) ≤
        10 ^ (600 * (n + 2) ^ 4) := by
      calc ((n + 1) * (kleeMinty n).maxEntry) ^ (100 * (n + 2) ^ 3)
          ≤ (10 ^ (4 * n)) ^ (100 * (n + 2) ^ 3) := Nat.pow_le_pow_left h1 _
        _ = 10 ^ (4 * n * (100 * (n + 2) ^ 3)) := by rw [← pow_mul]
        _ ≤ 10 ^ (600 * (n + 2) ^ 4) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have : 4 * n ≤ 6 * (n + 2) := by omega
          calc 4 * n * (100 * (n + 2) ^ 3) ≤ 6 * (n + 2) * (100 * (n + 2) ^ 3) :=
                Nat.mul_le_mul_right _ this
            _ = 600 * (n + 2) ^ 4 := by ring
    exact_mod_cast h2
  -- the runs (Lemma 18 (`lem:km-start`))
  have h := InitRuns.shield_hyp_linopt hP hB₀
  obtain ⟨hd1, hd2, hd3, -⟩ := KM.dantzig n hn
  obtain ⟨hex, hall, hpart⟩ := InitRuns.km_runs hn h hd1 hd2 hd3
  have hslack : ∀ g R, IsPartialWolfeRunWith p (IsLinoptChoice p) g R → R 0 = {k} → k ∈ R g :=
    fun g R hR h0 ↦ (km_struct hn hR h0).1
  have hs : HSingle p k := fun g R hR h0 j hj ↦ hs_of_one ((km_struct hn hR h0).2 j hj)
  have hb1 : HBound p k 1 := fun g R hR h0 j hj m w hmi ↦
    iter_le_one ((km_struct hn hR h0).2 j hj) hmi
  -- the integer matrix
  choose zz hzz using hint
  let E : Matrix (Fin (n + 3)) (Fin (2 * n + 2)) ℤ :=
    Matrix.of fun r j ↦ (if j = k then 2 else 1) * Fin.snoc (α := fun _ ↦ ℤ) (zz j) 1 r
  have hE : (E.map fun z : ℤ ↦ (z : ℝ)) = Et p k := by
    ext r j
    simp only [E, Et, Matrix.map_apply, Matrix.of_apply, nnlsMatrix, eta]
    induction r using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; split_ifs <;> simp
    | cast r => simp only [Fin.snoc_castSucc]; split_ifs <;> simp [hzz]
  refine ⟨E, fun r j ↦ ?_, ?_⟩
  · have h10 : (1 : ℤ) ≤ 10 ^ (600 * (n + 2) ^ 4) := one_le_pow₀ (by norm_num)
    simp only [E, Matrix.of_apply, abs_mul]
    have hη : |(if j = k then (2 : ℤ) else 1)| ≤ 2 := by split_ifs <;> norm_num
    have hs : |Fin.snoc (α := fun _ ↦ ℤ) (zz j) 1 r| ≤ 10 ^ (600 * (n + 2) ^ 4) := by
      induction r using Fin.lastCases with
      | last => simp only [Fin.snoc_last, abs_one]; exact h10
      | cast r =>
        simp only [Fin.snoc_castSucc]
        have := hsz j r
        rw [hzz] at this
        exact_mod_cast this
    exact mul_le_mul hη hs (abs_nonneg _) (by norm_num)
  rw [hE]
  refine ⟨?_, ?_, ?_⟩
  · -- an execution exists
    obtain ⟨f, R, hrun, hR0⟩ := hex
    have hrun' : IsWolfeRunWith p (IsLinoptChoice p) f R := hrun
    choose! js hjs using hrun'.1.2
    obtain ⟨T, s, hexec, hs1, -, -, -⟩ := exec_bwd hs hrun' hR0 hjs
    refine ⟨T, fun t ↦ Psi k (s t), (pe_tr k hs hslack T _).2 ⟨?_, fun _ ↦ ?_⟩, ?_⟩
    · simpa only [Phi_Psi] using hexec.1
    · simpa only [Phi_Psi] using hs1
    · rw [stopped_tr, Phi_Psi]; exact hexec.2
  · -- every execution
    intro T s hexec
    have hT : 1 ≤ T := by
      by_contra h0
      obtain rfl : T = 0 := by omega
      have := hexec.2
      rw [hexec.1.1, stopped_tr, Phi_init] at this
      exact init_not_stopped k this
    obtain ⟨hpe, hcond⟩ := (pe_tr k hs hslack T s).1 hexec.1
    obtain ⟨f, R, js, hrun, hR0, -, -, -, hnum⟩ :=
      exec_fwd hs ⟨hpe, (stopped_tr k _).1 hexec.2⟩ (hcond hT)
    have := (hall f R hrun hR0).1
    change LH.numAdds T (fun t ↦ Phi k (s t)) = _
    rw [hnum]; exact this
  · -- every partial execution
    intro T s hpe0
    rcases Nat.lt_or_ge T 2 with hT | hT
    · have : 0 < 2 ^ n := by positivity
      omega
    obtain ⟨hpe, hcond⟩ := (pe_tr k hs hslack T s).1 hpe0
    obtain ⟨g, R, js, hR, hR0, -, -, hcase⟩ := trace hs hb1 hpe (hcond (by omega)) T hT le_rfl
    have hg := hpart g R hR hR0
    rcases hcase with ⟨-, -, hbd⟩ | ⟨hjs, -, m, w, c, hmi, -, -, hbd⟩
    · omega
    · have hm := hb1 g R hR hR0 (js g) hjs m w hmi
      obtain ⟨S', hmaj⟩ := exists_major (hR.1 g le_rfl) hjs.1 (hs g R hR hR0 (js g) hjs)
      set R' : ℕ → Finset (Fin (2 * n + 2)) := fun l ↦ if l ≤ g then R l else S'
      have hR'le : ∀ l ≤ g, R' l = R l := fun l hl ↦ by simp [R', hl]
      have hR' : IsPartialWolfeRunWith p (IsLinoptChoice p) (g + 1) R' := by
        refine ⟨fun l hl ↦ ?_, fun l hl ↦ ?_⟩
        · rcases Nat.lt_or_ge g l with hgl | hlg
          · rw [show R' l = S' by simp [R', show ¬ l ≤ g by omega]]
            obtain ⟨-, -, -, -, hcS'⟩ := hmaj
            exact hcS'
          · rw [hR'le l hlg]; exact hR.1 l hlg
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
          · rw [hR'le l hl.le, hR'le (l + 1) hl]; exact hR.2 l hl
          · rw [hR'le l le_rfl, show R' (l + 1) = S' by simp [R']]; exact ⟨js l, hjs, hmaj⟩
      have hg1 := hpart (g + 1) R' hR' (by rw [hR'le 0 (Nat.zero_le _)]; exact hR0)
      omega

end WolfeSimplex

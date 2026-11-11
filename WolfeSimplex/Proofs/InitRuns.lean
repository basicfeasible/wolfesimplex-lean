import WolfeSimplex.Proofs.Shield
import WolfeSimplex.Proofs.RuleRuns
import WolfeSimplex.Proofs.Init
import WolfeSimplex.Proofs.KleeMinty

/-!
# Starting at the minimum-norm atom: the runs (paper: proofs of Lemma 14 (`lem:init-run`),
Lemma 17 (`lem:minnorm`), Lemma 18 (`lem:km-start`))

The first `m+1` major cycles from the slack atom insert the labels of `B₀ ∪ {ω}` one
by one (Lemma 13 (`lem:init`)(b) / Lemma 16 (`lem:weighted`)(b)); from the corral `B₀ ∪ {ω, n+2}`
on,
Theorem 1 (`thm:equivalence`)(c) for (LP⁺) with rules (`Proofs/RuleRuns.lean`) and
Lemma 12 (`lem:shield-lp`) / Lemma 16 (`lem:weighted`)(a) transfer the runs to (LP).

The rules used here (linopt, minnorm, least label) all choose an improving label
that minimizes a key `φ S j`; this is `argminRule`.
-/

namespace WolfeSimplex

open Finset Wolfe

namespace InitRuns

/-! ### Shifting and appending partial Wolfe runs -/

section Runs

variable {N D : ℕ} {p : Fin N → Fin D → ℝ} {ch : Finset (Fin N) → Fin N → Prop}

lemma shift {f a : ℕ} {S : ℕ → Finset (Fin N)} (h : IsPartialWolfeRunWith p ch f S)
    (ha : a ≤ f) : IsPartialWolfeRunWith p ch (f - a) (fun t ↦ S (a + t)) :=
  ⟨fun k hk ↦ h.1 _ (by omega), fun k hk ↦ h.2 (a + k) (by omega)⟩

lemma append_eq {a : ℕ} {S₁ S₂ : ℕ → Finset (Fin N)} (h : S₁ a = S₂ 0) {t : ℕ} (ht : a ≤ t) :
    (fun t ↦ if t ≤ a then S₁ t else S₂ (t - a)) t = S₂ (t - a) := by
  by_cases hta : t ≤ a
  · have : t = a := le_antisymm hta ht
    subst this; simp [h]
  · simp [hta]

lemma append {a b : ℕ} {S₁ S₂ : ℕ → Finset (Fin N)} (h₁ : IsPartialWolfeRunWith p ch a S₁)
    (h₂ : IsPartialWolfeRunWith p ch b S₂) (h : S₁ a = S₂ 0) :
    IsPartialWolfeRunWith p ch (a + b) (fun t ↦ if t ≤ a then S₁ t else S₂ (t - a)) := by
  refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩
  · by_cases hka : k ≤ a
    · simpa [hka] using h₁.1 k hka
    · rw [append_eq h (by omega)]; exact h₂.1 _ (by omega)
  · by_cases hka : k < a
    · have e1 : (fun t ↦ if t ≤ a then S₁ t else S₂ (t - a)) k = S₁ k := by simp [hka.le]
      have e2 : (fun t ↦ if t ≤ a then S₁ t else S₂ (t - a)) (k + 1) = S₁ (k + 1) := by
        simp [show k + 1 ≤ a by omega]
      rw [e1, e2]; exact h₁.2 k hka
    · rw [append_eq h (by omega), append_eq h (by omega), show k + 1 - a = k - a + 1 by omega]
      exact h₂.2 (k - a) (by omega)

end Runs

/-! ### The initial phase -/

section Init

variable {m n D : ℕ} (p : Fin (n + 2) → Fin D → ℝ) (B₀ : Finset (Fin n))
  {α : Type*} [LinearOrder α] (φ : Finset (Fin (n + 2)) → Fin (n + 2) → α)

/-- The rule that inserts an improving label minimizing the key `φ S j`. -/
def argminRule (S : Finset (Fin (n + 2))) (j : Fin (n + 2)) : Prop :=
  j ∈ improving p (affineMin p S) ∧ ∀ i ∈ improving p (affineMin p S), φ S j ≤ φ S i

/-- The facts about the atoms near the initial corral (Lemma 13 (`lem:init`) /
Lemma 16 (`lem:weighted`)), and the fact that the rule prefers every other label to `ω`. -/
structure Setup (m : ℕ) : Prop where
  card : B₀.card = m
  corral : ∀ S, Fin.last (n + 1) ∈ S → S ⊆ hat (hat B₀) → IsCorral p S
  imp : ∀ S, Fin.last (n + 1) ∈ S → S ⊆ hat (hat B₀) → (Fin.last n).castSucc ∉ S →
    improving p (affineMin p S) = (hat B₀).map Fin.castSuccEmb \ S
  major : ∀ S, Fin.last (n + 1) ∈ S → S ⊆ hat (hat B₀) → (Fin.last n).castSucc ∉ S →
    ∀ ℓ ∈ improving p (affineMin p S), ∀ S', MajorCycle p S ℓ S' ↔ S' = insert ℓ S
  lt : ∀ S, Fin.last (n + 1) ∈ S → S ⊆ hat (hat B₀) → (Fin.last n).castSucc ∉ S →
    ∀ ℓ ∈ (hat B₀).map Fin.castSuccEmb \ S, ℓ ≠ (Fin.last n).castSucc →
      φ S ℓ < φ S (Fin.last n).castSucc

/-- The invariant of the initial phase after `k` major cycles. -/
def Inv (m k : ℕ) (X : Finset (Fin (n + 2))) : Prop :=
  Fin.last (n + 1) ∈ X ∧ X ⊆ hat (hat B₀) ∧ X.card = k + 1 ∧
    (k ≤ m → (Fin.last n).castSucc ∉ X)

variable {p B₀ φ}

lemma omega_mem_R : (Fin.last n).castSucc ∈ (hat B₀).map Fin.castSuccEmb :=
  Finset.mem_map_of_mem _ IntLP.last_mem_hat

lemma slack_not_mem_R : Fin.last (n + 1) ∉ (hat B₀).map Fin.castSuccEmb := by
  simp [Fin.castSucc_ne_last]

lemma hat_hat_eq : hat (hat B₀) = insert (Fin.last (n + 1)) ((hat B₀).map Fin.castSuccEmb) := rfl

lemma card_R {m : ℕ} (hc : B₀.card = m) : ((hat B₀).map Fin.castSuccEmb).card = m + 1 := by
  rw [card_map, IntLP.card_hat, hc]

lemma card_hat_hat {m : ℕ} (hc : B₀.card = m) : (hat (hat B₀)).card = m + 2 := by
  rw [IntLP.card_hat, IntLP.card_hat, hc]

lemma inv_zero {m : ℕ} : Inv B₀ m 0 {Fin.last (n + 1)} := by
  refine ⟨mem_singleton_self _, ?_, by simp, fun _ ↦ ?_⟩
  · rw [singleton_subset_iff, hat_hat_eq]; exact mem_insert_self _ _
  · simp [Fin.castSucc_ne_last]

lemma inv_last {m : ℕ} (hc : B₀.card = m) {X : Finset (Fin (n + 2))} (h : Inv B₀ m (m + 1) X) :
    X = hat (hat B₀) :=
  Finset.eq_of_subset_of_card_le h.2.1 (by rw [card_hat_hat hc, h.2.2.1])

lemma omega_mem_imp {m k : ℕ} (hS : Setup p B₀ φ m) {X : Finset (Fin (n + 2))}
    (h : Inv B₀ m k X) (hk : k ≤ m) :
    (Fin.last n).castSucc ∈ improving p (affineMin p X) := by
  rw [hS.imp X h.1 h.2.1 (h.2.2.2 hk), mem_sdiff]
  exact ⟨omega_mem_R, h.2.2.2 hk⟩

/-- One major cycle of the initial phase. -/
lemma step {m k : ℕ} (hS : Setup p B₀ φ m) {X X' : Finset (Fin (n + 2))} {j : Fin (n + 2)}
    (h : Inv B₀ m k X) (hk : k ≤ m) (hj : argminRule p φ X j) (hmaj : MajorCycle p X j X') :
    j ∈ (hat B₀).map Fin.castSuccEmb ∧ j ∉ X ∧ X' = insert j X ∧ Inv B₀ m (k + 1) X' := by
  obtain ⟨hsl, hsub, hcard, hom⟩ := h
  have hω := hom hk
  have himp := hS.imp X hsl hsub hω
  have hjR : j ∈ (hat B₀).map Fin.castSuccEmb \ X := himp ▸ hmaj.2.1
  rw [mem_sdiff] at hjR
  have hX' := (hS.major X hsl hsub hω j hmaj.2.1 X').1 hmaj
  refine ⟨hjR.1, hjR.2, hX', ?_⟩
  subst hX'
  refine ⟨mem_insert_of_mem hsl, insert_subset (by rw [hat_hat_eq]; exact mem_insert_of_mem hjR.1) hsub,
    by rw [card_insert_of_notMem hjR.2, hcard], fun hk1 ↦ ?_⟩
  rw [mem_insert, not_or]
  refine ⟨fun hjω ↦ ?_, hω⟩
  subst hjω
  -- if `ω` is chosen, it is the only improving label, so `k = m`
  have hsub' : (hat B₀).map Fin.castSuccEmb ⊆ insert (Fin.last n).castSucc (X.erase (Fin.last (n + 1))) := by
    intro r hr
    by_cases hrX : r ∈ X
    · exact mem_insert_of_mem (mem_erase.2 ⟨fun h ↦ slack_not_mem_R (h ▸ hr), hrX⟩)
    · by_contra hne
      rw [mem_insert, not_or] at hne
      have hlt := hS.lt X hsl hsub hω r (mem_sdiff.2 ⟨hr, hrX⟩) hne.1
      have hrimp : r ∈ improving p (affineMin p X) := by rw [himp]; exact mem_sdiff.2 ⟨hr, hrX⟩
      exact absurd (hj.2 r hrimp) (not_le.2 hlt)
  have := card_le_card hsub'
  rw [card_R hS.card] at this
  have h2 := card_insert_le (Fin.last n).castSucc (X.erase (Fin.last (n + 1)))
  rw [card_erase_of_mem hsl, hcard] at h2
  omega

/-- The initial phase of every partial run from the slack atom. -/
lemma init_invariant {m f : ℕ} (hS : Setup p B₀ φ m) {S : ℕ → Finset (Fin (n + 2))}
    (hrun : IsPartialWolfeRunWith p (argminRule p φ) f S) (h0 : S 0 = {Fin.last (n + 1)}) :
    ∀ k ≤ min f (m + 1), Inv B₀ m k (S k) ∧
      ∀ k' < k, ∃ ℓ ∈ (hat B₀).map Fin.castSuccEmb, ℓ ∉ S k' ∧ S (k' + 1) = insert ℓ (S k') := by
  intro k
  induction k with
  | zero => intro _; rw [h0]; exact ⟨inv_zero, fun k' hk' ↦ absurd hk' (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨hinv, hsteps⟩ := ih (by omega)
    obtain ⟨j, hj, hmaj⟩ := hrun.2 k (by omega)
    obtain ⟨hjR, hjX, hX', hinv'⟩ := step hS hinv (by omega) hj hmaj
    refine ⟨hinv', fun k' hk' ↦ ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
    · exact hsteps k' hk'
    · exact ⟨j, hjR, hjX, hX'⟩

lemma m_succ_le {m f : ℕ} (hS : Setup p B₀ φ m) {S : ℕ → Finset (Fin (n + 2))}
    (hrun : IsWolfeRunWith p (argminRule p φ) f S) (h0 : S 0 = {Fin.last (n + 1)}) :
    m + 1 ≤ f := by
  by_contra hf
  have hinv := (init_invariant hS hrun.1 h0 f (by omega)).1
  have := omega_mem_imp hS hinv (by omega)
  rw [hrun.2] at this
  exact absurd this (Finset.notMem_empty _)

/-- A partial run of length `m+1` from the slack atom to `B₀ ∪ {ω, n+2}` exists. -/
lemma exists_init {m : ℕ} (hS : Setup p B₀ φ m) :
    ∃ S : ℕ → Finset (Fin (n + 2)), IsPartialWolfeRunWith p (argminRule p φ) (m + 1) S ∧
      S 0 = {Fin.last (n + 1)} ∧ S (m + 1) = hat (hat B₀) := by
  have key : ∀ k ≤ m + 1, ∃ S : ℕ → Finset (Fin (n + 2)),
      IsPartialWolfeRunWith p (argminRule p φ) k S ∧ S 0 = {Fin.last (n + 1)} ∧
        Inv B₀ m k (S k) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun _ ↦ {Fin.last (n + 1)}, ⟨fun _ _ ↦ ?_, fun k hk ↦ absurd hk (Nat.not_lt_zero _)⟩,
        rfl, inv_zero⟩
      exact hS.corral _ (mem_singleton_self _) (inv_zero (B₀ := B₀) (m := m)).2.1
    | succ k ih =>
      intro hk
      obtain ⟨S, hrun, h0, hinv⟩ := ih (by omega)
      have hne : (improving p (affineMin p (S k))).Nonempty :=
        ⟨_, omega_mem_imp hS hinv (by omega)⟩
      obtain ⟨j, hjI, hjmin⟩ := Finset.exists_min_image _ (φ (S k)) hne
      have hj : argminRule p φ (S k) j := ⟨hjI, hjmin⟩
      have hω := hinv.2.2.2 (by omega)
      have hmaj : MajorCycle p (S k) j (insert j (S k)) :=
        (hS.major (S k) hinv.1 hinv.2.1 hω j hjI _).2 rfl
      obtain ⟨-, -, -, hinv'⟩ := step hS hinv (by omega) hj hmaj
      have h1 : IsPartialWolfeRunWith p (argminRule p φ) 1
          (fun t ↦ if t = 0 then S k else insert j (S k)) := by
        refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ht with rfl | rfl
          · simpa using hrun.1 k le_rfl
          · simpa using hS.corral _ hinv'.1 hinv'.2.1
        · obtain rfl : t = 0 := by omega
          exact ⟨j, by simpa using hj, by simpa using hmaj⟩
      refine ⟨_, append hrun h1 (by simp), by simp [h0], ?_⟩
      simpa [show ¬ (k + 1 ≤ k) by omega, show k + 1 - k ≠ 0 by omega] using hinv'
  obtain ⟨S, hrun, h0, hinv⟩ := key (m + 1) le_rfl
  exact ⟨S, hrun, h0, inv_last hS.card hinv⟩

end Init

/-! ### From the corral `B₀ ∪ {ω, n+2}` on -/

section Transfer

variable {m n : ℕ} (P : IntLP m n) (Q : IntLP (m + 1) (n + 1)) (B₀ : Finset (Fin n))
  {α : Type*} [LinearOrder α] (φ : Finset (Fin (n + 2)) → Fin (n + 2) → α)
  (qch : Finset (Fin (n + 1)) → Fin (n + 1) → Prop) (pch : Finset (Fin n) → Fin n → Prop)

/-- The hypotheses of the transfer: (LP⁺)-type LP `Q` with the facts of Lemma 12 (`lem:shield-lp`)
/ Lemma 16 (`lem:weighted`)(a), and rules that correspond. -/
structure TransferHyp : Prop where
  hQ : Q.IsAdmissible
  hB₀ : P.toLP.IsFeasibleBasis B₀
  setup : Setup Q.atom B₀ φ m
  hfeas : ∀ B', Q.toLP.IsFeasibleBasis B' ↔ ∃ B, P.toLP.IsFeasibleBasis B ∧ B' = hat B
  himp : ∀ B, P.toLP.IsFeasibleBasis B →
    Q.toLP.improving (hat B) = (P.toLP.improving B).map Fin.castSuccEmb
  hleave : ∀ B, P.toLP.IsFeasibleBasis B → ∀ j ∈ P.toLP.improving B, ∀ i' : Fin (n + 1),
    Q.toLP.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔
      ∃ i, i' = Fin.castSucc i ∧ P.toLP.IsLeavingLabel B j i
  hch1 : ∀ B', Q.toLP.IsFeasibleBasis B' → ∀ j : Fin (n + 1),
    argminRule Q.atom φ (hat B') (Fin.castSucc j) ↔ qch B' j
  hch2 : ∀ B, P.toLP.IsFeasibleBasis B → ∀ j : Fin n, qch (hat B) (Fin.castSucc j) ↔ pch B j

variable {P Q B₀ φ qch pch}

lemma TransferHyp.hQB₀ (h : TransferHyp P Q B₀ φ qch pch) : Q.toLP.IsFeasibleBasis (hat B₀) :=
  (h.hfeas _).2 ⟨B₀, h.hB₀, rfl⟩

lemma forward_partial (h : TransferHyp P Q B₀ φ qch pch) {f : ℕ} {S : ℕ → Finset (Fin (n + 2))}
    (hrun : IsPartialWolfeRunWith Q.atom (argminRule Q.atom φ) f S)
    (h0 : S 0 = {Fin.last (n + 1)}) (hf : m + 1 ≤ f) :
    ∃ B, P.toLP.IsPartialSimplexRunWith pch (f - (m + 1)) B ∧ B 0 = B₀ ∧
      ∀ k ≤ f - (m + 1), S (m + 1 + k) = hat (hat (B k)) := by
  have hinv := (init_invariant h.setup hrun h0 (m + 1) (by omega)).1
  have hSm := inv_last h.setup.card hinv
  obtain ⟨B', hB'run, hB'0, hSB'⟩ := (IntLP.partialRun_hat_iff h.hQ _ qch h.hch1 (hat B₀) h.hQB₀
    (f - (m + 1)) (fun t ↦ S (m + 1 + t))).1 ⟨shift hrun hf, by simpa using hSm⟩
  obtain ⟨B, hBrun, hB0, hB'B⟩ := (LP.transfer_partialRun_iff P.toLP Q.toLP h.hfeas h.himp h.hleave
    qch pch h.hch2 B₀ h.hB₀ _ B').1 ⟨hB'run, hB'0⟩
  exact ⟨B, hBrun, hB0, fun k hk ↦ by rw [show S (m + 1 + k) = hat (B' k) from hSB' k hk, hB'B k hk]⟩

lemma forward_run (h : TransferHyp P Q B₀ φ qch pch) {f : ℕ} {S : ℕ → Finset (Fin (n + 2))}
    (hrun : IsWolfeRunWith Q.atom (argminRule Q.atom φ) f S)
    (h0 : S 0 = {Fin.last (n + 1)}) :
    m + 1 ≤ f ∧
    (∀ k < m + 1, ∃ ℓ ∈ (hat B₀).map Fin.castSuccEmb, ℓ ∉ S k ∧ S (k + 1) = insert ℓ (S k)) ∧
    ∃ B, P.toLP.IsSimplexRunWith pch (f - (m + 1)) B ∧ B 0 = B₀ ∧
      ∀ k ≤ f - (m + 1), S (m + 1 + k) = hat (hat (B k)) := by
  have hf := m_succ_le h.setup hrun h0
  have hinv := init_invariant h.setup hrun.1 h0 (m + 1) (by omega)
  have hSm := inv_last h.setup.card hinv.1
  refine ⟨hf, hinv.2, ?_⟩
  have hS' : IsWolfeRunWith Q.atom (argminRule Q.atom φ) (f - (m + 1)) (fun t ↦ S (m + 1 + t)) :=
    ⟨shift hrun.1 hf, by simpa [show m + 1 + (f - (m + 1)) = f by omega] using hrun.2⟩
  obtain ⟨B', hB'run, hB'0, hSB'⟩ := (IntLP.run_hat_iff h.hQ _ qch h.hch1 (hat B₀) h.hQB₀
    (f - (m + 1)) (fun t ↦ S (m + 1 + t))).1 ⟨hS', by simpa using hSm⟩
  obtain ⟨B, hBrun, hB0, hB'B⟩ := (LP.transfer_run_iff P.toLP Q.toLP h.hfeas h.himp h.hleave
    qch pch h.hch2 B₀ h.hB₀ _ B').1 ⟨hB'run, hB'0⟩
  exact ⟨B, hBrun, hB0, fun k hk ↦ by rw [show S (m + 1 + k) = hat (B' k) from hSB' k hk, hB'B k hk]⟩

lemma backward_run (h : TransferHyp P Q B₀ φ qch pch) {f : ℕ} {B : ℕ → Finset (Fin n)}
    (hrun : P.toLP.IsSimplexRunWith pch f B) (hB0 : B 0 = B₀) :
    ∃ S, IsWolfeRunWith Q.atom (argminRule Q.atom φ) (m + 1 + f) S ∧
      S 0 = {Fin.last (n + 1)} ∧ ∀ k ≤ f, S (m + 1 + k) = hat (hat (B k)) := by
  obtain ⟨hB'run, hB'0⟩ := (LP.transfer_run_iff P.toLP Q.toLP h.hfeas h.himp h.hleave
    qch pch h.hch2 B₀ h.hB₀ f (fun t ↦ hat (B t))).2 ⟨B, hrun, hB0, fun _ _ ↦ rfl⟩
  obtain ⟨hS2, hS20⟩ := (IntLP.run_hat_iff h.hQ (argminRule Q.atom φ) qch h.hch1 (hat B₀) h.hQB₀ f
    (fun t ↦ hat (hat (B t)))).2 ⟨fun t ↦ hat (B t), hB'run, hB'0, fun _ _ ↦ rfl⟩
  obtain ⟨S₁, hS₁, hS₁0, hS₁m⟩ := exists_init h.setup
  have heq : S₁ (m + 1) = hat (hat (B 0)) := by rw [hS₁m, ← hS20]
  refine ⟨_, ⟨append hS₁ hS2.1 heq, ?_⟩, by simp [hS₁0], fun k hk ↦ ?_⟩
  · have e := append_eq (S₂ := fun t ↦ hat (hat (B t))) heq (t := m + 1 + f) (by omega)
    simp only at e
    rw [e, show m + 1 + f - (m + 1) = f by omega]; exact hS2.2
  · have e := append_eq (S₂ := fun t ↦ hat (hat (B t))) heq (t := m + 1 + k) (by omega)
    simp only at e
    rw [e, show m + 1 + k - (m + 1) = k by omega]

end Transfer

/-! ### The shield LP (LP⁺): Lemma 14 (`lem:init-run`) -/

section Shield

variable {m n : ℕ} {P : IntLP m n} {e : Fin m → Fin n}

lemma mem_R_cases {ℓ : Fin (n + 2)} (h : ℓ ∈ (hat (basisOf e)).map Fin.castSuccEmb) :
    ℓ = (Fin.last n).castSucc ∨ ∃ i, ℓ = (e i).castSucc.castSucc := by
  simp only [hat, basisOf, Finset.mem_map, Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
    true_and, Fin.castSuccEmb_apply] at h
  obtain ⟨x, hx | ⟨k, ⟨i, rfl⟩, rfl⟩, rfl⟩ := h
  · left; rw [hx]
  · right; exact ⟨i, rfl⟩

/-- The improving labels of (LP⁺) at `B ∪ {ω}` are those of (LP) at `B`
(from the reduced costs in Lemma 12 (`lem:shield-lp`)). -/
lemma shield_improving (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B) :
    (P.shieldLP e).toLP.improving (hat B) = (P.toLP.improving B).map Fin.castSuccEmb := by
  obtain ⟨-, -, hfeas, hrc, -⟩ := IntLP.shield_lp_main P hP e hB₀
  have hQB : (P.shieldLP e).toLP.IsFeasibleBasis (hat B) := (hfeas _).2 ⟨B, hB, rfl⟩
  have hΔ : (0 : ℝ) < P.Delta0 e := by exact_mod_cast IntLP.Delta0_pos P e hB₀.1
  ext k
  induction k using Fin.lastCases with
  | last =>
    simp only [LP.improving, mem_filter, mem_univ, true_and, mem_map, Fin.castSuccEmb_apply,
      Fin.castSucc_ne_last, and_false, exists_false, iff_false, not_lt]
    rw [hQB.1.reducedCost_of_mem IntLP.last_mem_hat]
  | cast k =>
    rw [show Fin.castSucc k = Fin.castSuccEmb k from rfl, Finset.mem_map']
    simp only [LP.improving, mem_filter, mem_univ, true_and]
    rw [Fin.castSuccEmb_apply, hrc B hB.1 k]
    constructor
    · intro h; by_contra h'; have := not_lt.mp h'; nlinarith
    · intro h; exact mul_neg_of_pos_of_neg hΔ h

/-- The setup of the initial phase for the atoms of (LP⁺), for any key `φ` that prefers
every other label of `B₀ ∪ {ω}` to `ω`. -/
lemma shield_setup (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    {α : Type*} [LinearOrder α] (φ : Finset (Fin (n + 2)) → Fin (n + 2) → α)
    (hlt : ∀ S, Fin.last (n + 1) ∈ S → S ⊆ hat (hat (basisOf e)) → (Fin.last n).castSucc ∉ S →
      ∀ i, (e i).castSucc.castSucc ∉ S → φ S (e i).castSucc.castSucc < φ S (Fin.last n).castSucc) :
    Setup (P.shieldLP e).atom (basisOf e) φ m where
  card := hB₀.1.1
  corral S h1 h2 := IntLP.init_a_main P hP e hB₀ S h1 h2
  imp S h1 h2 h3 := (IntLP.init_b_main P hP e hB₀ S h1 h2 h3).1
  major S h1 h2 h3 := (IntLP.init_b_main P hP e hB₀ S h1 h2 h3).2.2
  lt S h1 h2 h3 ℓ hℓ hne := by
    rw [mem_sdiff] at hℓ
    rcases mem_R_cases hℓ.1 with h | ⟨i, rfl⟩
    · exact absurd h hne
    · exact hlt S h1 h2 h3 i hℓ.2

/-- The linopt rule prefers every label of `B₀` to `ω` in the initial phase. -/
lemma shield_linopt_lt (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (S : Finset (Fin (n + 2))) (h1 : Fin.last (n + 1) ∈ S) (h2 : S ⊆ hat (hat (basisOf e)))
    (h3 : (Fin.last n).castSucc ∉ S) (i : Fin m) (hi : (e i).castSucc.castSucc ∉ S) :
    (P.shieldLP e).atom (e i).castSucc.castSucc ⬝ᵥ affineMin (P.shieldLP e).atom S <
      (P.shieldLP e).atom (Fin.last n).castSucc ⬝ᵥ affineMin (P.shieldLP e).atom S := by
  have hQ := (IntLP.shield_lp_main P hP e hB₀).1
  have hg := (IntLP.init_b_main P hP e hB₀ S h1 h2 h3).2.1
  have hgi := hg (Fin.castSucc i) (by simpa using hi)
  have hgω := hg (Fin.last m) (by simpa using h3)
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at hgi hgω
  simp only [gap] at hgi hgω
  have hb : (P.shieldLP e).b (Fin.castSucc i) = (P.canonical e).b i := by
    simp [IntLP.shieldLP]
  have hb1 : (P.shieldLP e).b (Fin.last m) = 1 := by simp [IntLP.shieldLP]
  rw [hb] at hgi; rw [hb1] at hgω
  have h2b : (2 : ℝ) ≤ (P.canonical e).b i := by exact_mod_cast IntLP.two_le_canonical_b P e hP hB₀ i
  have hN : (0 : ℝ) < (P.shieldLP e).N := (P.shieldLP e).N_pos' (by omega)
  have hT : (0 : ℝ) < (P.shieldLP e).T := (P.shieldLP e).T_pos
  have hΔ : (0 : ℝ) < P.Delta0 e := by exact_mod_cast IntLP.Delta0_pos P e hB₀.1
  have hc : 0 < ((P.shieldLP e).N : ℝ) ^ 4 * P.Delta0 e := by positivity
  have : ((1 : ℤ) : ℝ) / (P.shieldLP e).T < ((P.canonical e).b i : ℝ) / (P.shieldLP e).T := by
    apply div_lt_div_of_pos_right _ hT; push_cast; linarith
  nlinarith

/-- The transfer hypotheses for (LP⁺) with linopt and Dantzig. -/
lemma shield_hyp_linopt (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) :
    TransferHyp P (P.shieldLP e) (basisOf e)
      (fun S j ↦ (P.shieldLP e).atom j ⬝ᵥ affineMin (P.shieldLP e).atom S)
      (P.shieldLP e).toLP.IsDantzigChoice P.toLP.IsDantzigChoice := by
  obtain ⟨hQ, -, hfeas, hrc, hleave⟩ := IntLP.shield_lp_main P hP e hB₀
  have hΔ : (0 : ℝ) < P.Delta0 e := by exact_mod_cast IntLP.Delta0_pos P e hB₀.1
  exact
  { hQ := hQ, hB₀ := hB₀
    setup := shield_setup hP hB₀ _ (shield_linopt_lt hP hB₀)
    hfeas := hfeas, himp := shield_improving hP hB₀, hleave := hleave
    hch1 := fun B' hB' j ↦ IntLP.linopt_hat_iff hQ hB' j
    hch2 := fun B hB j ↦ LP.dantzig_transfer P.toLP (P.shieldLP e).toLP _ hΔ
      (shield_improving hP hB₀) (fun B hB ↦ hrc B hB.1) B hB j }

/-- The transfer hypotheses for (LP⁺) with the least-label rule and Bland's rule. -/
lemma shield_hyp_leastLabel (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (ρ : Fin (n + 2) → ℕ) (hρ : ∀ k : Fin n, ρ k.castSucc.castSucc < ρ (Fin.last n).castSucc) :
    TransferHyp P (P.shieldLP e) (basisOf e) (fun _ j ↦ ρ j)
      ((P.shieldLP e).toLP.IsBlandChoice fun k ↦ ρ (Fin.castSucc k))
      (P.toLP.IsBlandChoice fun k ↦ ρ k.castSucc.castSucc) := by
  obtain ⟨hQ, -, hfeas, -, hleave⟩ := IntLP.shield_lp_main P hP e hB₀
  exact
  { hQ := hQ, hB₀ := hB₀
    setup := shield_setup hP hB₀ _ (fun _ _ _ _ i _ ↦ hρ (e i))
    hfeas := hfeas, himp := shield_improving hP hB₀, hleave := hleave
    hch1 := fun B' hB' j ↦ IntLP.leastLabel_hat_iff hQ hB' ρ j
    hch2 := fun B hB j ↦ LP.bland_transfer P.toLP (P.shieldLP e).toLP
      (shield_improving hP hB₀) _ B hB j }

end Shield

/-! ### The weighted shield LP (LP̃⁺): Lemma 17 (`lem:minnorm`) -/

section Weighted

variable {m n : ℕ} {P : IntLP m n} {e : Fin m → Fin n}

/-- The rank of a label of the weighted atoms in the order by norm: `σ k` for the
original label `k`, `n` for `ω`, `0` for the slack label (never used there). -/
def normRank (σ : Equiv.Perm (Fin n)) : Fin (n + 2) → ℕ :=
  Fin.snoc (α := fun _ ↦ ℕ) (IntLP.shieldRank σ) 0

lemma weighted_setup (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (σ : Equiv.Perm (Fin n)) :
    Setup (P.weightedLP e σ).atom (basisOf e) (fun _ j ↦ normSq ((P.weightedLP e σ).atom j)) m where
  card := hB₀.1.1
  corral S h1 h2 := (IntLP.weighted_b_main P hP e hB₀ σ S h1 h2).1
  imp S h1 h2 h3 := ((IntLP.weighted_b_main P hP e hB₀ σ S h1 h2).2 h3).1
  major S h1 h2 h3 := ((IntLP.weighted_b_main P hP e hB₀ σ S h1 h2).2 h3).2
  lt S h1 h2 h3 ℓ hℓ hne := by
    rw [mem_sdiff] at hℓ
    rcases mem_R_cases hℓ.1 with h | ⟨i, rfl⟩
    · exact absurd h hne
    · exact (IntLP.weighted_c_main P hP e hB₀ σ).2.2 (e i)

/-- Among the labels improving at `B ∪ {ω, n+2}`, the minnorm rule is the least-label rule
for `normRank σ`. -/
lemma minnorm_iff_leastLabel (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (σ : Equiv.Perm (Fin n)) (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B)
    (j : Fin (n + 2)) :
    argminRule (P.weightedLP e σ).atom (fun _ j ↦ normSq ((P.weightedLP e σ).atom j))
        (hat (hat B)) j ↔
      IsLeastLabelChoice (P.weightedLP e σ).atom (normRank σ) (hat (hat B)) j := by
  obtain ⟨hQ, -, hfeas, himp, -⟩ := IntLP.weighted_a_main P hP e hB₀ σ
  have hQB : (P.weightedLP e σ).toLP.IsFeasibleBasis (hat B) := (hfeas _).2 ⟨B, hB, rfl⟩
  have hI := IntLP.improving_hat (P := P.weightedLP e σ) hQB (by omega)
  rw [himp B hB, Finset.map_map] at hI
  have hmono := (IntLP.weighted_c_main P hP e hB₀ σ).2.1
  -- on improving labels, comparing norms is comparing ranks
  have key : ∀ a ∈ improving (P.weightedLP e σ).atom (affineMin (P.weightedLP e σ).atom (hat (hat B))),
      ∀ b ∈ improving (P.weightedLP e σ).atom (affineMin (P.weightedLP e σ).atom (hat (hat B))),
      (normSq ((P.weightedLP e σ).atom a) ≤ normSq ((P.weightedLP e σ).atom b) ↔
        normRank σ a ≤ normRank σ b) := by
    intro a ha b hb
    rw [hI, Finset.mem_map] at ha hb
    obtain ⟨a', -, rfl⟩ := ha
    obtain ⟨b', -, rfl⟩ := hb
    simp only [Function.Embedding.trans_apply, Fin.castSuccEmb_apply, normRank, Fin.snoc_castSucc,
      IntLP.shieldRank]
    constructor
    · intro h; by_contra h'
      have := hmono b' a' (by omega)
      linarith
    · intro h
      rcases lt_or_eq_of_le h with h | h
      · exact (hmono a' b' (by omega)).le
      · have : a' = b' := σ.injective (Fin.ext (by omega))
        rw [this]
  constructor
  · rintro ⟨hj, hmin⟩; exact ⟨hj, fun i hi ↦ (key j hj i hi).1 (hmin i hi)⟩
  · rintro ⟨hj, hmin⟩; exact ⟨hj, fun i hi ↦ (key j hj i hi).2 (hmin i hi)⟩

lemma weighted_hyp_minnorm (hP : P.IsAdmissible) (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (σ : Equiv.Perm (Fin n)) :
    TransferHyp P (P.weightedLP e σ) (basisOf e) (fun _ j ↦ normSq ((P.weightedLP e σ).atom j))
      ((P.weightedLP e σ).toLP.IsBlandChoice (IntLP.shieldRank σ))
      (P.toLP.IsBlandChoice fun k ↦ (σ k : ℕ)) := by
  obtain ⟨hQ, -, hfeas, himp, hleave⟩ := IntLP.weighted_a_main P hP e hB₀ σ
  refine
  { hQ := hQ, hB₀ := hB₀, setup := weighted_setup hP hB₀ σ
    hfeas := hfeas, himp := himp, hleave := hleave
    hch1 := fun B' hB' j ↦ ?_
    hch2 := fun B hB j ↦ ?_ }
  · obtain ⟨B, hB, rfl⟩ := (hfeas B').1 hB'
    rw [minnorm_iff_leastLabel hP hB₀ σ B hB, IntLP.leastLabel_hat_iff hQ hB' (normRank σ) j]
    simp only [normRank, Fin.snoc_castSucc]
  · rw [LP.bland_transfer P.toLP (P.weightedLP e σ).toLP himp _ B hB j]
    simp only [LP.IsBlandChoice, IntLP.shieldRank, Fin.snoc_castSucc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi ↦ by have := h2 i hi; omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i hi ↦ by have := h2 i hi; omega⟩

end Weighted

/-! ### Size bounds -/

lemma size_aux (m c W Wq : ℕ) (hc : 1 ≤ c) (hW : 2 ≤ W) (hq : Wq ≤ c * ((m + 1) * W) ^ (2 * m + 2)) :
    ((m + 1 + 1) * Wq) ^ (36 * (m + 1 + 1) ^ 2) ≤ (c * (m + 1) * W) ^ (100 * (m + 2) ^ 3) := by
  set X := (m + 1) * W with hX
  have hX2 : m + 2 ≤ X := by rw [hX]; nlinarith
  have hcX : 1 ≤ c * X := by nlinarith
  have h1 : (m + 1 + 1) * Wq ≤ (c * X) ^ (2 * m + 3) := by
    calc (m + 1 + 1) * Wq ≤ X * (c * X ^ (2 * m + 2)) := Nat.mul_le_mul hX2 hq
      _ = c * X ^ (2 * m + 3) := by ring_nf
      _ ≤ c ^ (2 * m + 3) * X ^ (2 * m + 3) :=
          Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) c)
      _ = (c * X) ^ (2 * m + 3) := by ring_nf
  rw [mul_assoc]
  calc ((m + 1 + 1) * Wq) ^ (36 * (m + 1 + 1) ^ 2)
      ≤ ((c * X) ^ (2 * m + 3)) ^ (36 * (m + 1 + 1) ^ 2) := Nat.pow_le_pow_left h1 _
    _ = (c * X) ^ ((2 * m + 3) * (36 * (m + 1 + 1) ^ 2)) := by rw [← pow_mul]
    _ ≤ (c * X) ^ (100 * (m + 2) ^ 3) := by
        apply Nat.pow_le_pow_right hcX
        have : (2 * m + 3) * 36 ≤ 100 * (m + 2) := by omega
        calc (2 * m + 3) * (36 * (m + 1 + 1) ^ 2) = ((2 * m + 3) * 36) * (m + 2) ^ 2 := by ring_nf
          _ ≤ (100 * (m + 2)) * (m + 2) ^ 2 := Nat.mul_le_mul_right _ this
          _ = 100 * (m + 2) ^ 3 := by ring_nf

lemma atom_size_of {m n : ℕ} (Q : IntLP (m + 1) (n + 1)) (c W : ℕ) (hc : 1 ≤ c) (hW : 2 ≤ W)
    (hq : Q.maxEntry ≤ c * ((m + 1) * W) ^ (2 * m + 2)) (j : Fin (n + 2)) (k : Fin (m + 2)) :
    |Q.atom j k| ≤ ((c * (m + 1) * W : ℕ) : ℝ) ^ (100 * (m + 2) ^ 3) := by
  refine (Q.atom_size (by omega) j k).trans ?_
  exact_mod_cast size_aux m c W _ hc hW hq

/-! ### Lemma 14 (`lem:init-run`) and Lemma 17 (`lem:minnorm`) -/

section Main

variable {m n : ℕ}

theorem init_linopt_main (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) :
    (∀ j k, ∃ z : ℤ, (P.shieldLP e).atom j k = z) ∧
    (∀ j k, |(P.shieldLP e).atom j k| ≤
      (((m + 1) * P.maxEntry : ℕ) : ℝ) ^ (100 * (m + 2) ^ 3)) ∧
    (∀ j ≠ Fin.last (n + 1),
      normSq ((P.shieldLP e).atom (Fin.last (n + 1))) < normSq ((P.shieldLP e).atom j)) ∧
    (∀ f S, IsWolfeRunWith (P.shieldLP e).atom (IsLinoptChoice (P.shieldLP e).atom) f S →
      S 0 = {Fin.last (n + 1)} →
      m + 1 ≤ f ∧
      (∀ k < m + 1, ∃ ℓ ∈ (hat (basisOf e)).map Fin.castSuccEmb,
        ℓ ∉ S k ∧ S (k + 1) = insert ℓ (S k)) ∧
      ∃ B, P.toLP.IsSimplexRunWith P.toLP.IsDantzigChoice (f - (m + 1)) B ∧
        B 0 = basisOf e ∧ ∀ k ≤ f - (m + 1), S (m + 1 + k) = hat (hat (B k))) ∧
    (∀ f B, P.toLP.IsSimplexRunWith P.toLP.IsDantzigChoice f B → B 0 = basisOf e →
      ∃ S, IsWolfeRunWith (P.shieldLP e).atom (IsLinoptChoice (P.shieldLP e).atom)
          (m + 1 + f) S ∧
        S 0 = {Fin.last (n + 1)} ∧ ∀ k ≤ f, S (m + 1 + k) = hat (hat (B k))) := by
  have h := shield_hyp_linopt hP hB₀
  have hsize := (IntLP.shield_lp_main P hP e hB₀).2.1
  refine ⟨(P.shieldLP e).atom_integral, fun j k ↦ ?_, IntLP.init_c_main P hP e hB₀,
    fun f S hrun h0 ↦ forward_run h hrun h0, fun f B hrun hB0 ↦ backward_run h hrun hB0⟩
  have := atom_size_of (P.shieldLP e) 1 P.maxEntry le_rfl P.two_le_maxEntry
    (by rw [one_mul]; exact hsize) j k
  simpa using this

theorem init_leastLabel_main (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e))
    (ρ : Fin (n + 2) → ℕ) (hρ : ∀ k : Fin n, ρ k.castSucc.castSucc < ρ (Fin.last n).castSucc) :
    (∀ f S, IsWolfeRunWith (P.shieldLP e).atom
        (IsLeastLabelChoice (P.shieldLP e).atom ρ) f S →
      S 0 = {Fin.last (n + 1)} →
      m + 1 ≤ f ∧
      (∀ k < m + 1, ∃ ℓ ∈ (hat (basisOf e)).map Fin.castSuccEmb,
        ℓ ∉ S k ∧ S (k + 1) = insert ℓ (S k)) ∧
      ∃ B, P.toLP.IsSimplexRunWith (P.toLP.IsBlandChoice fun k ↦ ρ k.castSucc.castSucc)
          (f - (m + 1)) B ∧
        B 0 = basisOf e ∧ ∀ k ≤ f - (m + 1), S (m + 1 + k) = hat (hat (B k))) ∧
    (∀ f B, P.toLP.IsSimplexRunWith (P.toLP.IsBlandChoice fun k ↦ ρ k.castSucc.castSucc) f B →
      B 0 = basisOf e →
      ∃ S, IsWolfeRunWith (P.shieldLP e).atom (IsLeastLabelChoice (P.shieldLP e).atom ρ)
          (m + 1 + f) S ∧
        S 0 = {Fin.last (n + 1)} ∧ ∀ k ≤ f, S (m + 1 + k) = hat (hat (B k))) := by
  have h := shield_hyp_leastLabel hP hB₀ ρ hρ
  exact ⟨fun f S hrun h0 ↦ forward_run h hrun h0, fun f B hrun hB0 ↦ backward_run h hrun hB0⟩

theorem minnorm_main (P : IntLP m n) (hP : P.IsAdmissible) (e : Fin m → Fin n)
    (hB₀ : P.toLP.IsFeasibleBasis (basisOf e)) (σ : Equiv.Perm (Fin n)) :
    (∀ j k, ∃ z : ℤ, (P.weightedLP e σ).atom j k = z) ∧
    (∀ j k, |(P.weightedLP e σ).atom j k| ≤
      (((n + 1) * (m + 1) * P.maxEntry : ℕ) : ℝ) ^ (100 * (m + 2) ^ 3)) ∧
    (∀ j k, j ≠ k → normSq ((P.weightedLP e σ).atom j) ≠ normSq ((P.weightedLP e σ).atom k)) ∧
    (∀ j ≠ Fin.last (n + 1),
      normSq ((P.weightedLP e σ).atom (Fin.last (n + 1))) < normSq ((P.weightedLP e σ).atom j)) ∧
    (∀ f S, IsWolfeRunWith (P.weightedLP e σ).atom (IsMinnormChoice (P.weightedLP e σ).atom) f S →
      S 0 = {Fin.last (n + 1)} →
      m + 1 ≤ f ∧
      (∀ k < m + 1, ∃ ℓ ∈ (hat (basisOf e)).map Fin.castSuccEmb,
        ℓ ∉ S k ∧ S (k + 1) = insert ℓ (S k)) ∧
      ∃ B, P.toLP.IsSimplexRunWith (P.toLP.IsBlandChoice fun k ↦ (σ k : ℕ)) (f - (m + 1)) B ∧
        B 0 = basisOf e ∧ ∀ k ≤ f - (m + 1), S (m + 1 + k) = hat (hat (B k))) ∧
    (∀ f B, P.toLP.IsSimplexRunWith (P.toLP.IsBlandChoice fun k ↦ (σ k : ℕ)) f B →
      B 0 = basisOf e →
      ∃ S, IsWolfeRunWith (P.weightedLP e σ).atom (IsMinnormChoice (P.weightedLP e σ).atom)
          (m + 1 + f) S ∧
        S 0 = {Fin.last (n + 1)} ∧ ∀ k ≤ f, S (m + 1 + k) = hat (hat (B k))) := by
  have h := weighted_hyp_minnorm hP hB₀ σ
  have hsize := (IntLP.weighted_a_main P hP e hB₀ σ).2.1
  obtain ⟨hc1, hc2, hc3⟩ := IntLP.weighted_c_main P hP e hB₀ σ
  set p := (P.weightedLP e σ).atom
  have hn : 0 < n := by
    have h1 := hB₀.1.1
    have h2 := Finset.card_le_univ (basisOf e)
    simp only [Fintype.card_fin] at h2
    have := hP.1; omega
  have hr_slack : normRank σ (Fin.last (n + 1)) = 0 := by simp [normRank]
  have hr_omega : normRank σ (Fin.last n).castSucc = n + 1 := by
    simp [normRank, IntLP.shieldRank]
  have hr_orig : ∀ k : Fin n, normRank σ k.castSucc.castSucc = σ k + 1 := by
    intro k; simp [normRank, IntLP.shieldRank]
  have hlt : ∀ a b, normRank σ a < normRank σ b → normSq (p a) < normSq (p b) := by
    intro a b hab
    induction b using Fin.lastCases with
    | last => rw [hr_slack] at hab; omega
    | cast b =>
      induction b using Fin.lastCases with
      | last =>
        induction a using Fin.lastCases with
        | last => exact (hc1 ⟨0, hn⟩).trans (hc3 _)
        | cast a =>
          induction a using Fin.lastCases with
          | last => rw [hr_omega] at hab; omega
          | cast a => exact hc3 a
      | cast b =>
        induction a using Fin.lastCases with
        | last => exact hc1 b
        | cast a =>
          induction a using Fin.lastCases with
          | last => rw [hr_omega, hr_orig] at hab; have := (σ b).isLt; omega
          | cast a => rw [hr_orig, hr_orig] at hab; exact hc2 a b (by omega)
  have hinj : ∀ a b, normRank σ a = normRank σ b → a = b := by
    intro a b hab
    induction b using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => rfl
      | cast a =>
        induction a using Fin.lastCases with
        | last => rw [hr_omega, hr_slack] at hab; omega
        | cast a => rw [hr_orig, hr_slack] at hab; omega
    | cast b =>
      induction b using Fin.lastCases with
      | last =>
        induction a using Fin.lastCases with
        | last => rw [hr_omega, hr_slack] at hab; omega
        | cast a =>
          induction a using Fin.lastCases with
          | last => rfl
          | cast a => rw [hr_orig, hr_omega] at hab; have := (σ a).isLt; omega
      | cast b =>
        induction a using Fin.lastCases with
        | last => rw [hr_orig, hr_slack] at hab; omega
        | cast a =>
          induction a using Fin.lastCases with
          | last => rw [hr_orig, hr_omega] at hab; have := (σ b).isLt; omega
          | cast a =>
            rw [hr_orig, hr_orig] at hab
            have : a = b := σ.injective (Fin.ext (by omega))
            rw [this]
  have hsz : ∀ j k, |p j k| ≤ (((n + 1) * (m + 1) * P.maxEntry : ℕ) : ℝ) ^ (100 * (m + 2) ^ 3) :=
    atom_size_of (P.weightedLP e σ) (n + 1) P.maxEntry (by omega) P.two_le_maxEntry hsize
  refine ⟨(P.weightedLP e σ).atom_integral, hsz, fun a b hab ↦ ?_, fun j hj ↦ ?_,
    fun f S hrun h0 ↦ forward_run h hrun h0, fun f B hrun hB0 ↦ backward_run h hrun hB0⟩
  · have hne : normRank σ a ≠ normRank σ b := fun h ↦ hab (hinj a b h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hlt a b h).ne
    · exact (hlt b a h).ne'
  · apply hlt
    rw [hr_slack]
    rcases Nat.eq_zero_or_pos (normRank σ j) with h | h
    · exact absurd (hinj _ _ (h.trans hr_slack.symm)) hj
    · exact h

end Main

/-! ### Lemma 18 (`lem:km-start`) -/

section KM

lemma pow_ten_le (n a : ℕ) (ha : a < n) : 2 * 10 ^ a ≤ 100 ^ n := by
  calc 2 * 10 ^ a ≤ 10 * 10 ^ a := by omega
    _ = 10 ^ (a + 1) := by ring
    _ ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) ha
    _ ≤ 100 ^ n := Nat.pow_le_pow_left (by norm_num) n

lemma km_maxEntry (n : ℕ) (hn : 1 ≤ n) : (kleeMinty n).maxEntry ≤ 100 ^ n := by
  have h2 : 2 ≤ 100 ^ n := by
    calc 2 ≤ 100 := by norm_num
      _ ≤ 100 ^ n := Nat.le_self_pow (by omega) 100
  unfold IntLP.maxEntry
  refine max_le h2 (max_le (max_le (Finset.sup_le fun ij _ ↦ ?_) (Finset.sup_le fun i _ ↦ ?_))
    (Finset.sup_le fun k _ ↦ ?_))
  · obtain ⟨i, k⟩ := ij
    simp only [kleeMinty, Matrix.of_apply]
    have hi := i.isLt
    split_ifs <;> simp only [Int.natAbs_one, Int.natAbs_zero, Int.natAbs_mul, Int.natAbs_pow] <;>
      norm_num <;> first | omega | exact pow_ten_le n _ (by omega)
  · simp only [kleeMinty, Int.natAbs_pow]
    norm_num
    exact Nat.pow_le_pow_right (by norm_num) i.isLt.le
  · simp only [kleeMinty]
    split_ifs
    · simp only [Int.natAbs_neg, Int.natAbs_pow]
      norm_num
      calc 10 ^ (n - 1 - k.val / 2) ≤ 2 * 10 ^ (n - 1 - k.val / 2) := by omega
        _ ≤ 100 ^ n := pow_ten_le n _ (by omega)
    · simp

lemma two_mul_add_one_le_four_pow (n : ℕ) (hn : 1 ≤ n) : 2 * n + 1 ≤ 4 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have := ih hk; rw [pow_succ]; omega

variable {n : ℕ}

/-- The common part of the two statements of Lemma 18 (`lem:km-start`). -/
lemma km_runs (hn : 1 ≤ n) {Q : IntLP (n + 1) (2 * n + 1)} {α : Type*} [LinearOrder α]
    {φ : Finset (Fin (2 * n + 2)) → Fin (2 * n + 2) → α}
    {qch : Finset (Fin (2 * n + 1)) → Fin (2 * n + 1) → Prop}
    {pch : Finset (Fin (2 * n)) → Fin (2 * n) → Prop}
    (h : TransferHyp (kleeMinty n) Q (basisOf (kmSlack n)) φ qch pch)
    (hex : ∃ f B, (kleeMinty n).toLP.IsSimplexRunWith pch f B ∧ B 0 = basisOf (kmSlack n))
    (hall : ∀ f B, (kleeMinty n).toLP.IsSimplexRunWith pch f B →
      B 0 = basisOf (kmSlack n) → f = 2 ^ n - 1)
    (hpart : ∀ f B, (kleeMinty n).toLP.IsPartialSimplexRunWith pch f B →
      B 0 = basisOf (kmSlack n) → f ≤ 2 ^ n - 1) :
    (∃ f S, IsWolfeRunWith Q.atom (argminRule Q.atom φ) f S ∧ S 0 = {Fin.last (2 * n + 1)}) ∧
    (∀ f S, IsWolfeRunWith Q.atom (argminRule Q.atom φ) f S → S 0 = {Fin.last (2 * n + 1)} →
      f + 1 = 2 ^ n + n + 1 ∧ Set.InjOn S (Set.Iic f)) ∧
    (∀ f S, IsPartialWolfeRunWith Q.atom (argminRule Q.atom φ) f S →
      S 0 = {Fin.last (2 * n + 1)} → f ≤ 2 ^ n + n) := by
  have hpow := Nat.one_le_two_pow (n := n)
  have hP := (KM.admissible n hn).1
  refine ⟨?_, fun f S hrun h0 ↦ ?_, fun f S hrun h0 ↦ ?_⟩
  · obtain ⟨f, B, hrun, hB0⟩ := hex
    obtain ⟨S, hS, hS0, -⟩ := backward_run h hrun hB0
    exact ⟨_, S, hS, hS0⟩
  · obtain ⟨hf, -, B, hBrun, hB0, hSB⟩ := forward_run h hrun h0
    have hlen := hall _ B hBrun hB0
    refine ⟨by omega, ?_⟩
    have hcard1 : ∀ t ≤ n + 1, (S t).card = t + 1 := fun t ht ↦
      (init_invariant h.setup hrun.1 h0 t (by omega)).1.2.2.1
    have hcard2 : ∀ t, n + 1 ≤ t → t ≤ f → S t = hat (hat (B (t - (n + 1)))) := by
      intro t ht1 ht2
      have := hSB (t - (n + 1)) (by omega)
      rwa [show n + 1 + (t - (n + 1)) = t by omega] at this
    have hcardB : ∀ k ≤ f - (n + 1), (hat (hat (B k))).card = n + 2 := by
      intro k hk
      rw [IntLP.card_hat, IntLP.card_hat, (hBrun.1.1 k hk).1.1]
    have hinjB := LP.partialRun_injOn _ hP.2.2.2 pch _ B hBrun.1
    intro a ha b hb hab
    simp only [Set.mem_Iic] at ha hb
    by_cases ha1 : a ≤ n
    · by_cases hb1 : b ≤ n
      · have := hcard1 a (by omega); rw [hab, hcard1 b (by omega)] at this; omega
      · have := hcard1 a (by omega)
        rw [hab, hcard2 b (by omega) hb, hcardB _ (by omega)] at this; omega
    · by_cases hb1 : b ≤ n
      · have := hcard1 b (by omega)
        rw [← hab, hcard2 a (by omega) ha, hcardB _ (by omega)] at this; omega
      · rw [hcard2 a (by omega) ha, hcard2 b (by omega) hb] at hab
        have := hinjB (by simp only [Set.mem_Iic]; omega) (by simp only [Set.mem_Iic]; omega)
          (hat_injective (hat_injective hab))
        omega
  · by_cases hf : n + 1 ≤ f
    · obtain ⟨B, hBrun, hB0, -⟩ := forward_partial h hrun h0 hf
      have := hpart _ B hBrun hB0
      omega
    · omega

theorem km_linopt_main (hn : 1 ≤ n) :
    ∃ p : Fin (2 * n + 2) → Fin (n + 2) → ℝ,
      (∀ j k, ∃ z : ℤ, p j k = z) ∧ (∀ j k, |p j k| ≤ (10 : ℝ) ^ (600 * (n + 2) ^ 4)) ∧
      ∃ k₀, (∀ j ≠ k₀, normSq (p k₀) < normSq (p j)) ∧
        (∃ f S, IsWolfeRunWith p (IsLinoptChoice p) f S ∧ S 0 = {k₀}) ∧
        (∀ f S, IsWolfeRunWith p (IsLinoptChoice p) f S → S 0 = {k₀} →
          f + 1 = 2 ^ n + n + 1 ∧ Set.InjOn S (Set.Iic f)) ∧
        (∀ f S, IsPartialWolfeRunWith p (IsLinoptChoice p) f S → S 0 = {k₀} → f ≤ 2 ^ n + n) := by
  obtain ⟨hP, hB₀⟩ := KM.admissible n hn
  obtain ⟨hint, hsz, hmin, -, -⟩ := init_linopt_main (kleeMinty n) hP (kmSlack n) hB₀
  have h := shield_hyp_linopt hP hB₀
  obtain ⟨hd1, hd2, hd3, -⟩ := KM.dantzig n hn
  refine ⟨_, hint, fun j k ↦ (hsz j k).trans ?_, _, hmin, km_runs hn h hd1 hd2 hd3⟩
  have hW := km_maxEntry n hn
  have h1 : (n + 1) * (kleeMinty n).maxEntry ≤ 10 ^ (4 * n) := by
    have : n + 1 ≤ 100 ^ n := by
      have := Nat.lt_pow_self (show 1 < 100 by norm_num) (n := n); omega
    calc (n + 1) * (kleeMinty n).maxEntry ≤ 100 ^ n * 100 ^ n := Nat.mul_le_mul this hW
      _ = 10 ^ (4 * n) := by rw [← mul_pow, pow_mul]; norm_num
  have h2 : ((n + 1) * (kleeMinty n).maxEntry) ^ (100 * (n + 2) ^ 3) ≤ 10 ^ (600 * (n + 2) ^ 4) := by
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

theorem km_minnorm_main (hn : 1 ≤ n) :
    ∃ p : Fin (2 * n + 2) → Fin (n + 2) → ℝ,
      (∀ j k, ∃ z : ℤ, p j k = z) ∧ (∀ j k, |p j k| ≤ (10 : ℝ) ^ (600 * (n + 2) ^ 4)) ∧
      (∀ j k, j ≠ k → normSq (p j) ≠ normSq (p k)) ∧
      ∃ k₀, (∀ j ≠ k₀, normSq (p k₀) < normSq (p j)) ∧
        (∃ f S, IsWolfeRunWith p (IsMinnormChoice p) f S ∧ S 0 = {k₀}) ∧
        (∀ f S, IsWolfeRunWith p (IsMinnormChoice p) f S → S 0 = {k₀} →
          f + 1 = 2 ^ n + n + 1 ∧ Set.InjOn S (Set.Iic f)) ∧
        (∀ f S, IsPartialWolfeRunWith p (IsMinnormChoice p) f S → S 0 = {k₀} → f ≤ 2 ^ n + n) := by
  obtain ⟨hP, hB₀⟩ := KM.admissible n hn
  obtain ⟨hint, hsz, hdist, hmin, -, -⟩ :=
    minnorm_main (kleeMinty n) hP (kmSlack n) hB₀ (Equiv.refl _)
  have h := weighted_hyp_minnorm hP hB₀ (Equiv.refl _)
  obtain ⟨hb1, hb2, hb3⟩ := KM.bland n hn
  refine ⟨_, hint, fun j k ↦ (hsz j k).trans ?_, hdist, _, hmin, km_runs hn h hb1 hb2 hb3⟩
  have hW := km_maxEntry n hn
  have hl : ∀ x, x ≤ 2 * n + 1 → x ≤ 100 ^ n := by
    intro x hx
    have : 2 * n + 1 ≤ 100 ^ n := by
      have h4 := Nat.lt_pow_self (show 1 < 4 by norm_num) (n := n)
      have h5 : 4 ^ n ≤ 100 ^ n := Nat.pow_le_pow_left (by norm_num) n
      have h6 := two_mul_add_one_le_four_pow n hn
      omega
    omega
  have h1 : (2 * n + 1) * (n + 1) * (kleeMinty n).maxEntry ≤ 10 ^ (6 * n) := by
    calc (2 * n + 1) * (n + 1) * (kleeMinty n).maxEntry ≤ 100 ^ n * 100 ^ n * 100 ^ n :=
          Nat.mul_le_mul (Nat.mul_le_mul (hl _ le_rfl) (hl _ (by omega))) hW
      _ = 10 ^ (6 * n) := by rw [← mul_pow, ← mul_pow, pow_mul]; norm_num
  have h2 : ((2 * n + 1) * (n + 1) * (kleeMinty n).maxEntry) ^ (100 * (n + 2) ^ 3) ≤
      10 ^ (600 * (n + 2) ^ 4) := by
    calc ((2 * n + 1) * (n + 1) * (kleeMinty n).maxEntry) ^ (100 * (n + 2) ^ 3)
        ≤ (10 ^ (6 * n)) ^ (100 * (n + 2) ^ 3) := Nat.pow_le_pow_left h1 _
      _ = 10 ^ (6 * n * (100 * (n + 2) ^ 3)) := by rw [← pow_mul]
      _ ≤ 10 ^ (600 * (n + 2) ^ 4) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have : 6 * n ≤ 6 * (n + 2) := by omega
        calc 6 * n * (100 * (n + 2) ^ 3) ≤ 6 * (n + 2) * (100 * (n + 2) ^ 3) :=
              Nat.mul_le_mul_right _ this
          _ = 600 * (n + 2) ^ 4 := by ring
  exact_mod_cast h2

end KM

end InitRuns

end WolfeSimplex

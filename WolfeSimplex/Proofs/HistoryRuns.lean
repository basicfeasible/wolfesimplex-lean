import WolfeSimplex.Defs.HistoryRules
import WolfeSimplex.Proofs.RuleRuns

/-!
# Corollary 2 (`cor:intro-rules`): deterministic rules (Dantzig, Bland, Zadeh, Cunningham)

Wolfe runs from `B̂₀` with the insertion rules linopt, least label, least inserted and round
robin are exactly the hats of the simplex runs from `B₀` with the pivot rules of Dantzig,
Bland, Zadeh and Cunningham (with the same ties allowed).
-/

namespace WolfeSimplex

open Finset Wolfe

variable {m n : ℕ}

/-! ### Cyclic distances under `Fin.castSucc` -/

lemma cyclicDist_eq {n : ℕ} (a b : Fin n) :
    cyclicDist a b = if (a : ℕ) ≤ b then (b : ℕ) - a else (b : ℕ) + n - a := by
  unfold cyclicDist
  have ha := a.isLt
  have hb := b.isLt
  split_ifs with h
  · rw [show (b : ℕ) + n - a = ((b : ℕ) - a) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The cyclic order seen from `a` is the same in `Fin n` and (via `castSucc`) in `Fin (n+1)`. -/
lemma cyclicDist_castSucc_le_iff {n : ℕ} (a b b' : Fin n) :
    cyclicDist a.castSucc b.castSucc ≤ cyclicDist a.castSucc b'.castSucc ↔
      cyclicDist a b ≤ cyclicDist a b' := by
  rw [cyclicDist_eq, cyclicDist_eq, cyclicDist_eq, cyclicDist_eq]
  simp only [Fin.val_castSucc]
  have := b.isLt; have := b'.isLt; have := a.isLt
  split_ifs <;> omega

lemma getLastD_map_castSucc {n : ℕ} (l : List (Fin n)) (j₀ : Fin n) :
    (l.map Fin.castSucc).getLastD j₀.castSucc = (l.getLastD j₀).castSucc := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a _ => simp

lemma range_map_castSucc {n : ℕ} {J' : ℕ → Fin (n + 1)} {J : ℕ → Fin n} {k : ℕ}
    (h : ∀ ℓ < k, J' ℓ = (J ℓ).castSucc) :
    (List.range k).map J' = ((List.range k).map J).map Fin.castSucc := by
  rw [List.map_map]
  exact List.map_congr_left fun ℓ hℓ ↦ h ℓ (List.mem_range.1 hℓ)

namespace IntLP

variable {P : IntLP m n}

/-- Wolfe runs with a history-dependent insertion rule from `B̂₀` are the hats of the simplex
runs with a corresponding history-dependent pivot rule from `B₀`. -/
theorem partialRunHist_hat_iff (hP : P.IsAdmissible)
    (wch : List (Fin (n + 1)) → Finset (Fin (n + 1)) → Fin (n + 1) → Prop)
    (sch : List (Fin n) → Finset (Fin n) → Fin n → Prop)
    (hch : ∀ hist B, P.toLP.IsFeasibleBasis B → ∀ j : Fin n,
      wch (hist.map Fin.castSucc) (hat B) (Fin.castSucc j) ↔ sch hist B j)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (f : ℕ)
    (S : ℕ → Finset (Fin (n + 1))) (J' : ℕ → Fin (n + 1)) :
    (IsPartialWolfeRunWithHist P.atom wch f S J' ∧ S 0 = hat B₀) ↔
      ∃ B J, P.toLP.IsPartialSimplexRunWithHist sch f B J ∧ B 0 = B₀ ∧
        (∀ k ≤ f, S k = hat (B k)) ∧ ∀ k < f, J' k = Fin.castSucc (J k) := by
  constructor
  · rintro ⟨⟨-, hmaj⟩, hS0⟩
    -- an element of `Fin n` (a feasible basis has `m ≥ 1` elements)
    have hne : B₀.Nonempty := by
      rw [← Finset.card_pos, hB₀.1.1]; exact hP.1
    obtain ⟨j₀, -⟩ := hne
    set B : ℕ → Finset (Fin n) := fun k ↦ unhat (S k)
    set J : ℕ → Fin n := fun k ↦ if h : J' k = Fin.last n then j₀ else (J' k).castPred h
    have key : ∀ k ≤ f, P.toLP.IsFeasibleBasis (B k) ∧ S k = hat (B k) := by
      intro k
      induction k with
      | zero => intro _; simp only [B, hS0, unhat_hat]; exact ⟨hB₀, trivial⟩
      | succ k ih =>
        intro hk
        obtain ⟨hBk, hSk⟩ := ih (by omega)
        obtain ⟨-, hj⟩ := hmaj k (by omega)
        rw [hSk] at hj
        obtain ⟨j', i, -, hj', hi, hS'⟩ := majorCycle_hat_spec hP hBk hj
        simp only [B, hS', unhat_hat]
        exact ⟨(LP.pivot_spec hBk hj' hi).1, trivial⟩
    have hJ : ∀ k < f, ∃ i, J' k = Fin.castSucc (J k) ∧ J k ∈ P.toLP.improving (B k) ∧
        P.toLP.IsLeavingLabel (B k) (J k) i ∧ S (k + 1) = hat (insert (J k) ((B k).erase i)) := by
      intro k hk
      obtain ⟨hBk, hSk⟩ := key k hk.le
      obtain ⟨-, hj⟩ := hmaj k hk
      rw [hSk] at hj
      obtain ⟨j', i, hjj, hj', hi, hS'⟩ := majorCycle_hat_spec hP hBk hj
      have hJk : J k = j' := by
        simp only [J, hjj, Fin.castSucc_ne_last, dite_false, Fin.castPred_castSucc]
      rw [hJk]
      exact ⟨i, hjj, hj', hi, hS'⟩
    have hJ' : ∀ k < f, J' k = Fin.castSucc (J k) := fun k hk ↦ (hJ k hk).choose_spec.1
    refine ⟨B, J, ⟨fun k hk ↦ (key k hk).1, fun k hk ↦ ?_⟩, by simp [B, hS0, unhat_hat],
      fun k hk ↦ (key k hk).2, hJ'⟩
    obtain ⟨hBk, hSk⟩ := key k hk.le
    obtain ⟨i, hjj, hj, hi, hS'⟩ := hJ k hk
    refine ⟨?_, hBk, hj, hBk.1.not_mem_of_mem_improving hj, i, hi, ?_⟩
    · have hw := (hmaj k hk).1
      rw [range_map_castSucc fun ℓ hℓ ↦ hJ' ℓ (by omega), hSk, hjj] at hw
      exact (hch _ _ hBk _).1 hw
    · simp only [B, hS', unhat_hat]
  · rintro ⟨B, J, ⟨hfeas, hpiv⟩, hB0, hS, hJ'⟩
    refine ⟨⟨fun k hk ↦ ?_, fun k hk ↦ ⟨?_, ?_⟩⟩, by rw [hS 0 (Nat.zero_le _), hB0]⟩
    · rw [hS k hk]; exact (thm_a hP (hfeas k hk)).1
    · rw [range_map_castSucc fun ℓ hℓ ↦ hJ' ℓ (by omega), hS k hk.le, hJ' k hk]
      exact (hch _ _ (hfeas k hk.le) _).2 (hpiv k hk).1
    · obtain ⟨-, hj, -, i, hi, hBeq⟩ := (hpiv k hk).2
      rw [hS k hk.le, hS (k + 1) hk, hBeq, hJ' k hk]
      exact ((thm_b hP (hfeas k hk.le) hj hi).2.2.2.2 _).2 rfl

theorem runHist_hat_iff (hP : P.IsAdmissible)
    (wch : List (Fin (n + 1)) → Finset (Fin (n + 1)) → Fin (n + 1) → Prop)
    (sch : List (Fin n) → Finset (Fin n) → Fin n → Prop)
    (hch : ∀ hist B, P.toLP.IsFeasibleBasis B → ∀ j : Fin n,
      wch (hist.map Fin.castSucc) (hat B) (Fin.castSucc j) ↔ sch hist B j)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (f : ℕ)
    (S : ℕ → Finset (Fin (n + 1))) (J' : ℕ → Fin (n + 1)) :
    (IsWolfeRunWithHist P.atom wch f S J' ∧ S 0 = hat B₀) ↔
      ∃ B J, P.toLP.IsSimplexRunWithHist sch f B J ∧ B 0 = B₀ ∧
        (∀ k ≤ f, S k = hat (B k)) ∧ ∀ k < f, J' k = Fin.castSucc (J k) := by
  constructor
  · rintro ⟨⟨hrun, hlast⟩, hS0⟩
    obtain ⟨B, J, hBrun, hB0, hSB, hJ⟩ :=
      (partialRunHist_hat_iff hP wch sch hch B₀ hB₀ f S J').1 ⟨hrun, hS0⟩
    refine ⟨B, J, ⟨hBrun, ?_⟩, hB0, hSB, hJ⟩
    rw [hSB f le_rfl, improving_hat (hBrun.1 f le_rfl) hP.1, Finset.map_eq_empty] at hlast
    exact hlast
  · rintro ⟨B, J, ⟨hBrun, hlast⟩, hB0, hSB, hJ⟩
    obtain ⟨hrun, hS0⟩ :=
      (partialRunHist_hat_iff hP wch sch hch B₀ hB₀ f S J').2 ⟨B, J, hBrun, hB0, hSB, hJ⟩
    refine ⟨⟨hrun, ?_⟩, hS0⟩
    rw [hSB f le_rfl, improving_hat (hBrun.1 f le_rfl) hP.1, hlast, Finset.map_empty]

/-- The least-inserted rule at `B̂` is Zadeh's rule at `B`. -/
lemma leastInserted_hat_iff (hP : P.IsAdmissible) (hist : List (Fin n)) {B : Finset (Fin n)}
    (hB : P.toLP.IsFeasibleBasis B) (j : Fin n) :
    IsLeastInsertedChoice P.atom (hist.map Fin.castSucc) (hat B) (Fin.castSucc j) ↔
      P.toLP.IsZadehChoice hist B j := by
  unfold IsLeastInsertedChoice LP.IsZadehChoice
  rw [improving_hat hB hP.1, show Fin.castSucc j = Fin.castSuccEmb j from rfl, Finset.mem_map',
    Finset.forall_mem_map]
  simp only [Fin.coe_castSuccEmb, List.count_map_of_injective _ _ (Fin.castSucc_injective n)]

/-- The round-robin rule at `B̂` (initial label `j₀`) is Cunningham's rule at `B`. -/
lemma roundRobin_hat_iff (hP : P.IsAdmissible) (j₀ : Fin n) (hist : List (Fin n))
    {B : Finset (Fin n)} (hB : P.toLP.IsFeasibleBasis B) (j : Fin n) :
    IsRoundRobinChoice P.atom (Fin.castSucc j₀) (hist.map Fin.castSucc) (hat B) (Fin.castSucc j) ↔
      P.toLP.IsCunninghamChoice j₀ hist B j := by
  unfold IsRoundRobinChoice LP.IsCunninghamChoice
  rw [improving_hat hB hP.1, show Fin.castSucc j = Fin.castSuccEmb j from rfl, Finset.mem_map',
    Finset.forall_mem_map]
  simp only [Fin.coe_castSuccEmb, getLastD_map_castSucc, cyclicDist_castSucc_le_iff]


/-- The round-robin rule at `B̂` with the slack as initial label is Cunningham's rule at `B`
with the initial label `0`: both start with the natural order `0, 1, …, n-1`. -/
lemma roundRobin_last_hat_iff (hP : P.IsAdmissible) (j₀ : Fin n) (hj₀ : (j₀ : ℕ) = 0)
    (hist : List (Fin n)) {B : Finset (Fin n)} (hB : P.toLP.IsFeasibleBasis B) (j : Fin n) :
    IsRoundRobinChoice P.atom (Fin.last n) (hist.map Fin.castSucc) (hat B) (Fin.castSucc j) ↔
      P.toLP.IsCunninghamChoice j₀ hist B j := by
  have key : ∀ b b' : Fin n,
      cyclicDist ((hist.map Fin.castSucc).getLastD (Fin.last n)) b.castSucc ≤
        cyclicDist ((hist.map Fin.castSucc).getLastD (Fin.last n)) b'.castSucc ↔
      cyclicDist (hist.getLastD j₀) b ≤ cyclicDist (hist.getLastD j₀) b' := by
    intro b b'
    induction hist using List.reverseRecOn with
    | nil =>
      simp only [List.map_nil, List.getLastD_nil]
      rw [cyclicDist_eq, cyclicDist_eq, cyclicDist_eq, cyclicDist_eq]
      simp only [Fin.val_last, Fin.val_castSucc, hj₀]
      have := b.isLt; have := b'.isLt
      split_ifs <;> omega
    | append_singleton l a _ =>
      simpa using cyclicDist_castSucc_le_iff a b b'
  unfold IsRoundRobinChoice LP.IsCunninghamChoice
  rw [improving_hat hB hP.1, show Fin.castSucc j = Fin.castSuccEmb j from rfl, Finset.mem_map',
    Finset.forall_mem_map]
  simp only [Fin.coe_castSuccEmb, key]

theorem rules_dantzig_main (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (f : ℕ)
    (S : ℕ → Finset (Fin (n + 1))) :
    (IsWolfeRunWith P.atom (IsLinoptChoice P.atom) f S ∧ S 0 = hat B₀) ↔
      ∃ B, P.toLP.IsSimplexRunWith P.toLP.IsDantzigChoice f B ∧ B 0 = B₀ ∧
        ∀ k ≤ f, S k = hat (B k) :=
  run_hat_iff hP _ _ (fun _ hB j ↦ linopt_hat_iff hP hB j) B₀ hB₀ f S

theorem rules_bland_main (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (ρ : Fin (n + 1) → ℕ) (f : ℕ)
    (S : ℕ → Finset (Fin (n + 1))) :
    (IsWolfeRunWith P.atom (IsLeastLabelChoice P.atom ρ) f S ∧ S 0 = hat B₀) ↔
      ∃ B, P.toLP.IsSimplexRunWith (P.toLP.IsBlandChoice fun k ↦ ρ (Fin.castSucc k)) f B ∧
        B 0 = B₀ ∧ ∀ k ≤ f, S k = hat (B k) :=
  run_hat_iff hP _ _ (fun _ hB j ↦ leastLabel_hat_iff hP hB ρ j) B₀ hB₀ f S

theorem rules_zadeh_main (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (f : ℕ)
    (S : ℕ → Finset (Fin (n + 1))) (J' : ℕ → Fin (n + 1)) :
    (IsWolfeRunWithHist P.atom (IsLeastInsertedChoice P.atom) f S J' ∧ S 0 = hat B₀) ↔
      ∃ B J, P.toLP.IsSimplexRunWithHist P.toLP.IsZadehChoice f B J ∧ B 0 = B₀ ∧
        (∀ k ≤ f, S k = hat (B k)) ∧ ∀ k < f, J' k = Fin.castSucc (J k) :=
  runHist_hat_iff hP _ _ (fun hist _ hB j ↦ leastInserted_hat_iff hP hist hB j) B₀ hB₀ f S J'

theorem rules_cunningham_main (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (j₀ : Fin n) (f : ℕ)
    (S : ℕ → Finset (Fin (n + 1))) (J' : ℕ → Fin (n + 1)) :
    (IsWolfeRunWithHist P.atom (IsRoundRobinChoice P.atom (Fin.castSucc j₀)) f S J' ∧
        S 0 = hat B₀) ↔
      ∃ B J, P.toLP.IsSimplexRunWithHist (P.toLP.IsCunninghamChoice j₀) f B J ∧ B 0 = B₀ ∧
        (∀ k ≤ f, S k = hat (B k)) ∧ ∀ k < f, J' k = Fin.castSucc (J k) :=
  runHist_hat_iff hP _ _ (fun hist _ hB j ↦ roundRobin_hat_iff hP j₀ hist hB j) B₀ hB₀ f S J'

theorem rules_cunningham_slack_main (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (j₀ : Fin n) (hj₀ : (j₀ : ℕ) = 0)
    (f : ℕ) (S : ℕ → Finset (Fin (n + 1))) (J' : ℕ → Fin (n + 1)) :
    (IsWolfeRunWithHist P.atom (IsRoundRobinChoice P.atom (Fin.last n)) f S J' ∧
        S 0 = hat B₀) ↔
      ∃ B J, P.toLP.IsSimplexRunWithHist (P.toLP.IsCunninghamChoice j₀) f B J ∧ B 0 = B₀ ∧
        (∀ k ≤ f, S k = hat (B k)) ∧ ∀ k < f, J' k = Fin.castSucc (J k) :=
  runHist_hat_iff hP _ _ (fun hist _ hB j ↦ roundRobin_last_hat_iff hP j₀ hj₀ hist hB j)
    B₀ hB₀ f S J'

end IntLP

end WolfeSimplex

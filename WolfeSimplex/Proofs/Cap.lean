import WolfeSimplex.Defs.Cap
import WolfeSimplex.Defs.HistoryRules
import WolfeSimplex.Defs.RandomRules
import WolfeSimplex.Proofs.RuleRuns
import WolfeSimplex.Proofs.InducedLemmasTBound
import WolfeSimplex.Proofs.CapFacts
import WolfeSimplex.Proofs.HistoryRuns

/-!
# The cap constraint (paper: Appendix C.2 (`app:cor-rules`) (cap argument))

For an LP with integer data, rank `m`, a finite optimum, and only nondegenerate feasible
bases, the capped LP satisfies (A1)–(A3), and its simplex runs from `B₀ ∪ {cap}` are those of
the original LP from `B₀`.

The facts about bases, pivots and admissibility are in `Proofs/CapFacts.lean`; here the runs
with history-dependent rules (Zadeh, Cunningham) are transferred.
-/

namespace WolfeSimplex

open Finset

variable {m n : ℕ}

/-! ### Transfer of runs with a history -/

-- `cyclicDist_eq` and `cyclicDist_castSucc_le_iff` are in `Proofs/HistoryRuns.lean`.

namespace LP

/-- Runs with a history-dependent rule transfer from `L` to `Q` (an LP with one more label),
when feasible bases of `L` give feasible bases `B̂` of `Q`, the improving sets correspond, the
pivots of `Q` at `B̂` are the hats of the pivots of `L` at `B`, and the rules correspond
(`d₀` is an arbitrary label, only needed to have an element of `Fin n`). -/
theorem histRun_transfer_iff {m' : ℕ} (L : LP m n) (Q : LP m' (n + 1)) (d₀ : Fin n)
    (hfeas : ∀ B, L.IsFeasibleBasis B → Q.IsFeasibleBasis (hat B))
    (himp : ∀ B, L.IsFeasibleBasis B →
      Q.improving (hat B) = (L.improving B).map Fin.castSuccEmb)
    (hpiv : ∀ B, L.IsFeasibleBasis B → ∀ j' S', Q.IsPivot (hat B) j' S' ↔
      ∃ j B', j' = Fin.castSucc j ∧ L.IsPivot B j B' ∧ S' = hat B')
    (qch : List (Fin (n + 1)) → Finset (Fin (n + 1)) → Fin (n + 1) → Prop)
    (pch : List (Fin n) → Finset (Fin n) → Fin n → Prop)
    (hch : ∀ B, L.IsFeasibleBasis B → ∀ (hist : List (Fin n)) (j : Fin n),
      qch (hist.map Fin.castSucc) (hat B) (Fin.castSucc j) ↔ pch hist B j)
    (B₀ : Finset (Fin n)) (hB₀ : L.IsFeasibleBasis B₀) (f : ℕ)
    (B' : ℕ → Finset (Fin (n + 1))) (J' : ℕ → Fin (n + 1)) :
    (Q.IsSimplexRunWithHist qch f B' J' ∧ B' 0 = hat B₀) ↔
      ∃ B J, L.IsSimplexRunWithHist pch f B J ∧ B 0 = B₀ ∧
        (∀ k ≤ f, B' k = hat (B k)) ∧ ∀ k < f, J' k = Fin.castSucc (J k) := by
  have hpivfeas : ∀ {B B'' : Finset (Fin n)} {j : Fin n}, L.IsPivot B j B'' →
      L.IsFeasibleBasis B'' := by
    rintro B B'' j ⟨hB, hj, -, i, hi, rfl⟩
    exact (L.pivot_spec hB hj hi).1
  have hhist : ∀ (J : ℕ → Fin n) (k : ℕ), (∀ i < k, J' i = Fin.castSucc (J i)) →
      (List.range k).map J' = ((List.range k).map J).map Fin.castSucc := by
    intro J k h
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact h i (List.mem_range.1 hi)
  constructor
  · rintro ⟨⟨⟨-, hstep⟩, hlast⟩, hB'0⟩
    set B : ℕ → Finset (Fin n) := fun k ↦ IntLP.unhat (B' k) with hBdef
    set J : ℕ → Fin n := fun k ↦ if h : (J' k : ℕ) < n then ⟨J' k, h⟩ else d₀
      with hJdef
    have hJ : ∀ (j : Fin n) k, J' k = j.castSucc → J k = j := by
      intro j k h
      have hlt : (J' k : ℕ) < n := by rw [h]; exact j.isLt
      simp only [hJdef, hlt, ↓reduceDIte]
      ext
      simp [h]
    have key : ∀ k ≤ f, L.IsFeasibleBasis (B k) ∧ B' k = hat (B k) := by
      intro k
      induction k with
      | zero => intro _; simp only [hBdef, hB'0, IntLP.unhat_hat]; exact ⟨hB₀, trivial⟩
      | succ k ih =>
        intro hk
        obtain ⟨hBk, hSk⟩ := ih (by omega)
        obtain ⟨-, hp⟩ := hstep k (by omega)
        rw [hSk] at hp
        obtain ⟨j, B'', -, hpj, hS'⟩ := (hpiv _ hBk _ _).1 hp
        simp only [hBdef, hS', IntLP.unhat_hat]
        exact ⟨hpivfeas hpj, trivial⟩
    have step : ∀ k < f, J' k = Fin.castSucc (J k) ∧ L.IsPivot (B k) (J k) (B (k + 1)) := by
      intro k hk
      obtain ⟨hBk, hSk⟩ := key k hk.le
      obtain ⟨-, hp⟩ := hstep k hk
      rw [hSk] at hp
      obtain ⟨j, B'', hjj, hpj, hS'⟩ := (hpiv _ hBk _ _).1 hp
      have hJk : J k = j := hJ j k hjj
      have hBk1 : B (k + 1) = B'' := by simp only [hBdef, hS', IntLP.unhat_hat]
      rw [hJk, hBk1]
      exact ⟨hjj, hpj⟩
    refine ⟨B, J, ⟨⟨fun k hk ↦ (key k hk).1, fun k hk ↦ ⟨?_, (step k hk).2⟩⟩, ?_⟩,
      by simp only [hBdef, hB'0, IntLP.unhat_hat], fun k hk ↦ (key k hk).2,
      fun k hk ↦ (step k hk).1⟩
    · have hq := (hstep k hk).1
      rw [hhist J k (fun i hi ↦ (step i (by omega)).1), (key k hk.le).2, (step k hk).1] at hq
      exact (hch _ (key k hk.le).1 _ _).1 hq
    · rw [(key f le_rfl).2, himp _ (key f le_rfl).1, Finset.map_eq_empty] at hlast
      exact hlast
  · rintro ⟨B, J, ⟨⟨hfeasP, hstep⟩, hlast⟩, hB0, hB'B, hJ'⟩
    refine ⟨⟨⟨fun k hk ↦ ?_, fun k hk ↦ ⟨?_, ?_⟩⟩, ?_⟩, ?_⟩
    · rw [hB'B k hk]; exact hfeas _ (hfeasP k hk)
    · rw [hhist J k (fun i hi ↦ hJ' i (by omega)), hB'B k hk.le, hJ' k hk]
      exact (hch _ (hfeasP k hk.le) _ _).2 (hstep k hk).1
    · rw [hB'B k hk.le, hB'B (k + 1) hk, hJ' k hk]
      exact (hpiv _ (hfeasP k hk.le) _ _).2 ⟨J k, B (k + 1), rfl, (hstep k hk).2, rfl⟩
    · rw [hB'B f le_rfl, himp _ (hfeasP f le_rfl), hlast, Finset.map_empty]
    · rw [hB'B 0 (Nat.zero_le _), hB0]

end LP

namespace IntLP

/-- A label, from a feasible basis (`m ≥ 1`). -/
lemma exists_label (P : IntLP m n) (hm : 1 ≤ m) {B₀ : Finset (Fin n)}
    (hB₀ : P.toLP.IsFeasibleBasis B₀) : Nonempty (Fin n) := by
  obtain ⟨j, -⟩ : B₀.Nonempty := Finset.card_pos.1 (by rw [hB₀.1.1]; omega)
  exact ⟨j⟩

/-- Zadeh's rule at `B̂` (history mapped by `castSucc`) is Zadeh's rule at `B`. -/
lemma zadeh_hat_cap_iff (P : IntLP m n) {B : Finset (Fin n)} (hB : P.toLP.IsFeasibleBasis B)
    (hist : List (Fin n)) (j : Fin n) :
    P.cap.toLP.IsZadehChoice (hist.map Fin.castSucc) (hat B) (Fin.castSucc j) ↔
      P.toLP.IsZadehChoice hist B j := by
  unfold LP.IsZadehChoice
  rw [P.improving_hat_cap hB.1, show Fin.castSucc j = Fin.castSuccEmb j from rfl,
    Finset.mem_map', Finset.forall_mem_map]
  simp only [Fin.coe_castSuccEmb,
    List.count_map_of_injective _ _ (Fin.castSucc_injective n)]

/-- Cunningham's rule at `B̂` (history mapped by `castSucc`) is Cunningham's rule at `B`. -/
lemma cunningham_hat_cap_iff (P : IntLP m n) {B : Finset (Fin n)}
    (hB : P.toLP.IsFeasibleBasis B) (j₀ : Fin n) (hist : List (Fin n)) (j : Fin n) :
    P.cap.toLP.IsCunninghamChoice (Fin.castSucc j₀) (hist.map Fin.castSucc) (hat B)
        (Fin.castSucc j) ↔ P.toLP.IsCunninghamChoice j₀ hist B j := by
  unfold LP.IsCunninghamChoice
  rw [List.getLastD_map, P.improving_hat_cap hB.1,
    show Fin.castSucc j = Fin.castSuccEmb j from rfl, Finset.mem_map', Finset.forall_mem_map]
  simp only [Fin.coe_castSuccEmb, cyclicDist_castSucc_le_iff]

-- Not all hypotheses of the statements below are needed by their proofs (e.g. the runs only
-- need the finite optimum); they are kept in the statements, which match the paper.
set_option linter.unusedVariables false in
theorem cap_admissible_main (P : IntLP m n) (hm : 1 ≤ m) (hrank : P.toLP.A.rank = m)
    (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B) :
    P.cap.IsAdmissible := by
  exact P.cap_isAdmissible hrank hopt hnd

set_option linter.unusedVariables false in
theorem cap_bases_main (P : IntLP m n) (hm : 1 ≤ m) (hrank : P.toLP.A.rank = m)
    (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B) :
    P.cap.toLP.IsFeasibleBasis (hat B) ∧
    (∀ j, P.cap.toLP.reducedCost (hat B) (Fin.castSucc j) = P.toLP.reducedCost B j) ∧
    P.cap.toLP.improving (hat B) = (P.toLP.improving B).map Fin.castSuccEmb ∧
    ∀ j' S', P.cap.toLP.IsPivot (hat B) j' S' ↔
      ∃ j B', j' = Fin.castSucc j ∧ P.toLP.IsPivot B j B' ∧ S' = hat B' := by
  exact ⟨P.isFeasibleBasis_hat_cap hB, P.reducedCost_hat_cap hB.1, P.improving_hat_cap hB.1,
    P.isPivot_hat_cap_iff hopt hB⟩

set_option linter.unusedVariables false in
/-- What `LP.randomEdge_transfer` needs for the cap (also: pivots of `P` exist and are
unique). -/
theorem cap_pivotTo (P : IntLP m n) (hm : 1 ≤ m) (hrank : P.toLP.A.rank = m)
    (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B) (j : Fin n)
    (hj : j ∈ P.toLP.improving B) :
    (∀ B', P.toLP.IsPivot B j B' ↔ B' = P.toLP.pivotTo B j) ∧
    P.toLP.IsFeasibleBasis (P.toLP.pivotTo B j) ∧
    P.cap.toLP.pivotTo (hat B) (Fin.castSucc j) = hat (P.toLP.pivotTo B j) := by
  exact ⟨P.isPivot_iff_eq_pivotTo hopt hnd hB hj, P.pivotTo_hat_cap hopt hnd hB hj⟩

set_option linter.unusedVariables false in
theorem cap_zadeh_main (P : IntLP m n) (hm : 1 ≤ m) (hrank : P.toLP.A.rank = m)
    (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (f : ℕ)
    (B' : ℕ → Finset (Fin (n + 1))) (J' : ℕ → Fin (n + 1)) :
    (P.cap.toLP.IsSimplexRunWithHist P.cap.toLP.IsZadehChoice f B' J' ∧ B' 0 = hat B₀) ↔
      ∃ B J, P.toLP.IsSimplexRunWithHist P.toLP.IsZadehChoice f B J ∧ B 0 = B₀ ∧
        (∀ k ≤ f, B' k = hat (B k)) ∧ ∀ k < f, J' k = Fin.castSucc (J k) := by
  obtain ⟨d₀⟩ := P.exists_label hm hB₀
  exact LP.histRun_transfer_iff P.toLP P.cap.toLP d₀ (fun B hB ↦ P.isFeasibleBasis_hat_cap hB)
    (fun B hB ↦ P.improving_hat_cap hB.1) (fun B hB ↦ P.isPivot_hat_cap_iff hopt hB) _ _
    (fun B hB ↦ P.zadeh_hat_cap_iff hB) B₀ hB₀ f B' J'

set_option linter.unusedVariables false in
theorem cap_cunningham_main (P : IntLP m n) (hm : 1 ≤ m) (hrank : P.toLP.A.rank = m)
    (hopt : ∃ x, P.toLP.IsOptimalSolution x)
    (hnd : ∀ B, P.toLP.IsFeasibleBasis B → P.toLP.IsNondegenerate B)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (j₀ : Fin n) (f : ℕ)
    (B' : ℕ → Finset (Fin (n + 1))) (J' : ℕ → Fin (n + 1)) :
    (P.cap.toLP.IsSimplexRunWithHist (P.cap.toLP.IsCunninghamChoice (Fin.castSucc j₀)) f B' J' ∧
        B' 0 = hat B₀) ↔
      ∃ B J, P.toLP.IsSimplexRunWithHist (P.toLP.IsCunninghamChoice j₀) f B J ∧ B 0 = B₀ ∧
        (∀ k ≤ f, B' k = hat (B k)) ∧ ∀ k < f, J' k = Fin.castSucc (J k) := by
  obtain ⟨d₀⟩ := P.exists_label hm hB₀
  exact LP.histRun_transfer_iff P.toLP P.cap.toLP d₀ (fun B hB ↦ P.isFeasibleBasis_hat_cap hB)
    (fun B hB ↦ P.improving_hat_cap hB.1) (fun B hB ↦ P.isPivot_hat_cap_iff hopt hB) _ _
    (fun B hB ↦ P.cunningham_hat_cap_iff hB j₀) B₀ hB₀ f B' J'

end IntLP

end WolfeSimplex

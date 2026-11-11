import WolfeSimplex.MainResults
import WolfeSimplex.Proofs.PaperPath

/-!
# Conditional transfers of iteration bounds and queried-label events

External simplex lower bounds remain explicit premises, not axioms. Randomized
run lengths are treated as distributions on the number of pivots. Their expected
length is the supremum of the expected truncated lengths, allowing infinity.
-/

namespace WolfeSimplex.Transfers

open Finset Wolfe
variable {m n : ℕ}

/-- Any property of complete run lengths transfers in both directions for the
induced pivot rule. This includes upper bounds as well as lower bounds. -/
theorem iteration_property (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀)
    (choice : Finset (Fin (n + 1)) → Fin (n + 1) → Prop) (R : ℕ → Prop) :
    (∀ f B, P.toLP.IsSimplexRunWith (fun B j ↦ choice (hat B) j.castSucc) f B →
      B 0 = B₀ → R f) ↔
    (∀ f S, IsWolfeRunWith P.atom choice f S → S 0 = hat B₀ → R f) := by
  have hcorr := IntLP.run_hat_iff (P := P) hP choice
    (fun B j ↦ choice (hat B) j.castSucc) (fun _ _ _ ↦ Iff.rfl) B₀ hB₀
  constructor
  · intro h f S hS h0
    obtain ⟨B, hB, hB0, _⟩ := (hcorr f S).mp ⟨hS, h0⟩
    exact h f B hB hB0
  · intro h f B hB h0
    have hs := (hcorr f (fun k ↦ hat (B k))).mpr ⟨B, hB, h0, fun _ _ ↦ rfl⟩
    exact h f _ hs.1 hs.2

/-- A rule that can always select an improving atom induces a pivot rule that
can always select an improving label at every feasible basis. -/
theorem induced_choice_total (P : IntLP m n) (hP : P.IsAdmissible)
    (choice : Finset (Fin (n + 1)) → Fin (n + 1) → Prop)
    (htotal : ∀ S, IsCorral P.atom S → (improving P.atom (affineMin P.atom S)).Nonempty →
      ∃ j ∈ improving P.atom (affineMin P.atom S), choice S j) :
    ∀ B, P.toLP.IsFeasibleBasis B → (P.toLP.improving B).Nonempty →
      ∃ j ∈ P.toLP.improving B, choice (hat B) j.castSucc := by
  intro B hB hΓ
  have ha := PaperPath.part_a P hP B hB
  have hΓ' : (improving P.atom (affineMin P.atom (hat B))).Nonempty := by
    rw [ha.2.1]
    exact hΓ.map
  obtain ⟨j, hj, hch⟩ := htotal (hat B) ha.1 hΓ'
  rw [ha.2.1, Finset.mem_map] at hj
  obtain ⟨k, hk, rfl⟩ := hj
  exact ⟨k, hk, hch⟩

/-- A source lower bound for all Dantzig runs transfers to all linopt runs. -/
theorem dantzig_lower_bound (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (L : ℕ)
    (hbound : ∀ f B, P.toLP.IsSimplexRunWith P.toLP.IsDantzigChoice f B →
      B 0 = B₀ → L ≤ f) :
    ∀ f S, IsWolfeRunWith P.atom (IsLinoptChoice P.atom) f S →
      S 0 = hat B₀ → L ≤ f := by
  intro f S hS h0
  obtain ⟨B, hB, hB0, _⟩ := (rules_dantzig P hP B₀ hB₀ f S).mp ⟨hS, h0⟩
  exact hbound f B hB hB0

theorem bland_lower_bound (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (ρ : Fin (n + 1) → ℕ) (L : ℕ)
    (hbound : ∀ f B, P.toLP.IsSimplexRunWith
      (P.toLP.IsBlandChoice fun j ↦ ρ j.castSucc) f B → B 0 = B₀ → L ≤ f) :
    ∀ f S, IsWolfeRunWith P.atom (IsLeastLabelChoice P.atom ρ) f S →
      S 0 = hat B₀ → L ≤ f := by
  intro f S hS h0
  obtain ⟨B, hB, hB0, _⟩ := (rules_bland P hP B₀ hB₀ ρ f S).mp ⟨hS, h0⟩
  exact hbound f B hB hB0

theorem zadeh_lower_bound (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (L : ℕ)
    (hbound : ∀ f B J, P.toLP.IsSimplexRunWithHist P.toLP.IsZadehChoice f B J →
      B 0 = B₀ → L ≤ f) :
    ∀ f S J, IsWolfeRunWithHist P.atom (IsLeastInsertedChoice P.atom) f S J →
      S 0 = hat B₀ → L ≤ f := by
  intro f S J hS h0
  obtain ⟨B, J', hB, hB0, _⟩ := (rules_zadeh P hP B₀ hB₀ f S J).mp ⟨hS, h0⟩
  exact hbound f B J' hB hB0

theorem cunningham_lower_bound (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (j₀ : Fin n) (L : ℕ)
    (hbound : ∀ f B J, P.toLP.IsSimplexRunWithHist (P.toLP.IsCunninghamChoice j₀) f B J →
      B 0 = B₀ → L ≤ f) :
    ∀ f S J, IsWolfeRunWithHist P.atom (IsRoundRobinChoice P.atom j₀.castSucc) f S J →
      S 0 = hat B₀ → L ≤ f := by
  intro f S J hS h0
  obtain ⟨B, J', hB, hB0, _⟩ :=
    (rules_cunningham P hP B₀ hB₀ j₀ f S J).mp ⟨hS, h0⟩
  exact hbound f B J' hB hB0

/-- Count transitions in a nonempty trace. The empty case is harmless. -/
def steps {α : Type} (trace : List α) : ℕ := trace.length - 1

/-- Expected value of a natural-valued distribution, in the extended nonnegative reals. -/
noncomputable def expectation (μ : PMF ℕ) : ENNReal := ∑' k, μ k * k

/-- Expected total iterations as the supremum of expected finite prefixes. -/
noncomputable def expectedLength {α : Type} (prefixes : ℕ → PMF (List α)) : ENNReal :=
  ⨆ k, expectation ((prefixes k).map steps)

@[simp] theorem steps_map {α β : Type} (f : α → β) (trace : List α) :
    steps (trace.map f) = steps trace := by simp [steps]

theorem random_edge_count (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (k : ℕ) :
    (Wolfe.randomRun P.atom (Wolfe.randomInsertion P.atom) k (hat B₀)).map steps =
      (P.toLP.randomRun P.toLP.randomEdge k B₀).map steps := by
  rw [rules_random_edge P hP B₀ hB₀ k, PMF.map_comp]
  congr 1
  funext trace
  simp

theorem random_bland_count (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (k : ℕ) :
    (Wolfe.randomOrderRun P.atom k (hat B₀)).map steps =
      (P.toLP.randomBlandRun k B₀).map steps := by
  rw [rules_random_bland P hP B₀ hB₀ k, PMF.map_comp]
  congr 1
  funext trace
  simp

theorem random_edge_expected (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) :
    expectedLength (fun k ↦ Wolfe.randomRun P.atom (Wolfe.randomInsertion P.atom) k (hat B₀)) =
      expectedLength (fun k ↦ P.toLP.randomRun P.toLP.randomEdge k B₀) := by
  unfold expectedLength
  congr 1
  funext k
  rw [random_edge_count P hP B₀ hB₀]

theorem random_bland_expected (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) :
    expectedLength (fun k ↦ Wolfe.randomOrderRun P.atom k (hat B₀)) =
      expectedLength (fun k ↦ P.toLP.randomBlandRun k B₀) := by
  unfold expectedLength
  congr 1
  funext k
  rw [random_bland_count P hP B₀ hB₀]

/-- Both randomized rules transfer any expected lower bound, including infinity. -/
theorem random_expected_lower_bounds (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (L : ENNReal) :
    (L ≤ expectedLength (fun k ↦ P.toLP.randomRun P.toLP.randomEdge k B₀) ↔
      L ≤ expectedLength (fun k ↦ Wolfe.randomRun P.atom
        (Wolfe.randomInsertion P.atom) k (hat B₀))) ∧
    (L ≤ expectedLength (fun k ↦ P.toLP.randomBlandRun k B₀) ↔
      L ≤ expectedLength (fun k ↦ Wolfe.randomOrderRun P.atom k (hat B₀))) := by
  rw [random_edge_expected P hP B₀ hB₀, random_bland_expected P hP B₀ hB₀]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- A specified entering label is exactly the specified inserted atom. -/
theorem pivot_label (P : IntLP m n) (hP : P.IsAdmissible)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B) (j : Fin n) (B' : Finset (Fin n)) :
    P.toLP.IsPivot B j B' ↔ MajorCycle P.atom (hat B) j.castSucc (hat B') := by
  constructor
  · rintro ⟨_, hj, _, i, hi, rfl⟩
    exact ((PaperPath.part_b P hP B hB j hj i hi).2.2.2.2 _).mpr rfl
  · intro h
    have hj : j ∈ P.toLP.improving B := by
      have := h.2.1
      rw [(PaperPath.part_a P hP B hB).2.1] at this
      simpa only [show j.castSucc = Fin.castSuccEmb j from rfl, Finset.mem_map'] using this
    obtain ⟨i, hi⟩ := LP.exists_leavingLabel hP.2.2.1 hB hj
    have heq := ((PaperPath.part_b P hP B hB j hj i hi).2.2.2.2 _).mp h
    exact ⟨hB, hj, hB.1.not_mem_of_mem_improving hj, i, hi, hat_injective heq⟩

/-- The queried-label event transfers over a complete simplex run. -/
theorem ever_enters_iff (P : IntLP m n) (hP : P.IsAdmissible)
    (f : ℕ) (B : ℕ → Finset (Fin n)) (hB : P.toLP.IsSimplexRun f B) (j : Fin n) :
    (∃ k < f, P.toLP.IsPivot (B k) j (B (k + 1))) ↔
      ∃ k < f, MajorCycle P.atom (hat (B k)) j.castSucc (hat (B (k + 1))) := by
  constructor <;> rintro ⟨k, hk, he⟩
  · exact ⟨k, hk, (pivot_label P hP (B k) (hB.1 k hk.le) j _).mp he⟩
  · exact ⟨k, hk, (pivot_label P hP (B k) (hB.1 k hk.le) j _).mpr he⟩

end WolfeSimplex.Transfers

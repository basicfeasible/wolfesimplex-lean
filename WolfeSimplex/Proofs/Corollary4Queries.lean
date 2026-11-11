import WolfeSimplex.Proofs.Corollary4Count
import WolfeSimplex.Proofs.MDPFeasibleBasis
import WolfeSimplex.Proofs.QueryEvents
import WolfeSimplex.Proofs.Corollary2Scaling

/-! Shortest-point initialization and both PSPACE query events. The source
hardness theorem is allowed to quantify over every Dantzig tie resolution, as
in Fearnley--Savani (2015), Theorems 1.1 and 1.2. -/
namespace WolfeSimplex.PaperCorollary4
open Finset Wolfe
variable {m n : ℕ}

def capEnum (e : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  Fin.snoc (fun i ↦ (e i).castSucc) (Fin.last n)

@[simp] theorem basisOf_capEnum (e : Fin m → Fin n) :
    basisOf (capEnum e) = hat (basisOf e) := by
  ext j
  induction j using Fin.lastCases with
  | last => simp [basisOf, capEnum, hat]; exact ⟨Fin.last m, by simp⟩
  | cast j =>
    simp only [IntLP.castSucc_mem_hat, basisOf, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      induction i using Fin.lastCases with
      | last => exact (Fin.castSucc_ne_last j (by simpa [capEnum] using hi.symm)).elim
      | cast i => exact ⟨i, by simpa [capEnum] using hi⟩
    · rintro ⟨i, rfl⟩; exact ⟨i.castSucc, by simp [capEnum]⟩

structure QueryInput (m n : ℕ) where
  lp : RatLP m n
  initial : Fin m → Fin n
  feasible : lp.toLP.IsFeasibleBasis (basisOf initial)
  owner : Fin n → Fin m
  positive : ∀ i, 0 < lp.toLP.b i
  offOwner : ∀ i j, i ≠ owner j → lp.toLP.A i j ≤ 0
  terminates : ∃ f B, lp.toLP.IsSimplexRunWith lp.toLP.IsDantzigChoice f B ∧
    B 0 = basisOf initial

namespace QueryInput
variable (I : QueryInput m n)

def target : IntLP (m + 2) (n + 2) := I.lp.integerize.cap.shieldLP (capEnum I.initial)

theorem integer_feasible (B : Finset (Fin n)) :
    I.lp.integerize.toLP.IsFeasibleBasis B ↔ I.lp.toLP.IsFeasibleBasis B := by
  rw [I.lp.integerize_eq_scale]
  exact I.lp.toLP.scale_isFeasibleBasis_iff
    (fun i ↦ Nat.cast_pos.mpr (I.lp.rowFactor_pos i)) _ B

theorem integer_nondegenerate (B : Finset (Fin n))
    (hB : I.lp.integerize.toLP.IsFeasibleBasis B) : I.lp.integerize.toLP.IsNondegenerate B :=
  (I.lp.integerize_nondegenerate B).2
    (I.lp.toLP.nondegenerate_of_columnOwners I.owner I.positive I.offOwner B
      ((I.integer_feasible B).1 hB))

theorem integer_optimum : ∃ x, I.lp.integerize.toLP.IsOptimalSolution x := by
  obtain ⟨f, B, hB, _⟩ := I.terminates
  have hI := (I.lp.integerize_run f B).2 hB
  have hf := hI.1.1 f le_rfl
  exact ⟨_, ((LP.optimal_iff hf (I.integer_nondegenerate _ hf)).2 hI.2).2⟩

theorem capped_admissible : I.lp.integerize.cap.IsAdmissible := by
  have hf := (I.integer_feasible _).2 I.feasible
  exact I.lp.integerize.cap_isAdmissible (PaperCorollary2.rank_of_basis _ _ hf.1)
    I.integer_optimum I.integer_nondegenerate

theorem capped_start : I.lp.integerize.cap.toLP.IsFeasibleBasis
    (basisOf (capEnum I.initial)) := by
  rw [basisOf_capEnum]
  exact I.lp.integerize.isFeasibleBasis_hat_cap ((I.integer_feasible _).2 I.feasible)

theorem target_integer : ∀ j k, ∃ z : ℤ, I.target.atom j k = z :=
  I.target.atom_integral

theorem unique_shortest : ∀ j ≠ Fin.last (n + 2),
    normSq (I.target.atom (Fin.last (n + 2))) < normSq (I.target.atom j) :=
  (InitRuns.init_linopt_main _ I.capped_admissible _ I.capped_start).2.2.1

/-- Every complete target run, hence also the fixed-index run, has a source
Dantzig suffix. The queried original label is absent throughout the prefix. -/
theorem trace (g : ℕ) (S : ℕ → Finset (Fin (n + 3)))
    (hS : IsWolfeRunWith I.target.atom (IsLinoptChoice I.target.atom) g S)
    (h0 : S 0 = {Fin.last (n + 2)}) :
    m + 2 ≤ g ∧
    (∀ k < m + 2, ∃ l ∈ (hat (hat (basisOf I.initial))).map Fin.castSuccEmb,
      l ∉ S k ∧ S (k + 1) = insert l (S k)) ∧
    ∃ B, I.lp.toLP.IsSimplexRunWith I.lp.toLP.IsDantzigChoice (g - (m + 2)) B ∧
      B 0 = basisOf I.initial ∧
      ∀ k ≤ g - (m + 2), S (m + 2 + k) = hat (hat (hat (B k))) := by
  obtain ⟨hg, hp, C, hC, hC0, hSC⟩ :=
    (InitRuns.init_linopt_main _ I.capped_admissible _ I.capped_start).2.2.2.1 g S hS h0
  simp only [basisOf_capEnum] at hp hC0
  obtain ⟨B, hB, hB0, hCB⟩ := (I.lp.integerize.cap_run_hat_iff I.integer_optimum
    _ _ (fun _ hB j ↦ IntLP.dantzig_hat_cap_iff hB j) _
    ((I.integer_feasible _).2 I.feasible) _ C).1 ⟨hC, hC0⟩
  exact ⟨hg, hp, B, (I.lp.integerize_run _ B).1 hB, hB0,
    fun k hk ↦ by rw [hSC k hk, hCB k hk]⟩

/-- A label absent from the source initial basis is inserted in the target
exactly when it enters the source basis. Final-support membership also agrees. -/
theorem queries (j : Fin n) (hj : j ∉ basisOf I.initial)
    (g : ℕ) (S : ℕ → Finset (Fin (n + 3)))
    (hS : IsWolfeRunWith I.target.atom (IsLinoptChoice I.target.atom) g S)
    (h0 : S 0 = {Fin.last (n + 2)}) :
    ∃ B, I.lp.toLP.IsSimplexRunWith I.lp.toLP.IsDantzigChoice (g - (m + 2)) B ∧
      B 0 = basisOf I.initial ∧
      ((∃ k < g, MajorCycle I.target.atom (S k) j.castSucc.castSucc.castSucc (S (k + 1))) ↔
        ∃ k < g - (m + 2), I.lp.toLP.IsPivot (B k) j (B (k + 1))) ∧
      (j.castSucc.castSucc.castSucc ∈ S g ↔ j ∈ B (g - (m + 2))) := by
  obtain ⟨hg, hp, B, hB, hB0, hSB⟩ := I.trace g S hS h0
  have hprefix : ∀ k ≤ m + 2, j.castSucc.castSucc.castSucc ∉ S k := by
    intro k hk
    induction k with
    | zero => simp [h0]
    | succ k ih =>
      obtain ⟨l, hl, _, he⟩ := hp k (by omega)
      rw [he, mem_insert]
      have hneq : j.castSucc.castSucc.castSucc ≠ l := by
        intro heq
        rw [← heq] at hl
        have : j ∈ basisOf I.initial := by
          have hh := Finset.mem_map.mp hl
          obtain ⟨a, ha, he⟩ := hh
          have hea : a = j.castSucc.castSucc := Fin.castSucc_injective _ he
          rw [hea] at ha
          simpa only [IntLP.castSucc_mem_hat] using ha
        exact hj this
      exact fun h ↦ h.elim hneq (ih (by omega))
  have hstep : ∀ k < g - (m + 2),
      MajorCycle I.target.atom (S (m + 2 + k)) j.castSucc.castSucc.castSucc
        (S (m + 2 + (k + 1))) ↔ I.lp.toLP.IsPivot (B k) j (B (k + 1)) := by
    intro k hk
    obtain ⟨l, _, hl⟩ := hB.1.2 k hk
    have hlf := hl.fresh
    have hfresh : l.castSucc.castSucc.castSucc ∈ S (m + 2 + (k + 1)) ∧
        l.castSucc.castSucc.castSucc ∉ S (m + 2 + k) := by
      rw [hSB (k + 1) (by omega), hSB k hk.le]
      simpa only [IntLP.castSucc_mem_hat] using hlf
    constructor
    · intro h
      have he := h.label_eq_of_fresh hfresh.1 hfresh.2
      have : j = l := Fin.castSucc_injective _ (Fin.castSucc_injective _ (Fin.castSucc_injective _ he))
      exact this.symm ▸ hl
    · intro h
      obtain ⟨a, _, ha⟩ := hS.1.2 (m + 2 + k) (by omega)
      have haf : MajorCycle I.target.atom (S (m + 2 + k)) a
          (S (m + 2 + (k + 1))) := by simpa only [Nat.add_assoc] using ha
      have hjfresh : j.castSucc.castSucc.castSucc ∈ S (m + 2 + (k + 1)) ∧
          j.castSucc.castSucc.castSucc ∉ S (m + 2 + k) := by
        rw [hSB (k + 1) (by omega), hSB k hk.le]
        simpa only [IntLP.castSucc_mem_hat] using h.fresh
      have he := haf.label_eq_of_fresh hjfresh.1 hjfresh.2
      exact he ▸ haf
  refine ⟨B, hB, hB0, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨k, hk, he⟩
    by_cases hkp : k < m + 2
    · obtain ⟨l, _, hn, hs⟩ := hp k hkp
      have heq := he.label_eq_of_fresh (hs ▸ mem_insert_self _ _) hn
      have : j.castSucc.castSucc.castSucc ∈ S (k + 1) := by rw [heq, hs]; simp
      exact (hprefix (k + 1) (by omega) this).elim
    · refine ⟨k - (m + 2), by omega, (hstep _ (by omega)).1 ?_⟩
      simpa only [show m + 2 + (k - (m + 2)) = k by omega,
        show m + 2 + (k - (m + 2) + 1) = k + 1 by omega] using he
  · rintro ⟨k, hk, he⟩
    exact ⟨m + 2 + k, by omega, by simpa only [Nat.add_assoc] using (hstep k hk).2 he⟩
  · have he := hSB (g - (m + 2)) le_rfl
    rw [show m + 2 + (g - (m + 2)) = g by omega] at he
    rw [he]
    simp only [IntLP.castSucc_mem_hat]

end QueryInput
end WolfeSimplex.PaperCorollary4

import WolfeSimplex.MainResults

/-!
# Theorem 1 following the paper's composition of lemmas

Part (a) composes Lemmas 2, 4 and 5. Lemma 4's gap formula is derived
from Lemma 3 and the affine-minimizer criterion in `Proofs/InducedLemmas`.
Part (b) transports Lemma 6 through Lemma 2. Part (c) is an induction
using these parts (a) and (b). Part (d) uses part (a) and Lemma 1(c).
These are proofs, not additional assumptions about the correspondence.
-/

namespace WolfeSimplex.PaperPath

open Finset Wolfe IntLP
variable {m n : ℕ}

/-- Part (a): Lemmas 2, 4 and 5. -/
theorem part_a (P : IntLP m n) (hP : P.IsAdmissible)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B) :
    IsCorral P.atom (hat B) ∧
    improving P.atom (affineMin P.atom (hat B)) = (P.toLP.improving B).map Fin.castSuccEmb ∧
    ∃ κ : ℝ, 0 < κ ∧
      (∀ j : Fin n, gap P.atom (Fin.castSucc j) (affineMin P.atom (hat B)) =
        κ * P.toLP.reducedCost B j) ∧
      gap P.atom (Fin.last n) (affineMin P.atom (hat B)) = 0 := by
  have hh := hom P hP
  have hS := (hh.2.1 (hat B)).2 ⟨B, hB, rfl⟩
  obtain ⟨_, hg, hs⟩ := corral P hP (hat B) hS.1
  have hrc := (hh.2.2.1 B hB).2.2
  let κ : ℝ := (P.N : ℝ) ^ 2 * P.sS (hat B)
  have hκ : 0 < κ := mul_pos (sq_pos_of_pos (P.N_pos' hP.1)) (hs hS)
  have hgap : ∀ j : Fin n, gap P.atom j.castSucc (affineMin P.atom (hat B)) =
      κ * P.toLP.reducedCost B j := by
    intro j
    rw [hg, hrc.1 j]
  have hlast : gap P.atom (Fin.last n) (affineMin P.atom (hat B)) = 0 := by
    rw [hg, hrc.2, mul_zero]
  refine ⟨(bases_corrals P hP (hat B) hS).2.2.2, ?_, κ, hκ, hgap, hlast⟩
  ext k
  induction k using Fin.lastCases with
  | last => simp [Wolfe.improving, hlast, Finset.mem_map, Fin.castSucc_ne_last]
  | cast k =>
    simp only [Wolfe.improving, mem_filter, mem_univ, true_and,
      show Fin.castSucc k = Fin.castSuccEmb k from rfl, Finset.mem_map', LP.improving]
    change gap P.atom k.castSucc (affineMin P.atom (hat B)) < 0 ↔
      P.toLP.reducedCost B k < 0
    rw [hgap]
    constructor
    · intro h
      by_contra h'
      have := not_lt.mp h'
      nlinarith
    · exact mul_neg_of_pos_of_neg hκ

/-- Part (b): Lemmas 2 and 6. -/
theorem part_b (P : IntLP m n) (hP : P.IsAdmissible)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B)
    (j : Fin n) (hj : j ∈ P.toLP.improving B) (i : Fin n) (hi : P.toLP.IsLeavingLabel B j i) :
    ¬ IsCorral P.atom (insert (Fin.castSucc j) (hat B)) ∧
    (∃ s', MinorCycle P.atom ⟨insert (Fin.castSucc j) (hat B), affineCoeffs P.atom (hat B)⟩ s') ∧
    (∀ s', MinorCycle P.atom ⟨insert (Fin.castSucc j) (hat B), affineCoeffs P.atom (hat B)⟩ s' →
      s'.S = hat (insert j (B.erase i))) ∧
    IsCorral P.atom (hat (insert j (B.erase i))) ∧
    ∀ S' : Finset (Fin (n + 1)),
      MajorCycle P.atom (hat B) (Fin.castSucc j) S' ↔ S' = hat (insert j (B.erase i)) := by
  have hh := hom P hP
  have hS := (hh.2.1 (hat B)).2 ⟨B, hB, rfl⟩
  have hj' : P.inducedLP.reducedCost (hat B) j.castSucc < 0 := by
    rw [(hh.2.2.1 B hB).2.2.1 j]
    exact (Finset.mem_filter.mp hj).2
  have hi' := ((hh.2.2.2.1 B hB j hj).2 i.castSucc).2 ⟨i, rfl, hi⟩
  simpa only [hat_insert_erase] using
    pivot P hP (hat B) hS j.castSucc hj' i.castSucc hi'

private theorem major_step {m n : ℕ} (P : IntLP m n) (hP : P.IsAdmissible)
    {B : Finset (Fin n)} (hB : P.toLP.IsFeasibleBasis B)
    {j : Fin (n + 1)} {S' : Finset (Fin (n + 1))}
    (h : MajorCycle P.atom (hat B) j S') :
    ∃ j' i, j' ∈ P.toLP.improving B ∧ P.toLP.IsLeavingLabel B j' i ∧
      S' = hat (insert j' (B.erase i)) := by
  have hj := h.2.1
  rw [(part_a P hP B hB).2.1, Finset.mem_map] at hj
  obtain ⟨j', hj', rfl⟩ := hj
  obtain ⟨i, hi⟩ := LP.exists_leavingLabel hP.2.2.1 hB hj'
  exact ⟨j', i, hj', hi, ((part_b P hP B hB j' hj' i hi).2.2.2.2 S').1 h⟩

/-- Part (c): complete runs, by induction using parts (a) and (b). -/
theorem part_c (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀)
    (f : ℕ) (S : ℕ → Finset (Fin (n + 1))) :
    (IsWolfeRun P.atom f S ∧ S 0 = hat B₀) ↔
      ∃ B : ℕ → Finset (Fin n), P.toLP.IsSimplexRun f B ∧ B 0 = B₀ ∧
        ∀ k ≤ f, S k = hat (B k) := by
  constructor
  · rintro ⟨⟨-, hmaj, hlast⟩, hS0⟩
    set B : ℕ → Finset (Fin n) := fun k ↦ unhat (S k)
    have key : ∀ k ≤ f, P.toLP.IsFeasibleBasis (B k) ∧ S k = hat (B k) := by
      intro k
      induction k with
      | zero => intro _; simp only [B, hS0, unhat_hat]; exact ⟨hB₀, trivial⟩
      | succ k ih =>
        intro hk
        obtain ⟨hBk, hSk⟩ := ih (by omega)
        obtain ⟨j, hj⟩ := hmaj k (by omega)
        rw [hSk] at hj
        obtain ⟨j', i, hj', hi, hS'⟩ := major_step P hP hBk hj
        have hB' := (LP.pivot_spec hBk hj' hi).1
        simp only [B, hS', unhat_hat]
        exact ⟨hB', trivial⟩
    refine ⟨B, ⟨fun k hk ↦ (key k hk).1, fun k hk ↦ ?_, ?_⟩, by simp [B, hS0, unhat_hat],
      fun k hk ↦ (key k hk).2⟩
    · obtain ⟨hBk, hSk⟩ := key k hk.le
      obtain ⟨j, hj⟩ := hmaj k hk
      rw [hSk] at hj
      obtain ⟨j', i, hj', hi, hS'⟩ := major_step P hP hBk hj
      refine ⟨j', hj', hBk, hj', hBk.1.not_mem_of_mem_improving hj', i, hi, ?_⟩
      simp only [B, hS', unhat_hat]
    · obtain ⟨hBf, hSf⟩ := key f le_rfl
      rw [hSf, (part_a P hP _ hBf).2.1, Finset.map_eq_empty] at hlast
      exact hlast
  · rintro ⟨B, ⟨hfeas, hpiv, hlast⟩, hB0, hS⟩
    refine ⟨⟨fun k hk ↦ ?_, fun k hk ↦ ?_, ?_⟩, by rw [hS 0 (Nat.zero_le _), hB0]⟩
    · rw [hS k hk]; exact (part_a P hP _ (hfeas k hk)).1
    · obtain ⟨j, hj, -, -, -, i, hi, heq⟩ := hpiv k hk
      refine ⟨Fin.castSucc j, ?_⟩
      rw [hS k hk.le, hS (k + 1) hk, heq]
      exact ((part_b P hP _ (hfeas k hk.le) j hj i hi).2.2.2.2 _).2 rfl
    · rw [hS f le_rfl, (part_a P hP _ (hfeas f le_rfl)).2.1, hlast, Finset.map_empty]


/-- Part (d): stopping and optimality, from part (a) and Lemma 1(c). -/
theorem part_d (P : IntLP m n) (hP : P.IsAdmissible)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B) :
    (improving P.atom (affineMin P.atom (hat B)) = ∅ ∧
      IsMinNormPoint P.atom (affineMin P.atom (hat B))) ↔ P.toLP.IsOptimalBasis B := by
  have ha := part_a P hP B hB
  have hc := ha.1
  have hcriterion := (affine_min P.atom (hat B) hc.1 hc.2.1).2.2.2 hc
  rw [LP.optimal_iff hB (hP.2.2.2 B hB)]
  constructor
  · intro h
    have hzero : (P.toLP.improving B).map Fin.castSuccEmb = ∅ := ha.2.1.symm.trans h.1
    exact Finset.map_eq_empty.mp hzero
  · intro h
    have hzero : improving P.atom (affineMin P.atom (hat B)) = ∅ := by
      rw [ha.2.1, h, Finset.map_empty]
    exact ⟨hzero, hcriterion.mpr hzero⟩

end WolfeSimplex.PaperPath

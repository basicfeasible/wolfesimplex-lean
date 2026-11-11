import WolfeSimplex.Defs.NetworkFlow
import WolfeSimplex.Proofs.RunLocal

/-!
# Capacity-slack conversion (Appendix C.4)

The bounded-variable model converts to standard form with the same improving
choices, ratio tests, pivots and complete run lengths. Upper-bound entries use
capacity slacks with negated reduced costs, and bound flips are retained.
Strictly interior tree flows and positive capacities give nondegenerate
standard-form bases.
-/

namespace WolfeSimplex.BoundedLP

open Finset Matrix

variable {m n : ℕ} (P : BoundedLP m n) (S : State n)

@[simp] theorem lower_ne_upper (i j : Fin n) : lower i ≠ upper j := by
  intro h
  have hv := congrArg Fin.val h
  simp [lower, upper] at hv
  omega

@[simp] theorem upper_ne_lower (i j : Fin n) : upper i ≠ lower j :=
  (lower_ne_upper j i).symm

@[simp] theorem lower_inj (i j : Fin n) : lower i = lower j ↔ i = j := by
  simp [lower]

@[simp] theorem upper_inj (i j : Fin n) : upper i = upper j ↔ i = j := by
  simp [upper]

@[simp] theorem lower_mem_map (t : Finset (Fin n)) (j : Fin n) :
    lower j ∈ t.map (Fin.castAddEmb n) ↔ j ∈ t := by
  change Fin.castAddEmb n j ∈ t.map (Fin.castAddEmb n) ↔ j ∈ t
  rw [Finset.mem_map']

@[simp] theorem upper_mem_map (t : Finset (Fin n)) (j : Fin n) :
    upper j ∈ t.map (Fin.natAddEmb n) ↔ j ∈ t := by
  change Fin.natAddEmb n j ∈ t.map (Fin.natAddEmb n) ↔ j ∈ t
  rw [Finset.mem_map']

@[simp] theorem lower_not_mem_upper_map (t : Finset (Fin n)) (j : Fin n) :
    lower j ∉ t.map (Fin.natAddEmb n) := by
  intro h
  obtain ⟨i, -, hi⟩ := Finset.mem_map.mp h
  exact upper_ne_lower i j hi

@[simp] theorem upper_not_mem_lower_map (t : Finset (Fin n)) (j : Fin n) :
    upper j ∉ t.map (Fin.castAddEmb n) := by
  intro h
  obtain ⟨i, -, hi⟩ := Finset.mem_map.mp h
  exact lower_ne_upper i j hi

@[simp] theorem mem_active_lower (j : Fin n) :
    lower j ∈ S.activeBounds ↔ j ∉ S.tree ∧ j ∉ S.atUpper := by
  simp only [State.activeBounds, Finset.mem_union, lower_mem_map,
    lower_not_mem_upper_map, or_false, Finset.mem_sdiff, Finset.mem_univ,
    true_and, not_or]

@[simp] theorem mem_active_upper (j : Fin n) :
    upper j ∈ S.activeBounds ↔ j ∈ S.atUpper := by
  simp only [State.activeBounds, Finset.mem_union, upper_not_mem_lower_map,
    upper_mem_map, false_or]

@[simp] theorem mem_basis_lower (j : Fin n) :
    lower j ∈ S.basis ↔ j ∈ S.tree ∨ j ∈ S.atUpper := by
  simp only [State.basis, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_active_lower]
  tauto

@[simp] theorem mem_basis_upper (j : Fin n) :
    upper j ∈ S.basis ↔ j ∉ S.atUpper := by
  simp only [State.basis, Finset.mem_sdiff, Finset.mem_univ, true_and, mem_active_upper]

@[simp] theorem lift_lower (x : Fin n → ℝ) (j : Fin n) : P.lift x (lower j) = x j := by
  simp [lift, lower]

@[simp] theorem lift_upper (x : Fin n → ℝ) (j : Fin n) :
    P.lift x (upper j) = P.u j - x j := by
  simp only [lift, upper, Fin.append_right, Pi.sub_apply]

@[simp] theorem liftDir_lower (d : Fin n → ℝ) (j : Fin n) : liftDir d (lower j) = d j := by
  simp [liftDir, lower]

@[simp] theorem liftDir_upper (d : Fin n → ℝ) (j : Fin n) : liftDir d (upper j) = -d j := by
  simp only [liftDir, upper, Fin.append_right, Pi.neg_apply]

theorem standard_mulVec_lower (z : Fin (n + n) → ℝ) (i : Fin m) :
    (P.standard.A *ᵥ z) (Fin.castAdd n i) = (P.A *ᵥ fun j ↦ z (lower j)) i := by
  simp [standard, mulVec, dotProduct, Fin.sum_univ_add, lower, -Fin.natAdd_eq_addNat]

theorem standard_mulVec_upper (z : Fin (n + n) → ℝ) (j : Fin n) :
    (P.standard.A *ᵥ z) (Fin.natAdd m j) = z (lower j) + z (upper j) := by
  simp [standard, mulVec, dotProduct, Fin.sum_univ_add, lower, upper,
    -Fin.natAdd_eq_addNat]

theorem standard_mulVec_eq_b_iff (z : Fin (n + n) → ℝ) :
    P.standard.A *ᵥ z = P.standard.b ↔
      P.A *ᵥ (fun j ↦ z (lower j)) = P.b ∧ ∀ j, z (lower j) + z (upper j) = P.u j := by
  constructor
  · intro h
    refine ⟨funext fun i ↦ ?_, fun j ↦ ?_⟩
    · have hi := congrFun h (Fin.castAdd n i)
      rw [standard_mulVec_lower] at hi
      simpa only [standard, Fin.append_left] using hi
    · have hj := congrFun h (Fin.natAdd m j)
      rw [standard_mulVec_upper] at hj
      simpa only [standard, Fin.append_right] using hj
  · rintro ⟨hA, hcap⟩
    funext r
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) r
    · rw [standard_mulVec_lower]
      simpa only [standard, Fin.append_left] using congrFun hA i
    · rw [standard_mulVec_upper]
      simpa only [standard, Fin.append_right] using hcap j

theorem standard_mulVec_eq_zero_iff (z : Fin (n + n) → ℝ) :
    P.standard.A *ᵥ z = 0 ↔
      P.A *ᵥ (fun j ↦ z (lower j)) = 0 ∧ ∀ j, z (lower j) + z (upper j) = 0 := by
  constructor
  · intro h
    refine ⟨funext fun i ↦ ?_, fun j ↦ ?_⟩
    · simpa [standard_mulVec_lower] using congrFun h (Fin.castAdd n i)
    · simpa [standard_mulVec_upper] using congrFun h (Fin.natAdd m j)
  · rintro ⟨hA, hcap⟩
    funext r
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) r
    · simpa [standard_mulVec_lower] using congrFun hA i
    · simpa [standard_mulVec_upper] using hcap j

/-- Adding capacity slacks is an exact equivalence of feasible points. -/
theorem lift_feasible_iff (x : Fin n → ℝ) : P.standard.IsFeasible (P.lift x) ↔ P.IsFeasible x := by
  rw [LP.IsFeasible, standard_mulVec_eq_b_iff]
  constructor
  · rintro ⟨⟨hA, -⟩, hnonneg⟩
    refine ⟨by simpa using hA, fun j ↦ ⟨?_, ?_⟩⟩
    · simpa using hnonneg (lower j)
    · have := hnonneg (upper j)
      simp only [lift_upper] at this
      linarith
  · rintro ⟨hA, hx⟩
    refine ⟨⟨by simpa using hA, by intro j; simp⟩, fun l ↦ ?_⟩
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) l
    · change 0 ≤ P.lift x (lower j)
      rw [lift_lower]
      exact (hx j).1
    · change 0 ≤ P.lift x (upper j)
      rw [lift_upper]
      exact sub_nonneg.mpr (hx j).2

theorem basis_card (hT : P.toLP.IsBasis S.tree) (hTU : Disjoint S.tree S.atUpper) :
    S.basis.card = m + n := by
  have hd : Disjoint ((univ \ (S.tree ∪ S.atUpper)).map (Fin.castAddEmb n))
      (S.atUpper.map (Fin.natAddEmb n)) := by
    rw [Finset.disjoint_left]
    intro l hl hu
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hl
    obtain ⟨j, -, hj⟩ := Finset.mem_map.mp hu
    exact upper_ne_lower j i (by simpa [lower, upper] using hj)
  have hTUcard : S.tree.card + S.atUpper.card ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ (S.tree ∪ S.atUpper))
    simpa [Finset.card_union_of_disjoint hTU] using h
  have ha : S.activeBounds.card = n - (S.tree.card + S.atUpper.card) + S.atUpper.card := by
    simp only [State.activeBounds, Finset.card_union_of_disjoint hd, Finset.card_map,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, Finset.card_union_of_disjoint hTU]
  rw [State.basis, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, ha]
  have := hT.1
  omega

/-- The forest basis extends to the exact standard-form basis in the paper. -/
theorem standard_isBasis (hT : P.toLP.IsBasis S.tree) (hTU : Disjoint S.tree S.atUpper) :
    P.standard.IsBasis S.basis := by
  refine ⟨basis_card P S hT hTU, (LP.linIndep_iff _ _).2 ?_⟩
  intro z hz hAz
  obtain ⟨hA, hsum⟩ := (standard_mulVec_eq_zero_iff P z).1 hAz
  have hzero : (fun j ↦ z (lower j)) = 0 := hT.eq_zero (fun j hj ↦ ?_) hA
  · funext l
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) l
    · exact congrFun hzero j
    · change z (upper j) = 0
      have h := hsum j
      have hzj : z (lower j) = 0 := congrFun hzero j
      rw [hzj, zero_add] at h
      exact h
  · by_cases hu : j ∈ S.atUpper
    · have hs : z (upper j) = 0 := hz _ (by simpa using hu)
      linarith [hsum j]
    · exact hz _ (by simp [hj, hu])

theorem standard_basicSol (hS : P.IsState S) :
    P.standard.basicSol S.basis = P.lift S.flow := by
  symm
  apply (standard_isBasis P S hS.1 hS.2.1).eq_basicSol
  · exact ((lift_feasible_iff P S.flow).2 hS.2.2.1).1
  · intro l hl
    revert hl
    refine Fin.addCases (fun j hl ↦ ?_) (fun j hl ↦ ?_) l
    · change lower j ∉ S.basis at hl
      have hj : j ∉ S.tree ∧ j ∉ S.atUpper := by
        simpa only [mem_basis_lower, not_or] using hl
      change P.lift S.flow (lower j) = 0
      rw [lift_lower, hS.2.2.2 j hj.1]
      simp only [ite_eq_right hj.2]
    · change upper j ∉ S.basis at hl
      have hu : j ∈ S.atUpper := by simpa only [mem_basis_upper, not_not] using hl
      have ht : j ∉ S.tree := fun ht ↦ Finset.disjoint_left.mp hS.2.1 ht hu
      change P.lift S.flow (upper j) = 0
      rw [lift_upper, hS.2.2.2 j ht]
      simp only [ite_eq_left hu, sub_self]

theorem standard_feasibleBasis (hS : P.IsState S) : P.standard.IsFeasibleBasis S.basis := by
  refine ⟨standard_isBasis P S hS.1 hS.2.1, ?_⟩
  rw [standard_basicSol P S hS]
  exact ((lift_feasible_iff P S.flow).2 hS.2.2.1).2

/-- Strictly interior tree flows and positive capacities give a nondegenerate
standard-form basis, including its non-tree basic variables. -/
theorem standard_nondegenerate (hS : P.IsState S) (hu : ∀ j, 0 < P.u j)
    (hnd : P.IsNondegenerate S) : P.standard.IsNondegenerate S.basis := by
  intro l hl
  rw [standard_basicSol P S hS]
  revert hl
  refine Fin.addCases (fun j hl ↦ ?_) (fun j hl ↦ ?_) l
  · change lower j ∈ S.basis at hl
    have hj := (mem_basis_lower S j).1 hl
    change 0 < P.lift S.flow (lower j)
    rw [lift_lower]
    rcases hj with ht | hj
    · exact (hnd j ht).1
    · have ht : j ∉ S.tree := fun ht ↦ Finset.disjoint_left.mp hS.2.1 ht hj
      simpa only [hS.2.2.2 j ht, ite_eq_left hj] using hu j
  · change upper j ∈ S.basis at hl
    have hj := (mem_basis_upper S j).1 hl
    change 0 < P.lift S.flow (upper j)
    rw [lift_upper]
    by_cases ht : j ∈ S.tree
    · exact sub_pos.mpr (hnd j ht).2
    · simpa only [hS.2.2.2 j ht, ite_eq_right hj, sub_zero] using hu j

theorem entering_not_mem_basis (j : Fin n) (hj : j ∉ S.tree) : S.entering j ∉ S.basis := by
  by_cases hu : j ∈ S.atUpper <;> simp [State.entering, hu, hj]

theorem nonbasic_label (hTU : Disjoint S.tree S.atUpper) (l : Fin (n + n))
    (hl : l ∉ S.basis) : ∃ j, j ∉ S.tree ∧ l = S.entering j := by
  revert hl
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) l
  · intro hl
    change lower j ∉ S.basis at hl
    have hj : j ∉ S.tree ∧ j ∉ S.atUpper := by
      simpa only [mem_basis_lower, not_or] using hl
    exact ⟨j, hj.1, by simp [State.entering, hj.2, lower]⟩
  · intro hl
    change upper j ∉ S.basis at hl
    have hu : j ∈ S.atUpper := by simpa only [mem_basis_upper, not_not] using hl
    exact ⟨j, fun ht ↦ Finset.disjoint_left.mp hTU ht hu,
      by simp [State.entering, hu, upper]⟩

theorem direction_null (hT : P.toLP.IsBasis S.tree) (j : Fin n) (hj : j ∉ S.tree) :
    P.A *ᵥ P.direction S j = 0 := by
  change P.toLP.A *ᵥ P.direction S j = 0
  rw [direction, mulVec_smul, (hT.basicDir_spec hj).1, smul_zero]

theorem direction_j (hT : P.toLP.IsBasis S.tree) (j : Fin n) (hj : j ∉ S.tree) :
    P.direction S j j = sign S j := by
  simp [direction, (hT.basicDir_spec hj).2.1]

theorem direction_off_tree (hT : P.toLP.IsBasis S.tree) (j : Fin n) (hj : j ∉ S.tree)
    (k : Fin n) (hk : k ∉ S.tree) (hkj : k ≠ j) : P.direction S j k = 0 := by
  simp [direction, (hT.basicDir_spec hj).2.2 k hk hkj]

theorem liftDir_entering (hT : P.toLP.IsBasis S.tree) (j : Fin n) (hj : j ∉ S.tree) :
    liftDir (P.direction S j) (S.entering j) = 1 := by
  by_cases hu : j ∈ S.atUpper <;>
    simp [State.entering, hu, direction_j P S hT j hj, sign]

theorem liftDir_off_basis (hS : P.IsState S) (j : Fin n) (hj : j ∉ S.tree)
    (l : Fin (n + n)) (hl : l ∉ S.basis) (hle : l ≠ S.entering j) :
    liftDir (P.direction S j) l = 0 := by
  obtain ⟨k, hk, rfl⟩ := nonbasic_label S hS.2.1 l hl
  have hkj : k ≠ j := fun h ↦ hle (by rw [h])
  by_cases hu : k ∈ S.atUpper <;>
    simp [State.entering, hu, direction_off_tree P S hS.1 j hj k hk hkj]

/-- A fundamental network direction becomes the ordinary basic direction,
with sign reversed when the entering arc starts at capacity. -/
theorem standard_basicDir (hS : P.IsState S) (j : Fin n) (hj : j ∉ S.tree) :
    P.standard.basicDir S.basis (S.entering j) = liftDir (P.direction S j) := by
  symm
  apply (standard_isBasis P S hS.1 hS.2.1).eq_basicDir (entering_not_mem_basis S j hj)
  refine ⟨?_, liftDir_entering P S hS.1 j hj, fun l hl hle ↦ ?_⟩
  · rw [standard_mulVec_eq_zero_iff]
    exact ⟨by simpa using direction_null P S hS.1 j hj, by intro k; simp⟩
  · exact liftDir_off_basis P S hS j hj l hl hle

theorem standard_cost (z : Fin (n + n) → ℝ) :
    P.standard.c ⬝ᵥ z = P.c ⬝ᵥ (fun j ↦ z (lower j)) := by
  simp [standard, dotProduct, Fin.sum_univ_add, lower, -Fin.natAdd_eq_addNat]

/-- In particular, an upper arc's entering capacity slack has the negated
reduced cost of the original arc. -/
theorem standard_reducedCost (hS : P.IsState S) (j : Fin n) (hj : j ∉ S.tree) :
    P.standard.reducedCost S.basis (S.entering j) = P.reducedCost S j := by
  rw [← (standard_isBasis P S hS.1 hS.2.1).cost_basicDir (entering_not_mem_basis S j hj),
    standard_basicDir P S hS j hj, standard_cost]
  simp only [liftDir_lower]
  change P.toLP.c ⬝ᵥ P.direction S j = P.reducedCost S j
  rw [direction, dotProduct_smul, hS.1.cost_basicDir hj, smul_eq_mul]
  rfl

theorem standard_improving_iff (hS : P.IsState S) (l : Fin (n + n)) :
    l ∈ P.standard.improving S.basis ↔ ∃ j, P.IsImproving S j ∧ l = S.entering j := by
  constructor
  · intro hl
    have hn := (standard_isBasis P S hS.1 hS.2.1).not_mem_of_mem_improving hl
    obtain ⟨j, hj, rfl⟩ := nonbasic_label S hS.2.1 l hn
    refine ⟨j, ⟨hj, ?_⟩, rfl⟩
    have hr : P.standard.reducedCost S.basis (S.entering j) < 0 := by
      simpa [LP.improving] using hl
    rwa [standard_reducedCost P S hS j hj] at hr
  · rintro ⟨j, ⟨hj, hr⟩, rfl⟩
    simpa [LP.improving, standard_reducedCost P S hS j hj] using hr

theorem oriented_cost_eq_neg_abs (j : Fin n) (hj : P.IsImproving S j) :
    P.reducedCost S j = -|P.toLP.reducedCost S.tree j| := by
  have hr := hj.2
  by_cases hu : j ∈ S.atUpper
  · simp only [reducedCost, sign, ite_eq_left hu, neg_one_mul, neg_lt_zero] at hr ⊢
    rw [abs_of_pos hr]
  · simp only [reducedCost, sign, ite_eq_right hu, one_mul] at hr ⊢
    rw [abs_of_neg hr]
    ring

/-- Greatest absolute improving network cost is exactly Dantzig's minimum
standard-form reduced cost. All tied choices are preserved. -/
theorem standard_dantzig_iff (hS : P.IsState S) (j : Fin n) :
    P.standard.IsDantzigChoice S.basis (S.entering j) ↔ P.IsDantzigChoice S j := by
  have hinj : Function.Injective S.entering := by
    intro a b h
    by_cases ha : a ∈ S.atUpper <;> by_cases hb : b ∈ S.atUpper <;>
      simp_all [State.entering]
  constructor
  · rintro ⟨himp, hmin⟩
    obtain ⟨i, hi, heq⟩ := (standard_improving_iff P S hS _).1 himp
    have hij : j = i := hinj heq
    subst i
    refine ⟨hi, fun k hk ↦ ?_⟩
    have h := hmin (S.entering k) ((standard_improving_iff P S hS _).2 ⟨k, hk, rfl⟩)
    rw [standard_reducedCost P S hS j hi.1, standard_reducedCost P S hS k hk.1,
      oriented_cost_eq_neg_abs P S j hi, oriented_cost_eq_neg_abs P S k hk] at h
    linarith
  · rintro ⟨hj, hmax⟩
    refine ⟨(standard_improving_iff P S hS _).2 ⟨j, hj, rfl⟩, fun l hl ↦ ?_⟩
    obtain ⟨k, hk, rfl⟩ := (standard_improving_iff P S hS _).1 hl
    rw [standard_reducedCost P S hS j hj.1, standard_reducedCost P S hS k hk.1,
      oriented_cost_eq_neg_abs P S j hj, oriented_cost_eq_neg_abs P S k hk]
    linarith [hmax k hk]

theorem standard_isLeavingLabel_iff (hS : P.IsState S) (j : Fin n) (hj : j ∉ S.tree)
    (l : Fin (n + n)) :
    P.standard.IsLeavingLabel S.basis (S.entering j) l ↔ P.IsLeavingBound S j l := by
  have hm : ∀ k, liftDir (P.direction S j) k < 0 → k ∈ S.basis := by
    intro k hk
    by_contra hkn
    have hn := (standard_isBasis P S hS.1 hS.2.1).basicDir_nonneg_of_not_mem
      (entering_not_mem_basis S j hj) hkn
    rw [standard_basicDir P S hS j hj] at hn
    linarith
  rw [LP.IsLeavingLabel, standard_basicSol P S hS, standard_basicDir P S hS j hj]
  constructor
  · rintro ⟨-, hl, hmin⟩
    exact ⟨hl, fun k hk ↦ hmin k (hm k hk) hk⟩
  · rintro ⟨hl, hmin⟩
    exact ⟨hm l hl, hl, fun k _ hk ↦ hmin k hk⟩

/-- The exchange of active bounds becomes the exchange of standard-form
basic variables, including an entering arc that flips to its opposite bound. -/
theorem basis_exchange {S' : State n} {e l : Fin (n + n)}
    (he : e ∉ S.basis) (hl : l ∈ S.basis)
    (hactive : S'.activeBounds = insert l (S.activeBounds.erase e)) :
    S'.basis = insert e (S.basis.erase l) := by
  have heA : e ∈ S.activeBounds := by simpa [State.basis] using he
  have hlA : l ∉ S.activeBounds := by simpa [State.basis] using hl
  ext k
  by_cases hke : k = e <;> by_cases hkl : k = l <;>
    simp_all [State.basis]

/-- Every bounded-variable network pivot is one ordinary simplex pivot. -/
theorem standard_pivot (hS : P.IsState S) (j : Fin n) (S' : State n)
    (hp : P.IsPivot S j S') :
    P.standard.IsPivot S.basis (S.entering j) S'.basis := by
  obtain ⟨hj, l, hl, hactive, -⟩ := hp
  have hl' := (standard_isLeavingLabel_iff P S hS j hj.1 l).2 hl
  exact ⟨standard_feasibleBasis P S hS,
    (standard_improving_iff P S hS _).2 ⟨j, hj, rfl⟩,
    entering_not_mem_basis S j hj.1, l, hl', basis_exchange S
      (entering_not_mem_basis S j hj.1) hl'.1 hactive⟩

/-- The complete network run, terminal condition and exact pivot count survive
the capacity-slack conversion. -/
theorem standard_run (f : ℕ) (R : ℕ → State n) (hR : P.IsDantzigRun f R) :
    P.standard.IsSimplexRunWith P.standard.IsDantzigChoice f (fun k ↦ (R k).basis) := by
  refine ⟨⟨fun k hk ↦ standard_feasibleBasis P (R k) (hR.1 k hk), fun k hk ↦ ?_⟩, ?_⟩
  · obtain ⟨j, hchoice, hp⟩ := hR.2.1 k hk
    exact ⟨(R k).entering j, (standard_dantzig_iff P (R k) (hR.1 k hk.le) j).2 hchoice,
      standard_pivot P (R k) (hR.1 k hk.le) j (R (k + 1)) hp⟩
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    obtain ⟨j, hj, -⟩ := (standard_improving_iff P (R f) (hR.1 f le_rfl) l).1 hl
    exact hR.2.2 j hj

theorem standard_unique (hS : P.IsState S)
    (hunique : ∀ j k, P.IsDantzigChoice S j → P.IsDantzigChoice S k → j = k) :
    ∀ a b, P.standard.IsDantzigChoice S.basis a →
      P.standard.IsDantzigChoice S.basis b → a = b := by
  intro a b ha hb
  obtain ⟨j, -, rfl⟩ := (standard_improving_iff P S hS a).1 ha.1
  obtain ⟨k, -, rfl⟩ := (standard_improving_iff P S hS b).1 hb.1
  exact congrArg S.entering (hunique j k ((standard_dantzig_iff P S hS j).1 ha)
    ((standard_dantzig_iff P S hS k).1 hb))

end WolfeSimplex.BoundedLP

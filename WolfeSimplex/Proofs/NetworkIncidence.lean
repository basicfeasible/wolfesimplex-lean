import WolfeSimplex.Proofs.NetworkFlow

/-!
# Network conservation and spanning-forest bases

Arcs are indexed independently of their endpoints, so parallel arcs are allowed.
One root is removed in each component. A forest is certified combinatorially by
its fundamental cuts and edge count, not by assuming linear independence of its
incidence columns. This file proves that independence and the row-deletion step.
-/

namespace WolfeSimplex

open Finset Matrix

structure FlowNetwork (v n : ℕ) where
  tail : Fin n → Fin v
  head : Fin n → Fin v
  supply : Fin v → ℝ
  cost : Fin n → ℝ
  capacity : Fin n → ℝ

namespace FlowNetwork

variable {v n m c : ℕ} (N : FlowNetwork v n)

def incidence : Matrix (Fin v) (Fin n) ℝ :=
  fun w e ↦ (if N.head e = w then 1 else 0) - (if N.tail e = w then 1 else 0)

def IsFeasible (x : Fin n → ℝ) : Prop :=
  N.incidence *ᵥ x = N.supply ∧ ∀ e, 0 ≤ x e ∧ x e ≤ N.capacity e

/-- A component partition, one root per component, and an enumeration of the
remaining vertices. No linear-algebraic rank property is assumed. -/
structure RowDeletion (m c : ℕ) where
  component : Fin v → Fin c
  root : Fin c → Fin v
  root_component : ∀ k, component (root k) = k
  arc_component : ∀ e, component (N.head e) = component (N.tail e)
  rows : Fin m ≃ {w : Fin v // w ≠ root (component w)}

variable {N} (D : N.RowDeletion m c)

def RowDeletion.vertices (k : Fin c) : Finset (Fin v) :=
  univ.filter (fun w ↦ D.component w = k)

def RowDeletion.Balanced : Prop :=
  ∀ k, ∑ w ∈ D.vertices k, N.supply w = 0

def RowDeletion.bounded : BoundedLP m n where
  A := fun i e ↦ N.incidence (D.rows i).val e
  b := fun i ↦ N.supply (D.rows i).val
  c := N.cost
  u := N.capacity

theorem cut_column (C : Finset (Fin v)) (e : Fin n) :
    ∑ w ∈ C, N.incidence w e =
      (if N.head e ∈ C then 1 else 0) - (if N.tail e ∈ C then 1 else 0) := by
  simp [incidence, Finset.sum_sub_distrib, eq_comm]

theorem cut_flow (C : Finset (Fin v)) (x : Fin n → ℝ) :
    ∑ w ∈ C, (N.incidence *ᵥ x) w =
      ∑ e, ((if N.head e ∈ C then 1 else 0) -
        (if N.tail e ∈ C then 1 else 0)) * x e := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_mul, cut_column]

theorem RowDeletion.component_flow_zero (x : Fin n → ℝ) (k : Fin c) :
    ∑ w ∈ D.vertices k, (N.incidence *ᵥ x) w = 0 := by
  rw [cut_flow]
  apply Finset.sum_eq_zero
  intro e _
  simp [RowDeletion.vertices, D.arc_component e]

/-- A function with zero values off the roots and zero component sums vanishes. -/
theorem RowDeletion.eq_zero_of_nonroot (r : Fin v → ℝ)
    (hn : ∀ w, w ≠ D.root (D.component w) → r w = 0)
    (hs : ∀ k, ∑ w ∈ D.vertices k, r w = 0) : r = 0 := by
  funext w
  by_cases hw : w ≠ D.root (D.component w)
  · exact hn w hw
  · have he : w = D.root (D.component w) := not_ne_iff.mp hw
    let k := D.component w
    have hsum : ∑ a ∈ D.vertices k, r a = r (D.root k) := by
      apply Finset.sum_eq_single (D.root k)
      · intro a ha hne
        have hc : D.component a = k := (Finset.mem_filter.mp ha).2
        apply hn a
        simpa only [hc] using hne
      · simp [RowDeletion.vertices, D.root_component]
    have hz := (hsum.symm.trans (hs k))
    exact (congrArg r he).trans hz

theorem RowDeletion.mulVec_eq_iff (x : Fin n → ℝ) (hb : D.Balanced) :
    D.bounded.A *ᵥ x = D.bounded.b ↔ N.incidence *ᵥ x = N.supply := by
  constructor
  · intro h
    have hz : (N.incidence *ᵥ x) - N.supply = 0 := by
      apply D.eq_zero_of_nonroot
      · intro w hw
        let i := D.rows.symm ⟨w, hw⟩
        have hi : D.rows i = ⟨w, hw⟩ := D.rows.apply_symm_apply _
        have he := congrFun h i
        change (N.incidence *ᵥ x) (D.rows i).val = N.supply (D.rows i).val at he
        rw [hi] at he
        exact sub_eq_zero.mpr he
      · intro k
        simp only [Pi.sub_apply, Finset.sum_sub_distrib,
          RowDeletion.component_flow_zero, hb k, sub_self]
    exact sub_eq_zero.mp hz
  · intro h
    funext i
    exact congrFun h (D.rows i).val

theorem RowDeletion.feasible_iff (x : Fin n → ℝ) (hb : D.Balanced) :
    D.bounded.IsFeasible x ↔ N.IsFeasible x := by
  unfold BoundedLP.IsFeasible IsFeasible
  rw [D.mulVec_eq_iff x hb]
  rfl

/-- A combinatorial fundamental-cut certificate for a spanning forest.
Each tree arc crosses its cut, every other tree arc stays on one side, and no
root belongs to a cut. The edge count is the number of non-root vertices. -/
structure RowDeletion.ForestCertificate (T : Finset (Fin n)) where
  card : T.card = m
  cut : T → Finset (Fin v)
  no_root : ∀ e k, D.root k ∉ cut e
  separates : ∀ e : T,
    (N.head e ∈ cut e ∧ N.tail e ∉ cut e) ∨
      (N.head e ∉ cut e ∧ N.tail e ∈ cut e)
  others : ∀ (e f : T), f ≠ e → (N.head f ∈ cut e ↔ N.tail f ∈ cut e)

theorem RowDeletion.forest_isBasis {T : Finset (Fin n)} (F : D.ForestCertificate T) :
    D.bounded.toLP.IsBasis T := by
  refine ⟨F.card, (LP.linIndep_iff _ _).2 ?_⟩
  intro x hx hAx
  funext e
  by_cases he : e ∈ T
  · let a : T := ⟨e, he⟩
    let C := F.cut a
    have hzero : ∑ w ∈ C, (N.incidence *ᵥ x) w = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      have hn : w ≠ D.root (D.component w) := by
        intro h
        exact F.no_root a (D.component w) (h ▸ hw)
      let i := D.rows.symm ⟨w, hn⟩
      have hi : D.rows i = ⟨w, hn⟩ := D.rows.apply_symm_apply _
      have h := congrFun hAx i
      change (N.incidence *ᵥ x) (D.rows i).val = 0 at h
      rw [hi] at h
      exact h
    rw [cut_flow] at hzero
    have hsingle : (∑ f, ((if N.head f ∈ C then 1 else 0) -
        (if N.tail f ∈ C then 1 else 0)) * x f) =
        ((if N.head e ∈ C then 1 else 0) -
          (if N.tail e ∈ C then 1 else 0)) * x e := by
      apply Finset.sum_eq_single e
      · intro f _ hfe
        by_cases hf : f ∈ T
        · have hmem := F.others a ⟨f, hf⟩ (fun h ↦ hfe (congrArg Subtype.val h))
          simp only [C, hmem, sub_self, zero_mul]
        · simp only [hx f hf, mul_zero]
      · simp
    rw [hsingle] at hzero
    have hnonzero : ((if N.head e ∈ C then (1 : ℝ) else 0) -
        (if N.tail e ∈ C then 1 else 0)) ≠ 0 := by
      rcases F.separates a with ⟨hh, ht⟩ | ⟨hh, ht⟩
      · change N.head e ∈ C at hh
        change N.tail e ∉ C at ht
        simp [hh, ht]
      · change N.head e ∉ C at hh
        change N.tail e ∈ C at ht
        simp [hh, ht]
    exact (mul_eq_zero.mp hzero).resolve_left hnonzero
  · exact hx e he

/-- A genuine network state uses full conservation and a combinatorial forest. -/
def RowDeletion.IsState (S : BoundedLP.State n) : Prop :=
  Nonempty (D.ForestCertificate S.tree) ∧ Disjoint S.tree S.atUpper ∧
    N.IsFeasible S.flow ∧
      ∀ e ∉ S.tree, S.flow e = if e ∈ S.atUpper then N.capacity e else 0

theorem RowDeletion.state_to_bounded (S : BoundedLP.State n) (hb : D.Balanced)
    (hS : D.IsState S) : D.bounded.IsState S := by
  obtain ⟨F⟩ := hS.1
  exact ⟨D.forest_isBasis F, hS.2.1, (D.feasible_iff S.flow hb).2 hS.2.2.1,
    hS.2.2.2⟩

/-- The fundamental cycle is characterized on the full incidence matrix,
independently of any reduced LP or standard-form basis. -/
def IsFundamental (T : Finset (Fin n)) (j : Fin n) (d : Fin n → ℝ) : Prop :=
  N.incidence *ᵥ d = 0 ∧ d j = 1 ∧ ∀ e ∉ T, e ≠ j → d e = 0

theorem RowDeletion.full_null_iff (d : Fin n → ℝ) :
    D.bounded.A *ᵥ d = 0 ↔ N.incidence *ᵥ d = 0 := by
  constructor
  · intro h
    apply D.eq_zero_of_nonroot
    · intro w hw
      let i := D.rows.symm ⟨w, hw⟩
      have hi : D.rows i = ⟨w, hw⟩ := D.rows.apply_symm_apply _
      have he := congrFun h i
      change (N.incidence *ᵥ d) (D.rows i).val = 0 at he
      rwa [hi] at he
    · exact D.component_flow_zero d
  · intro h
    funext i
    exact congrFun h (D.rows i).val

theorem RowDeletion.fundamental_exists {T : Finset (Fin n)}
    (F : D.ForestCertificate T) (j : Fin n) (hj : j ∉ T) :
    ∃ d, N.IsFundamental T j d := by
  have hd := (D.forest_isBasis F).basicDir_spec hj
  exact ⟨D.bounded.toLP.basicDir T j, (D.full_null_iff _).1 hd.1, hd.2⟩

noncomputable def fundamental (T : Finset (Fin n)) (j : Fin n) : Fin n → ℝ :=
  Classical.epsilon (N.IsFundamental T j)

theorem RowDeletion.fundamental_eq {T : Finset (Fin n)}
    (F : D.ForestCertificate T) (j : Fin n) (hj : j ∉ T) :
    N.fundamental T j = D.bounded.toLP.basicDir T j := by
  have hd := Classical.epsilon_spec (D.fundamental_exists F j hj)
  exact (D.forest_isBasis F).eq_basicDir hj ⟨(D.full_null_iff _).2 hd.1, hd.2⟩

/-- The signed cost of one unit around the fundamental cycle. -/
noncomputable def cycleCost (T : Finset (Fin n)) (j : Fin n) : ℝ :=
  N.cost ⬝ᵥ N.fundamental T j

theorem RowDeletion.cycleCost_eq {T : Finset (Fin n)}
    (F : D.ForestCertificate T) (j : Fin n) (hj : j ∉ T) :
    N.cycleCost T j = D.bounded.toLP.reducedCost T j := by
  unfold cycleCost
  rw [D.fundamental_eq F j hj]
  exact (D.forest_isBasis F).cost_basicDir hj

noncomputable def orientedDirection (S : BoundedLP.State n) (j : Fin n) : Fin n → ℝ :=
  BoundedLP.sign S j • N.fundamental S.tree j

noncomputable def IsImproving (S : BoundedLP.State n) (j : Fin n) : Prop :=
  j ∉ S.tree ∧ BoundedLP.sign S j * N.cycleCost S.tree j < 0

noncomputable def IsDantzigChoice (S : BoundedLP.State n) (j : Fin n) : Prop :=
  N.IsImproving S j ∧ ∀ k, N.IsImproving S k →
    |N.cycleCost S.tree k| ≤ |N.cycleCost S.tree j|

theorem RowDeletion.improving_iff (S : BoundedLP.State n) (hS : D.IsState S) (j : Fin n) :
    N.IsImproving S j ↔ D.bounded.IsImproving S j := by
  obtain ⟨F⟩ := hS.1
  constructor <;> rintro ⟨hj, hc⟩ <;> refine ⟨hj, ?_⟩
  · simpa only [D.cycleCost_eq F j hj, BoundedLP.reducedCost] using hc
  · simpa only [D.cycleCost_eq F j hj, BoundedLP.reducedCost] using hc

theorem RowDeletion.dantzig_iff (S : BoundedLP.State n) (hS : D.IsState S) (j : Fin n) :
    N.IsDantzigChoice S j ↔ D.bounded.IsDantzigChoice S j := by
  obtain ⟨F⟩ := hS.1
  constructor
  · rintro ⟨hj, hmin⟩
    refine ⟨(D.improving_iff S hS j).1 hj, fun k hk ↦ ?_⟩
    have hk' := (D.improving_iff S hS k).2 hk
    simpa only [D.cycleCost_eq F k hk'.1, D.cycleCost_eq F j hj.1] using hmin k hk'
  · rintro ⟨hj, hmin⟩
    refine ⟨(D.improving_iff S hS j).2 hj, fun k hk ↦ ?_⟩
    have hk' := (D.improving_iff S hS k).1 hk
    simpa only [D.cycleCost_eq F k hk.1, D.cycleCost_eq F j hj.1] using hmin k hk'

def residual (x : Fin n → ℝ) : Fin (n + n) → ℝ :=
  Fin.append x (N.capacity - x)

def IsLeavingBound (x d : Fin n → ℝ) (l : Fin (n + n)) : Prop :=
  BoundedLP.liftDir d l < 0 ∧ ∀ k, BoundedLP.liftDir d k < 0 →
    N.residual x l / (-BoundedLP.liftDir d l) ≤
      N.residual x k / (-BoundedLP.liftDir d k)

/-- The network algorithm augments its fundamental circulation and exchanges
active bounds. This definition includes a bound flip on the entering arc. -/
noncomputable def IsPivot (S : BoundedLP.State n) (j : Fin n)
    (S' : BoundedLP.State n) : Prop :=
  N.IsImproving S j ∧ ∃ l,
    N.IsLeavingBound S.flow (N.orientedDirection S j) l ∧
    S'.activeBounds = insert l (S.activeBounds.erase (S.entering j)) ∧
    S'.flow = S.flow +
      (N.residual S.flow l / (-BoundedLP.liftDir (N.orientedDirection S j) l)) •
        N.orientedDirection S j

noncomputable def RowDeletion.IsDantzigRun (f : ℕ) (R : ℕ → BoundedLP.State n) : Prop :=
  (∀ k ≤ f, D.IsState (R k)) ∧
    (∀ k < f, ∃ j, N.IsDantzigChoice (R k) j ∧ N.IsPivot (R k) j (R (k + 1))) ∧
    ∀ j, ¬ N.IsImproving (R f) j

theorem RowDeletion.orientedDirection_eq (S : BoundedLP.State n) (hS : D.IsState S)
    (j : Fin n) (hj : j ∉ S.tree) :
    N.orientedDirection S j = D.bounded.direction S j := by
  obtain ⟨F⟩ := hS.1
  unfold orientedDirection BoundedLP.direction
  rw [D.fundamental_eq F j hj]

theorem RowDeletion.pivot_to_bounded (S S' : BoundedLP.State n) (hS : D.IsState S)
    (j : Fin n) (hp : N.IsPivot S j S') : D.bounded.IsPivot S j S' := by
  obtain ⟨hj, l, hl, ha, hx⟩ := hp
  have hd := D.orientedDirection_eq S hS j hj.1
  refine ⟨(D.improving_iff S hS j).1 hj, l, ?_, ha, ?_⟩
  · change D.bounded.IsLeavingBound S j l
    simpa only [BoundedLP.IsLeavingBound, IsLeavingBound, hd,
      BoundedLP.lift, RowDeletion.bounded, residual] using hl
  · simpa only [hd, BoundedLP.lift, RowDeletion.bounded, residual] using hx

/-- The full network algorithm, not an assumed LP pivot correspondence, gives
the bounded-variable run used by the capacity-slack theorem. -/
theorem RowDeletion.run_to_bounded (f : ℕ) (R : ℕ → BoundedLP.State n)
    (hb : D.Balanced) (hR : D.IsDantzigRun f R) :
    D.bounded.IsDantzigRun f R := by
  refine ⟨fun k hk ↦ D.state_to_bounded (R k) hb (hR.1 k hk), ?_, ?_⟩
  · intro k hk
    obtain ⟨j, hj, hp⟩ := hR.2.1 k hk
    exact ⟨j, (D.dantzig_iff (R k) (hR.1 k hk.le) j).1 hj,
      D.pivot_to_bounded (R k) (R (k + 1)) (hR.1 k hk.le) j hp⟩
  · intro j hj
    exact hR.2.2 j ((D.improving_iff (R f) (hR.1 f le_rfl) j).2 hj)

theorem RowDeletion.standard_run (f : ℕ) (R : ℕ → BoundedLP.State n)
    (hb : D.Balanced) (hR : D.IsDantzigRun f R) :
    D.bounded.standard.IsSimplexRunWith D.bounded.standard.IsDantzigChoice f
      (fun k ↦ (R k).basis) :=
  BoundedLP.standard_run _ f R (D.run_to_bounded f R hb hR)

end FlowNetwork
end WolfeSimplex

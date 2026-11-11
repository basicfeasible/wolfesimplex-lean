import WolfeSimplex.Proofs.NetworkEncoding

/-! Native networks with explicitly absent upper bounds. An infinite-capacity
arc has no upper ratio-test candidate. At a one-way source/sink endpoint,
conservation bounds its flow; an input-computable finite replacement is strict.
The source run, its length and its largest encountered flow are not inputs to
the replacement. -/
namespace WolfeSimplex
open Finset Matrix

namespace FlowNetwork
variable {v n : ℕ} (N : FlowNetwork v n)

theorem flow_le_outward_supply (x : Fin n → ℝ)
    (hx : N.incidence *ᵥ x = N.supply) (hpos : ∀ a, 0 ≤ x a)
    (e : Fin n) (hout : ∀ a, N.head a ≠ N.tail e) :
    x e ≤ |N.supply (N.tail e)| := by
  have he := congrFun hx (N.tail e)
  have hs : (∑ a, if N.tail a = N.tail e then x a else 0) = -N.supply (N.tail e) := by
    simpa [incidence, mulVec, dotProduct, hout, ite_mul] using congrArg Neg.neg he
  have hm : x e ≤ ∑ a, if N.tail a = N.tail e then x a else 0 := by
    simpa using Finset.single_le_sum
      (f := fun a ↦ if N.tail a = N.tail e then x a else 0)
      (fun a _ ↦ by split_ifs; exact hpos a; exact le_rfl) (mem_univ e)
  rw [hs] at hm
  exact hm.trans (neg_le_abs _)

theorem flow_le_inward_supply (x : Fin n → ℝ)
    (hx : N.incidence *ᵥ x = N.supply) (hpos : ∀ a, 0 ≤ x a)
    (e : Fin n) (hin : ∀ a, N.tail a ≠ N.head e) :
    x e ≤ |N.supply (N.head e)| := by
  have he := congrFun hx (N.head e)
  have hs : (∑ a, if N.head a = N.head e then x a else 0) = N.supply (N.head e) := by
    simpa [incidence, mulVec, dotProduct, hin, ite_mul] using he
  have hm : x e ≤ ∑ a, if N.head a = N.head e then x a else 0 := by
    simpa using Finset.single_le_sum
      (f := fun a ↦ if N.head a = N.head e then x a else 0)
      (fun a _ ↦ by split_ifs; exact hpos a; exact le_rfl) (mem_univ e)
  rw [hs] at hm
  exact hm.trans (le_abs_self _)
end FlowNetwork

/-- `infinite` marks absent upper bounds; `data.capacity` on those arcs is an
ignored input placeholder. All finite capacities and all supplies/costs are
actual rationals, not existential real encodings. -/
structure ExtendedNetwork (v n : ℕ) where
  data : RationalNetwork v n
  infinite : Finset (Fin n)

namespace ExtendedNetwork
variable {v n m c : ℕ} (Q : ExtendedNetwork v n)

/-- Structural promise of DS18's five outer uncapacitated arcs. Each is at an
endpoint with only outgoing arcs or at one with only incoming arcs. -/
def Terminal : Prop := ∀ e ∈ Q.infinite,
  (∀ a, Q.data.head a ≠ Q.data.tail e) ∨ (∀ a, Q.data.tail a ≠ Q.data.head e)

def bound : ℕ := 1 + ∑ w, (Q.data.supply w).num.natAbs

def finite : RationalNetwork v n :=
  { Q.data with capacity := fun e ↦ if e ∈ Q.infinite then (Q.bound : ℚ) else Q.data.capacity e }

def IsFeasible (x : Fin n → ℝ) : Prop :=
  Q.data.toNetwork.incidence *ᵥ x = Q.data.toNetwork.supply ∧
    (∀ e, 0 ≤ x e) ∧ ∀ e ∉ Q.infinite, x e ≤ (Q.data.capacity e : ℝ)

theorem bound_pos : 0 < Q.bound := by unfold bound; omega

private theorem rat_abs_le_num (q : ℚ) : |(q : ℝ)| ≤ (q.num.natAbs : ℝ) := by
  rw [Rat.cast_def, abs_div,
    abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℝ) < q.den)]
  have hab : (q.num.natAbs : ℝ) = |(q.num : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hab]
  apply (div_le_iff₀ (by exact_mod_cast q.den_pos : (0 : ℝ) < q.den)).2
  have hd : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  nlinarith [abs_nonneg (q.num : ℝ)]

theorem supply_lt_bound (w : Fin v) : |(Q.data.supply w : ℝ)| < (Q.bound : ℝ) := by
  have hs : (Q.data.supply w).num.natAbs ≤ ∑ a, (Q.data.supply a).num.natAbs :=
    single_le_sum (f := fun a ↦ (Q.data.supply a).num.natAbs)
      (fun _ _ ↦ Nat.zero_le _) (mem_univ w)
  have hs' : ((Q.data.supply w).num.natAbs : ℝ) < Q.bound := by
    exact_mod_cast (by unfold bound; omega : (Q.data.supply w).num.natAbs < Q.bound)
  exact (rat_abs_le_num _).trans_lt hs'

theorem flow_lt_bound (hQ : Q.Terminal) (x : Fin n → ℝ)
    (hx : Q.data.toNetwork.incidence *ᵥ x = Q.data.toNetwork.supply)
    (hpos : ∀ a, 0 ≤ x a) (e : Fin n) (he : e ∈ Q.infinite) : x e < (Q.bound : ℝ) := by
  rcases hQ e he with h | h
  · exact (Q.data.toNetwork.flow_le_outward_supply x hx hpos e h).trans_lt
      (Q.supply_lt_bound _)
  · exact (Q.data.toNetwork.flow_le_inward_supply x hx hpos e h).trans_lt
      (Q.supply_lt_bound _)

theorem feasible_iff (hQ : Q.Terminal) (x : Fin n → ℝ) :
    Q.IsFeasible x ↔ Q.finite.toNetwork.IsFeasible x := by
  constructor
  · rintro ⟨hx, hp, hu⟩
    refine ⟨hx, fun e ↦ ⟨hp e, ?_⟩⟩
    by_cases he : e ∈ Q.infinite
    · simpa [finite, RationalNetwork.toNetwork, he] using (Q.flow_lt_bound hQ x hx hp e he).le
    · simpa [finite, RationalNetwork.toNetwork, he] using hu e he
  · rintro ⟨hx, hu⟩
    exact ⟨hx, fun e ↦ (hu e).1,
      fun e he ↦ by simpa [finite, RationalNetwork.toNetwork, he] using (hu e).2⟩

theorem finite_positive (hp : ∀ e ∉ Q.infinite, 0 < (Q.data.capacity e : ℝ)) :
    ∀ e, 0 < (Q.finite.capacity e : ℝ) := by
  intro e
  by_cases he : e ∈ Q.infinite
  · simpa [finite, he] using (Nat.cast_pos.mpr Q.bound_pos : (0 : ℝ) < Q.bound)
  · simpa [finite, he] using hp e he

variable (D : Q.data.toNetwork.RowDeletion m c)

def deletion : Q.finite.toNetwork.RowDeletion m c where
  component := D.component
  root := D.root
  root_component := D.root_component
  arc_component := D.arc_component
  rows := D.rows

theorem balanced (hb : D.Balanced) : (Q.deletion D).Balanced := hb

def IsState (S : BoundedLP.State n) : Prop :=
  Nonempty (D.ForestCertificate S.tree) ∧ Disjoint S.tree S.atUpper ∧
    Q.IsFeasible S.flow ∧ (∀ e ∈ S.atUpper, e ∉ Q.infinite) ∧
    ∀ e ∉ S.tree, S.flow e = if e ∈ S.atUpper then (Q.data.capacity e : ℝ) else 0

theorem state_to_finite (hQ : Q.Terminal) (S : BoundedLP.State n) (hS : Q.IsState D S) :
    (Q.deletion D).IsState S := by
  obtain ⟨F⟩ := hS.1
  let F' : (Q.deletion D).ForestCertificate S.tree :=
    { card := F.card
      cut := F.cut
      no_root := F.no_root
      separates := F.separates
      others := F.others }
  refine ⟨⟨F'⟩, hS.2.1,
    (Q.feasible_iff hQ _).1 hS.2.2.1, ?_⟩
  intro e he
  rw [hS.2.2.2.2 e he]
  by_cases hu : e ∈ S.atUpper
  · simp [hu, finite, RationalNetwork.toNetwork, hS.2.2.2.1 e hu]
  · simp [hu]

def IsNondegenerate (S : BoundedLP.State n) : Prop :=
  ∀ e ∈ S.tree, 0 < S.flow e ∧ (e ∉ Q.infinite → S.flow e < (Q.data.capacity e : ℝ))

theorem nondegenerate_to_finite (hQ : Q.Terminal) (S : BoundedLP.State n)
    (hS : Q.IsState D S) (hnd : Q.IsNondegenerate S) :
    ∀ e ∈ S.tree, 0 < S.flow e ∧ S.flow e < (Q.finite.capacity e : ℝ) := by
  intro e he
  refine ⟨(hnd e he).1, ?_⟩
  by_cases hi : e ∈ Q.infinite
  · simpa [finite, hi] using Q.flow_lt_bound hQ S.flow hS.2.2.1.1 hS.2.2.1.2.1 e hi
  · simpa [finite, hi] using (hnd e he).2 hi

/-- Lower bounds always exist. Only finite upper bounds enter the native
ratio test; the placeholder capacity of an uncapacitated arc is never read. -/
def HasBound (l : Fin (n + n)) : Prop :=
  Fin.addCases (fun _ ↦ True) (fun e ↦ e ∉ Q.infinite) l

@[simp] theorem hasBound_lower (e : Fin n) : Q.HasBound (BoundedLP.lower e) := by
  simp [HasBound, BoundedLP.lower, -Fin.natAdd_eq_addNat]

@[simp] theorem hasBound_upper (e : Fin n) :
    Q.HasBound (BoundedLP.upper e) ↔ e ∉ Q.infinite := by
  simp [HasBound, BoundedLP.upper, -Fin.natAdd_eq_addNat]

def IsLeavingBound (x d : Fin n → ℝ) (l : Fin (n + n)) : Prop :=
  Q.HasBound l ∧ BoundedLP.liftDir d l < 0 ∧ ∀ k, Q.HasBound k →
    BoundedLP.liftDir d k < 0 →
      Q.data.toNetwork.residual x l / (-BoundedLP.liftDir d l) ≤
        Q.data.toNetwork.residual x k / (-BoundedLP.liftDir d k)

noncomputable def IsPivot (S : BoundedLP.State n) (j : Fin n) (S' : BoundedLP.State n) : Prop :=
  Q.data.toNetwork.IsImproving S j ∧ ∃ l,
    Q.IsLeavingBound S.flow (Q.data.toNetwork.orientedDirection S j) l ∧
    S'.activeBounds = insert l (S.activeBounds.erase (S.entering j)) ∧
    S'.flow = S.flow + (Q.data.toNetwork.residual S.flow l /
      (-BoundedLP.liftDir (Q.data.toNetwork.orientedDirection S j) l)) •
        Q.data.toNetwork.orientedDirection S j

noncomputable def IsDantzigRun (f : ℕ) (R : ℕ → BoundedLP.State n) : Prop :=
  (∀ k ≤ f, Q.IsState D (R k)) ∧
    (∀ k < f, ∃ j, Q.data.toNetwork.IsDantzigChoice (R k) j ∧ Q.IsPivot (R k) j (R (k + 1))) ∧
    ∀ j, ¬ Q.data.toNetwork.IsImproving (R f) j

theorem residual_eq (x : Fin n → ℝ) (l : Fin (n + n)) (hl : Q.HasBound l) :
    Q.finite.toNetwork.residual x l = Q.data.toNetwork.residual x l := by
  refine Fin.addCases (fun e _ ↦ ?_) (fun e he ↦ ?_) l hl
  · simp [FlowNetwork.residual, -Fin.natAdd_eq_addNat]
  · have he : e ∉ Q.infinite := by
      simpa [HasBound, -Fin.natAdd_eq_addNat] using he
    simp [FlowNetwork.residual, finite, RationalNetwork.toNetwork, he,
      -Fin.natAdd_eq_addNat]

theorem pivot_to_finite (hQ : Q.Terminal) (S S' : BoundedLP.State n)
    (hS' : Q.IsState D S') (j : Fin n) (hp : Q.IsPivot S j S') :
    Q.finite.toNetwork.IsPivot S j S' := by
  obtain ⟨hj, l, ⟨hl, hn, hmin⟩, hact, hx⟩ := hp
  have hd : Q.finite.toNetwork.orientedDirection S j = Q.data.toNetwork.orientedDirection S j := rfl
  refine ⟨hj, l, ⟨?_, ?_⟩, hact, ?_⟩
  · simpa only [hd] using hn
  · intro k hk
    rw [hd, Q.residual_eq S.flow l hl]
    by_cases hb : Q.HasBound k
    · rw [Q.residual_eq S.flow k hb]
      exact hmin k hb (by simpa only [hd] using hk)
    · have hu : ∃ e, k = BoundedLP.upper e ∧ e ∈ Q.infinite := by
        revert hb
        refine Fin.addCases (fun e ↦ ?_) (fun e ↦ ?_) k
        · intro hb; exact (hb (Q.hasBound_lower e)).elim
        · intro hb
          exact ⟨e, rfl, not_not.mp (by
            simpa [HasBound, -Fin.natAdd_eq_addNat] using hb)⟩
      obtain ⟨e, rfl, he⟩ := hu
      have hlt := Q.flow_lt_bound hQ S'.flow hS'.2.2.1.1 hS'.2.2.1.2.1 e he
      have heq := congrFun hx e
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at heq
      have hdir : 0 < Q.data.toNetwork.orientedDirection S j e := by
        simpa only [hd, BoundedLP.liftDir_upper, neg_lt_zero] using hk
      have hres : Q.finite.toNetwork.residual S.flow (BoundedLP.upper e) =
          (Q.bound : ℝ) - S.flow e := by
        simp [FlowNetwork.residual, BoundedLP.upper, finite, RationalNetwork.toNetwork, he,
          -Fin.natAdd_eq_addNat]
      rw [hres, BoundedLP.liftDir_upper, neg_neg]
      apply (le_div_iff₀ hdir).2
      linarith
  · simpa only [hd, Q.residual_eq S.flow l hl] using hx

theorem run_to_finite (hQ : Q.Terminal) (f : ℕ) (R : ℕ → BoundedLP.State n)
    (hR : Q.IsDantzigRun D f R) : (Q.deletion D).IsDantzigRun f R := by
  refine ⟨fun k hk ↦ Q.state_to_finite D hQ _ (hR.1 k hk), ?_, hR.2.2⟩
  intro k hk
  obtain ⟨j, hj, hp⟩ := hR.2.1 k hk
  exact ⟨j, hj, Q.pivot_to_finite D hQ _ _ (hR.1 (k + 1) (by omega)) j hp⟩

end ExtendedNetwork
end WolfeSimplex

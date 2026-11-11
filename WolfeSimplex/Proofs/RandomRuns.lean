import WolfeSimplex.Defs.RandomRules
import WolfeSimplex.Proofs.RuleRuns

/-!
# Corollary 2 (`cor:intro-rules`): randomized rules (Random-Edge, Random-Bland)

The random and random-order insertion rules from `B̂₀` produce the same distribution of runs
as Random-Edge and Random-Bland from `B₀` (mapped by `B ↦ B̂`). A general transfer lemma
between LPs (`LP.randomEdge_transfer`, `LP.randomBland_transfer`) is also used for the cap
(Appendix C.2 (`app:cor-rules`) (cap argument)).
-/

namespace WolfeSimplex

open Finset Wolfe

variable {m n : ℕ}

/-! ### Helpers on `PMF` and `uniformOn` -/

lemma pmf_bind_congr_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a ↦ ?_
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ((PMF.mem_support_iff _ _).2 ha)]

lemma uniformOn_apply {α : Type*} [DecidableEq α] (s : Finset α) (h : s.Nonempty) (a : α) :
    uniformOn s h a = if a ∈ s then ((s.card : ENNReal))⁻¹ else 0 := rfl

lemma mem_of_mem_support_uniformOn {α : Type*} [DecidableEq α] {s : Finset α}
    {h : s.Nonempty} {a : α} (ha : a ∈ (uniformOn s h).support) : a ∈ s := by
  rw [PMF.mem_support_iff, uniformOn_apply] at ha
  by_contra h'
  simp [h'] at ha

/-- The pushforward of the uniform distribution on `s` under an embedding `e` is the
uniform distribution on `e(s)`. -/
lemma uniformOn_eq_map {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α)
    (hs : s.Nonempty) (e : α ↪ β) (t : Finset β) (ht : t.Nonempty) (hst : t = s.map e) :
    uniformOn t ht = (uniformOn s hs).map e := by
  subst hst
  ext b
  rw [PMF.map_apply, uniformOn_apply]
  by_cases hb : b ∈ s.map e
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hb
    rw [if_pos hb, tsum_eq_single a, if_pos rfl, uniformOn_apply, if_pos ha, Finset.card_map]
    intro a' ha'
    rw [if_neg]
    intro h'
    exact ha' (e.injective h').symm
  · rw [if_neg hb]
    symm
    refine ENNReal.tsum_eq_zero.2 fun a ↦ ?_
    split_ifs with h'
    · rw [uniformOn_apply, if_neg]
      intro ha
      exact hb (h' ▸ Finset.mem_map_of_mem e ha)
    · rfl

lemma uniformOn_univ_map_of_injective {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] [Nonempty α] [Nonempty β] (f : α → β) (hf : Function.Injective f)
    (hcard : Fintype.card α = Fintype.card β) :
    (uniformOn (univ : Finset α) univ_nonempty).map f =
      uniformOn (univ : Finset β) univ_nonempty := by
  refine (uniformOn_eq_map univ univ_nonempty ⟨f, hf⟩ univ univ_nonempty ?_).symm
  exact (Finset.eq_univ_of_card _ (by rw [card_map, card_univ, hcard])).symm

lemma uniformOn_univ_map_fst {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] [Nonempty α] [Nonempty β] :
    (uniformOn (univ : Finset (α × β)) univ_nonempty).map Prod.fst =
      uniformOn (univ : Finset α) univ_nonempty := by
  ext a
  rw [PMF.map_apply, uniformOn_apply, if_pos (mem_univ _), tsum_fintype]
  simp only [uniformOn_apply, mem_univ, if_true]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq, mem_univ, if_true, Finset.sum_const, card_univ,
    Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul]
  have hα : (Fintype.card α : ENNReal) ≠ 0 := by simp
  have hβ : (Fintype.card β : ENNReal) ≠ 0 := by simp
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [ENNReal.mul_inv (Or.inl hα) (Or.inl (ENNReal.natCast_ne_top _)),
    mul_comm ((Fintype.card α : ENNReal))⁻¹, ← mul_assoc,
    ENNReal.mul_inv_cancel hβ (ENNReal.natCast_ne_top _), one_mul]

/-- Binding the uniform distribution on `γ` against `F` equals binding the uniform
distribution on `α` against `G`, if `γ` is in bijection with `α × β` via `Φ` and
`F (Φ (a, b)) = G a`. -/
lemma uniformOn_bind_eq {α β γ X : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] [Nonempty α] [Nonempty β] [Nonempty γ]
    (Φ : α × β → γ) (hΦ : Function.Injective Φ) (hcard : Fintype.card (α × β) = Fintype.card γ)
    (F : γ → PMF X) (G : α → PMF X) (hFG : ∀ a b, F (Φ (a, b)) = G a) :
    (uniformOn (univ : Finset γ) univ_nonempty).bind F =
      (uniformOn (univ : Finset α) univ_nonempty).bind G := by
  rw [← uniformOn_univ_map_of_injective Φ hΦ hcard, PMF.bind_map,
    ← uniformOn_univ_map_fst (α := α) (β := β), PMF.bind_map]
  congr 1
  funext ⟨a, b⟩
  exact hFG a b

/-! ### `firstInOrder` -/

lemma firstInOrder_mem (π : Equiv.Perm (Fin n)) (s : Finset (Fin n)) (h : s.Nonempty) :
    firstInOrder π s h ∈ s := by
  obtain ⟨a, ha, he⟩ := Finset.mem_map.1 (Finset.min'_mem (s.map π.toEmbedding) h.map)
  unfold firstInOrder
  rw [← he]
  simpa using ha

lemma firstInOrder_le (π : Equiv.Perm (Fin n)) (s : Finset (Fin n)) (h : s.Nonempty)
    {t : Fin n} (ht : t ∈ s) : π (firstInOrder π s h) ≤ π t := by
  unfold firstInOrder
  rw [Equiv.apply_symm_apply]
  exact Finset.min'_le _ _ (Finset.mem_map_of_mem π.toEmbedding ht)

lemma eq_firstInOrder (π : Equiv.Perm (Fin n)) (s : Finset (Fin n)) (h : s.Nonempty)
    {x : Fin n} (hx : x ∈ s) (hle : ∀ t ∈ s, π x ≤ π t) : x = firstInOrder π s h := by
  apply π.injective
  exact le_antisymm (hle _ (firstInOrder_mem π s h)) (firstInOrder_le π s h hx)

/-! ### Extending a permutation of `Fin n` to `Fin (n + 1)` -/

/-- `extFun σ p` sends `last` to `p` and `castSucc i` to `p.succAbove (σ i)`. -/
def extFun (σ : Equiv.Perm (Fin n)) (p : Fin (n + 1)) (k : Fin (n + 1)) : Fin (n + 1) :=
  Fin.lastCases p (fun i ↦ p.succAbove (σ i)) k

@[simp] lemma extFun_last (σ : Equiv.Perm (Fin n)) (p : Fin (n + 1)) :
    extFun σ p (Fin.last n) = p := by
  simp [extFun]

@[simp] lemma extFun_castSucc (σ : Equiv.Perm (Fin n)) (p : Fin (n + 1)) (i : Fin n) :
    extFun σ p (Fin.castSucc i) = p.succAbove (σ i) := by
  simp [extFun]

lemma extFun_injective (σ : Equiv.Perm (Fin n)) (p : Fin (n + 1)) :
    Function.Injective (extFun σ p) := by
  intro a b hab
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rfl
    | cast b => simp at hab
  | cast a =>
    induction b using Fin.lastCases with
    | last => simp at hab
    | cast b => simpa using hab

/-- The permutation `extFun σ p` of `Fin (n + 1)`. -/
noncomputable def extPerm (x : Equiv.Perm (Fin n) × Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (extFun x.1 x.2) (Finite.injective_iff_bijective.1 (extFun_injective _ _))

lemma extPerm_apply (x : Equiv.Perm (Fin n) × Fin (n + 1)) (k : Fin (n + 1)) :
    extPerm x k = extFun x.1 x.2 k := rfl

lemma extPerm_injective : Function.Injective (extPerm (n := n)) := by
  rintro ⟨σ, p⟩ ⟨σ', p'⟩ h
  have hp : p = p' := by
    have := congrArg (fun π : Equiv.Perm (Fin (n + 1)) ↦ π (Fin.last n)) h
    simpa [extPerm_apply] using this
  subst hp
  have hσ : σ = σ' := by
    ext i
    have := congrArg (fun π : Equiv.Perm (Fin (n + 1)) ↦ π (Fin.castSucc i)) h
    simp only [extPerm_apply, extFun_castSucc, Fin.succAbove_right_inj] at this
    rw [this]
  rw [hσ]

lemma card_perm_prod :
    Fintype.card (Equiv.Perm (Fin n) × Fin (n + 1)) = Fintype.card (Equiv.Perm (Fin (n + 1))) := by
  simp [Fintype.card_perm, Fintype.card_prod, Nat.factorial_succ, mul_comm]

lemma firstInOrder_extPerm (σ : Equiv.Perm (Fin n)) (p : Fin (n + 1)) (s : Finset (Fin n))
    (h : s.Nonempty) (t : Finset (Fin (n + 1))) (ht : t.Nonempty)
    (hst : t = s.map Fin.castSuccEmb) :
    firstInOrder (extPerm (σ, p)) t ht = Fin.castSucc (firstInOrder σ s h) := by
  subst hst
  symm
  apply eq_firstInOrder
  · exact Finset.mem_map_of_mem Fin.castSuccEmb (firstInOrder_mem σ s h)
  · intro t' ht'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.1 ht'
    simp only [extPerm_apply, Fin.coe_castSuccEmb, extFun_castSucc]
    exact (Fin.strictMono_succAbove p).monotone (firstInOrder_le σ s h ht)

/-- Random-order binding: averaging over uniform permutations of `Fin (n + 1)` a quantity that
depends, at `extPerm (σ, p)`, only on `σ`. -/
lemma uniformPerm_bind_eq {X : Type*} (F : Equiv.Perm (Fin (n + 1)) → PMF X)
    (G : Equiv.Perm (Fin n) → PMF X) (hFG : ∀ σ p, F (extPerm (σ, p)) = G σ) :
    (uniformOn (univ : Finset (Equiv.Perm (Fin (n + 1)))) univ_nonempty).bind F =
      (uniformOn (univ : Finset (Equiv.Perm (Fin n))) univ_nonempty).bind G :=
  uniformOn_bind_eq extPerm extPerm_injective card_perm_prod F G hFG

/-! ### Abstract randomized runs -/

/-- An abstract randomized run: states `σ`, labels `ι`, improving labels `imp`, transitions
`next`, and a randomized rule. -/
noncomputable def genRun {σ ι : Type*} (imp : σ → Finset ι) (next : σ → ι → σ)
    (rule : (s : σ) → (imp s).Nonempty → PMF ι) : ℕ → σ → PMF (List σ)
  | 0, s => PMF.pure [s]
  | k + 1, s =>
    if h : (imp s).Nonempty then
      (rule s h).bind fun j ↦ (genRun imp next rule k (next s j)).map (List.cons s)
    else PMF.pure [s]

theorem genRun_transfer {σ σ' ι ι' : Type*} (imp : σ → Finset ι) (next : σ → ι → σ)
    (rule : (s : σ) → (imp s).Nonempty → PMF ι)
    (imp' : σ' → Finset ι') (next' : σ' → ι' → σ')
    (rule' : (s : σ') → (imp' s).Nonempty → PMF ι')
    (h : σ → σ') (e : ι → ι') (Inv : σ → Prop)
    (himp : ∀ s, Inv s → ((imp' (h s)).Nonempty ↔ (imp s).Nonempty))
    (hrule : ∀ s, Inv s → ∀ hs hs', rule' (h s) hs' = (rule s hs).map e)
    (hnext : ∀ s, Inv s → ∀ hs, ∀ j ∈ (rule s hs).support,
      Inv (next s j) ∧ next' (h s) (e j) = h (next s j))
    (k : ℕ) (s : σ) (hs : Inv s) :
    genRun imp' next' rule' k (h s) = (genRun imp next rule k s).map (List.map h) := by
  induction k generalizing s with
  | zero => simp [genRun, PMF.pure_map]
  | succ k ih =>
    rw [genRun, genRun]
    by_cases hne : (imp s).Nonempty
    · have hne' := (himp s hs).2 hne
      rw [dif_pos hne', dif_pos hne, hrule s hs hne hne', PMF.bind_map, PMF.map_bind]
      apply pmf_bind_congr_support
      intro j hj
      obtain ⟨hinv, hnx⟩ := hnext s hs hne j hj
      simp only [Function.comp_apply, hnx, ih _ hinv, PMF.map_comp]
      congr 1
    · have hne' : ¬ (imp' (h s)).Nonempty := fun h' ↦ hne ((himp s hs).1 h')
      rw [dif_neg hne', dif_neg hne, PMF.pure_map]
      simp

lemma LP.randomRun_eq_genRun (P : LP m n)
    (rule : (B : Finset (Fin n)) → (P.improving B).Nonempty → PMF (Fin n)) (k : ℕ)
    (B : Finset (Fin n)) : P.randomRun rule k B = genRun P.improving P.pivotTo rule k B := by
  induction k generalizing B with
  | zero => rfl
  | succ k ih => simp only [LP.randomRun, genRun, ih]

lemma Wolfe.randomRun_eq_genRun {D : ℕ} (p : Fin n → Fin D → ℝ)
    (rule : (S : Finset (Fin n)) → (improving p (affineMin p S)).Nonempty → PMF (Fin n))
    (k : ℕ) (S : Finset (Fin n)) :
    Wolfe.randomRun p rule k S =
      genRun (fun S ↦ improving p (affineMin p S)) (majorTo p) rule k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [Wolfe.randomRun, genRun, ih]

namespace LP

/-- Transfer of runs with arbitrary randomized rules from `P` to `Q`. -/
theorem randomRun_transfer {m' : ℕ} (P : LP m n) (Q : LP m' (n + 1))
    (hstep : ∀ B, P.IsFeasibleBasis B →
      Q.improving (hat B) = (P.improving B).map Fin.castSuccEmb ∧
      ∀ j ∈ P.improving B, P.IsFeasibleBasis (P.pivotTo B j) ∧
        Q.pivotTo (hat B) (Fin.castSucc j) = hat (P.pivotTo B j))
    (ruleP : (B : Finset (Fin n)) → (P.improving B).Nonempty → PMF (Fin n))
    (ruleQ : (B : Finset (Fin (n + 1))) → (Q.improving B).Nonempty → PMF (Fin (n + 1)))
    (hrule : ∀ B, P.IsFeasibleBasis B → ∀ hP hQ, ruleQ (hat B) hQ = (ruleP B hP).map Fin.castSucc)
    (hsupp : ∀ B, P.IsFeasibleBasis B → ∀ hP, ∀ j ∈ (ruleP B hP).support, j ∈ P.improving B)
    (B₀ : Finset (Fin n)) (hB₀ : P.IsFeasibleBasis B₀) (k : ℕ) :
    Q.randomRun ruleQ k (hat B₀) = (P.randomRun ruleP k B₀).map (List.map hat) := by
  rw [randomRun_eq_genRun, randomRun_eq_genRun]
  refine genRun_transfer _ _ _ _ _ _ hat Fin.castSucc P.IsFeasibleBasis ?_ hrule ?_ k B₀ hB₀
  · intro B hB
    rw [(hstep B hB).1, Finset.map_nonempty]
  · intro B hB hP j hj
    exact (hstep B hB).2 j (hsupp B hB hP j hj)

end LP

namespace IntLP

/-- Under nondegeneracy the leaving label is unique. -/
lemma leavingLabel_unique (P : IntLP m n) (hP : P.IsAdmissible) {B : Finset (Fin n)}
    (hB : P.toLP.IsFeasibleBasis B) {j : Fin n} (hj : j ∈ P.toLP.improving B) {i i' : Fin n}
    (hi : P.toLP.IsLeavingLabel B j i) (hi' : P.toLP.IsLeavingLabel B j i') : i = i' := by
  by_contra hne
  obtain ⟨hB', hx'⟩ := LP.pivot_spec hB hj hi
  have hmem : i' ∈ insert j (B.erase i) :=
    Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨Ne.symm hne, hi'.1⟩)
  have hpos := hP.2.2.2 _ hB' i' hmem
  rw [hx'] at hpos
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hpos
  have heq : P.toLP.basicSol B i / (-P.toLP.basicDir B j i) =
      P.toLP.basicSol B i' / (-P.toLP.basicDir B j i') :=
    le_antisymm (hi.2.2 i' hi'.1 hi'.2.1) (hi'.2.2 i hi.1 hi.2.1)
  rw [heq, div_neg, neg_mul, div_mul_cancel₀ _ hi'.2.1.ne, add_neg_cancel] at hpos
  exact lt_irrefl _ hpos

theorem unique_steps (P : IntLP m n) (hP : P.IsAdmissible)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B) (j : Fin n)
    (hj : j ∈ P.toLP.improving B) :
    (∀ B', P.toLP.IsPivot B j B' ↔ B' = P.toLP.pivotTo B j) ∧
    (∀ S', MajorCycle P.atom (hat B) (Fin.castSucc j) S' ↔ S' = hat (P.toLP.pivotTo B j)) := by
  have hjB := hB.1.not_mem_of_mem_improving hj
  obtain ⟨i, hi⟩ := LP.exists_leavingLabel hP.2.2.1 hB hj
  have hpiv : ∀ B', P.toLP.IsPivot B j B' ↔ B' = insert j (B.erase i) := by
    intro B'
    constructor
    · rintro ⟨-, -, -, i', hi', rfl⟩
      rw [leavingLabel_unique P hP hB hj hi hi']
    · rintro rfl
      exact ⟨hB, hj, hjB, i, hi, rfl⟩
  have hto : P.toLP.pivotTo B j = insert j (B.erase i) :=
    (hpiv _).1 (Classical.epsilon_spec (p := P.toLP.IsPivot B j) ⟨_, (hpiv _).2 rfl⟩)
  refine ⟨fun B' ↦ by rw [hpiv, hto], fun S' ↦ ?_⟩
  rw [hto]
  exact (thm_b hP hB hj hi).2.2.2.2 S'

/-- One Wolfe step at `B̂`: the pivot result is feasible and `majorTo` is its hat. -/
lemma wolfe_step (P : IntLP m n) (hP : P.IsAdmissible) {B : Finset (Fin n)}
    (hB : P.toLP.IsFeasibleBasis B) {j : Fin n} (hj : j ∈ P.toLP.improving B) :
    P.toLP.IsFeasibleBasis (P.toLP.pivotTo B j) ∧
      majorTo P.atom (hat B) (Fin.castSucc j) = hat (P.toLP.pivotTo B j) := by
  obtain ⟨h1, h2⟩ := unique_steps P hP B hB j hj
  constructor
  · obtain ⟨-, -, -, i, hi, heq⟩ := (h1 _).2 rfl
    rw [heq]
    exact (LP.pivot_spec hB hj hi).1
  · exact (h2 _).1 (Classical.epsilon_spec (p := MajorCycle P.atom (hat B) (Fin.castSucc j))
      ⟨_, (h2 _).2 rfl⟩)

theorem wolfe_randomRun_transfer (P : IntLP m n) (hP : P.IsAdmissible)
    (ruleW : (S : Finset (Fin (n + 1))) → (improving P.atom (affineMin P.atom S)).Nonempty →
      PMF (Fin (n + 1)))
    (ruleP : (B : Finset (Fin n)) → (P.toLP.improving B).Nonempty → PMF (Fin n))
    (hrule : ∀ B, P.toLP.IsFeasibleBasis B → ∀ hB hW,
      ruleW (hat B) hW = (ruleP B hB).map Fin.castSucc)
    (hsupp : ∀ B, P.toLP.IsFeasibleBasis B → ∀ hB, ∀ j ∈ (ruleP B hB).support,
      j ∈ P.toLP.improving B)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (k : ℕ) :
    Wolfe.randomRun P.atom ruleW k (hat B₀) =
      (P.toLP.randomRun ruleP k B₀).map (List.map hat) := by
  rw [Wolfe.randomRun_eq_genRun, LP.randomRun_eq_genRun]
  refine genRun_transfer _ _ _ _ _ _ hat Fin.castSucc P.toLP.IsFeasibleBasis ?_ hrule ?_
    k B₀ hB₀
  · intro B hB
    rw [improving_hat hB hP.1, Finset.map_nonempty]
  · intro B hB hB' j hj
    exact wolfe_step P hP hB (hsupp B hB hB' j hj)

end IntLP


namespace LP

/-- Transfer of Random-Edge runs from an LP `P` to an LP `Q` with one more label, when the
pivots of `Q` at `B̂` are the hats of the pivots of `P` at `B`. -/
theorem randomEdge_transfer {m' : ℕ} (P : LP m n) (Q : LP m' (n + 1))
    (hstep : ∀ B, P.IsFeasibleBasis B →
      Q.improving (hat B) = (P.improving B).map Fin.castSuccEmb ∧
      ∀ j ∈ P.improving B, P.IsFeasibleBasis (P.pivotTo B j) ∧
        Q.pivotTo (hat B) (Fin.castSucc j) = hat (P.pivotTo B j))
    (B₀ : Finset (Fin n)) (hB₀ : P.IsFeasibleBasis B₀) (k : ℕ) :
    Q.randomRun Q.randomEdge k (hat B₀) = (P.randomRun P.randomEdge k B₀).map (List.map hat) := by
  refine randomRun_transfer P Q hstep _ _ ?_ ?_ B₀ hB₀ k
  · intro B hB hP hQ
    exact uniformOn_eq_map _ hP Fin.castSuccEmb _ hQ (hstep B hB).1
  · intro B _ hP j hj
    exact mem_of_mem_support_uniformOn hj

/-- The same for Random-Bland. -/
theorem randomBland_transfer {m' : ℕ} (P : LP m n) (Q : LP m' (n + 1))
    (hstep : ∀ B, P.IsFeasibleBasis B →
      Q.improving (hat B) = (P.improving B).map Fin.castSuccEmb ∧
      ∀ j ∈ P.improving B, P.IsFeasibleBasis (P.pivotTo B j) ∧
        Q.pivotTo (hat B) (Fin.castSucc j) = hat (P.pivotTo B j))
    (B₀ : Finset (Fin n)) (hB₀ : P.IsFeasibleBasis B₀) (k : ℕ) :
    Q.randomBlandRun k (hat B₀) = (P.randomBlandRun k B₀).map (List.map hat) := by
  unfold randomBlandRun
  rw [PMF.map_bind]
  refine uniformPerm_bind_eq _ _ fun σ p ↦ ?_
  refine randomRun_transfer P Q hstep _ _ ?_ ?_ B₀ hB₀ k
  · intro B hB hP hQ
    simp only [blandBy, PMF.pure_map]
    rw [firstInOrder_extPerm σ p _ hP _ hQ (hstep B hB).1]
  · intro B _ hP j hj
    simp only [blandBy, PMF.mem_support_pure_iff] at hj
    rw [hj]
    exact firstInOrder_mem _ _ _

end LP

namespace IntLP

theorem rules_unique_steps_main (P : IntLP m n) (hP : P.IsAdmissible)
    (B : Finset (Fin n)) (hB : P.toLP.IsFeasibleBasis B) (j : Fin n)
    (hj : j ∈ P.toLP.improving B) :
    (∀ B', P.toLP.IsPivot B j B' ↔ B' = P.toLP.pivotTo B j) ∧
    (∀ S', MajorCycle P.atom (hat B) (Fin.castSucc j) S' ↔ S' = hat (P.toLP.pivotTo B j)) :=
  unique_steps P hP B hB j hj

theorem rules_random_edge_main (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (k : ℕ) :
    Wolfe.randomRun P.atom (Wolfe.randomInsertion P.atom) k (hat B₀) =
      (P.toLP.randomRun P.toLP.randomEdge k B₀).map (List.map hat) := by
  refine wolfe_randomRun_transfer P hP _ _ ?_ ?_ B₀ hB₀ k
  · intro B hB hB' hW
    exact uniformOn_eq_map _ hB' Fin.castSuccEmb _ hW (improving_hat hB hP.1)
  · intro B _ hB' j hj
    exact mem_of_mem_support_uniformOn hj

theorem rules_random_bland_main (P : IntLP m n) (hP : P.IsAdmissible)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (k : ℕ) :
    Wolfe.randomOrderRun P.atom k (hat B₀) =
      (P.toLP.randomBlandRun k B₀).map (List.map hat) := by
  unfold Wolfe.randomOrderRun LP.randomBlandRun
  rw [PMF.map_bind]
  refine uniformPerm_bind_eq _ _ fun σ p ↦ ?_
  refine wolfe_randomRun_transfer P hP _ _ ?_ ?_ B₀ hB₀ k
  · intro B hB hB' hW
    simp only [leastLabelBy, LP.blandBy, PMF.pure_map]
    rw [firstInOrder_extPerm σ p _ hB' _ hW (improving_hat hB hP.1)]
  · intro B _ hB' j hj
    simp only [LP.blandBy, PMF.mem_support_pure_iff] at hj
    rw [hj]
    exact firstInOrder_mem _ _ _

end IntLP

end WolfeSimplex

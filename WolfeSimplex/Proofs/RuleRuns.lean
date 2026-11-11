import WolfeSimplex.Defs.Rules
import WolfeSimplex.Proofs.Pivot

/-!
# Runs with rules

* Part 1: Wolfe runs with an insertion rule from a corral `B̂` correspond to simplex
  runs with a pivot rule from `B` (generalizing `thm_c` to rules and partial runs),
  and the linopt / least-label insertion rules correspond to Dantzig's / Bland's
  pivot rule.
* Part 2: transfer of simplex runs with rules between an LP `Q` with one extra label
  and an LP `P`, when the feasible bases, improving sets and leaving labels of `Q`
  at `B̂` are those of `P` at `B`.
* Part 3: in a nondegenerate LP, a (partial) simplex run never visits a basis twice.
-/

namespace WolfeSimplex

open Finset Wolfe

variable {m n : ℕ}

/-! ### A set identity for `hat` -/

/-- `(B̂ \ {i}) ∪ {j} = (B \ {i} ∪ {j})^`. -/
lemma hat_insert_erase (B : Finset (Fin n)) (j i : Fin n) :
    insert (Fin.castSucc j) ((hat B).erase (Fin.castSucc i)) = hat (insert j (B.erase i)) := by
  ext k
  induction k using Fin.lastCases with
  | last =>
    have : Fin.last n ≠ Fin.castSucc i := (Fin.castSucc_ne_last i).symm
    simp [this, (Fin.castSucc_ne_last j).symm, IntLP.last_mem_hat]
  | cast k =>
    simp only [mem_insert, mem_erase, IntLP.castSucc_mem_hat, Fin.castSucc_inj, ne_eq]

lemma hat_injective : Function.Injective (hat : Finset (Fin n) → Finset (Fin (n + 1))) := by
  intro B B' h
  rw [← IntLP.unhat_hat B, h, IntLP.unhat_hat]

/-! ### Part 1: Wolfe runs at `B̂` with rules -/

namespace IntLP

variable {P : IntLP m n}

/-- Every major cycle at `B̂` inserts `j` for an improving label `j` of `B` and ends
at `B̂'` for the pivot `B'` on `j` with some leaving label `i`. -/
lemma majorCycle_hat_spec (hP : P.IsAdmissible) {B : Finset (Fin n)}
    (hB : P.toLP.IsFeasibleBasis B) {j : Fin (n + 1)} {S' : Finset (Fin (n + 1))}
    (h : MajorCycle P.atom (hat B) j S') :
    ∃ j' i, j = Fin.castSucc j' ∧ j' ∈ P.toLP.improving B ∧ P.toLP.IsLeavingLabel B j' i ∧
      S' = hat (insert j' (B.erase i)) := by
  have hj := h.2.1
  rw [improving_hat hB hP.1, Finset.mem_map] at hj
  obtain ⟨j', hj', rfl⟩ := hj
  obtain ⟨i, hi⟩ := LP.exists_leavingLabel hP.2.2.1 hB hj'
  exact ⟨j', i, rfl, hj', hi, ((thm_b hP hB hj' hi).2.2.2.2 S').1 h⟩

theorem partialRun_hat_iff (hP : P.IsAdmissible)
    (wch : Finset (Fin (n + 1)) → Fin (n + 1) → Prop) (sch : Finset (Fin n) → Fin n → Prop)
    (hch : ∀ B, P.toLP.IsFeasibleBasis B → ∀ j : Fin n, wch (hat B) (Fin.castSucc j) ↔ sch B j)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (f : ℕ)
    (S : ℕ → Finset (Fin (n + 1))) :
    (IsPartialWolfeRunWith P.atom wch f S ∧ S 0 = hat B₀) ↔
      ∃ B : ℕ → Finset (Fin n), P.toLP.IsPartialSimplexRunWith sch f B ∧ B 0 = B₀ ∧
        ∀ k ≤ f, S k = hat (B k) := by
  constructor
  · rintro ⟨⟨-, hmaj⟩, hS0⟩
    set B : ℕ → Finset (Fin n) := fun k ↦ unhat (S k)
    have key : ∀ k ≤ f, P.toLP.IsFeasibleBasis (B k) ∧ S k = hat (B k) := by
      intro k
      induction k with
      | zero => intro _; simp only [B, hS0, unhat_hat]; exact ⟨hB₀, trivial⟩
      | succ k ih =>
        intro hk
        obtain ⟨hBk, hSk⟩ := ih (by omega)
        obtain ⟨j, -, hj⟩ := hmaj k (by omega)
        rw [hSk] at hj
        obtain ⟨j', i, -, hj', hi, hS'⟩ := majorCycle_hat_spec hP hBk hj
        simp only [B, hS', unhat_hat]
        exact ⟨(LP.pivot_spec hBk hj' hi).1, trivial⟩
    refine ⟨B, ⟨fun k hk ↦ (key k hk).1, fun k hk ↦ ?_⟩, by simp [B, hS0, unhat_hat],
      fun k hk ↦ (key k hk).2⟩
    obtain ⟨hBk, hSk⟩ := key k hk.le
    obtain ⟨j, hwj, hj⟩ := hmaj k hk
    rw [hSk] at hj hwj
    obtain ⟨j', i, rfl, hj', hi, hS'⟩ := majorCycle_hat_spec hP hBk hj
    refine ⟨j', (hch _ hBk j').1 hwj, hBk, hj', hBk.1.not_mem_of_mem_improving hj', i, hi, ?_⟩
    simp only [B, hS', unhat_hat]
  · rintro ⟨B, ⟨hfeas, hpiv⟩, hB0, hS⟩
    refine ⟨⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩, by rw [hS 0 (Nat.zero_le _), hB0]⟩
    · rw [hS k hk]; exact (thm_a hP (hfeas k hk)).1
    · obtain ⟨j, hsj, -, hj, -, i, hi, heq⟩ := hpiv k hk
      refine ⟨Fin.castSucc j, ?_, ?_⟩
      · rw [hS k hk.le]; exact (hch _ (hfeas k hk.le) j).2 hsj
      · rw [hS k hk.le, hS (k + 1) hk, heq]
        exact ((thm_b hP (hfeas k hk.le) hj hi).2.2.2.2 _).2 rfl

theorem run_hat_iff (hP : P.IsAdmissible)
    (wch : Finset (Fin (n + 1)) → Fin (n + 1) → Prop) (sch : Finset (Fin n) → Fin n → Prop)
    (hch : ∀ B, P.toLP.IsFeasibleBasis B → ∀ j : Fin n, wch (hat B) (Fin.castSucc j) ↔ sch B j)
    (B₀ : Finset (Fin n)) (hB₀ : P.toLP.IsFeasibleBasis B₀) (f : ℕ)
    (S : ℕ → Finset (Fin (n + 1))) :
    (IsWolfeRunWith P.atom wch f S ∧ S 0 = hat B₀) ↔
      ∃ B : ℕ → Finset (Fin n), P.toLP.IsSimplexRunWith sch f B ∧ B 0 = B₀ ∧
        ∀ k ≤ f, S k = hat (B k) := by
  constructor
  · rintro ⟨⟨hrun, hlast⟩, hS0⟩
    obtain ⟨B, hBrun, hB0, hSB⟩ :=
      (partialRun_hat_iff hP wch sch hch B₀ hB₀ f S).1 ⟨hrun, hS0⟩
    refine ⟨B, ⟨hBrun, ?_⟩, hB0, hSB⟩
    rw [hSB f le_rfl, improving_hat (hBrun.1 f le_rfl) hP.1, Finset.map_eq_empty] at hlast
    exact hlast
  · rintro ⟨B, ⟨hBrun, hlast⟩, hB0, hSB⟩
    obtain ⟨hrun, hS0⟩ := (partialRun_hat_iff hP wch sch hch B₀ hB₀ f S).2 ⟨B, hBrun, hB0, hSB⟩
    refine ⟨⟨hrun, ?_⟩, hS0⟩
    rw [hSB f le_rfl, improving_hat (hBrun.1 f le_rfl) hP.1, hlast, Finset.map_empty]

theorem linopt_hat_iff_of_nondegenerate {B : Finset (Fin n)} (hm : 1 ≤ m)
    (hB : P.toLP.IsFeasibleBasis B) (hnd : P.toLP.IsNondegenerate B) (j : Fin n) :
    IsLinoptChoice P.atom (hat B) (Fin.castSucc j) ↔ P.toLP.IsDantzigChoice B j := by
  obtain ⟨-, himp, κ, hκ, hgap, -⟩ := thm_a_of_nondegenerate hm hB hnd
  have hdot : ∀ k : Fin n, P.atom (Fin.castSucc k) ⬝ᵥ affineMin P.atom (hat B) =
      κ * P.toLP.reducedCost B k + normSq (affineMin P.atom (hat B)) := by
    intro k
    have := hgap k
    unfold gap at this
    linarith
  unfold IsLinoptChoice LP.IsDantzigChoice
  rw [himp, show Fin.castSucc j = Fin.castSuccEmb j from rfl, Finset.mem_map',
    Finset.forall_mem_map]
  simp only [Fin.coe_castSuccEmb, hdot]
  constructor
  · rintro ⟨hj, h⟩
    refine ⟨hj, fun i hi ↦ ?_⟩
    have : κ * P.toLP.reducedCost B j ≤ κ * P.toLP.reducedCost B i := by linarith [h i hi]
    exact le_of_mul_le_mul_left this hκ
  · rintro ⟨hj, h⟩
    refine ⟨hj, fun i hi ↦ ?_⟩
    have := mul_le_mul_of_nonneg_left (h i hi) hκ.le
    linarith

theorem linopt_hat_iff {B : Finset (Fin n)} (hP : P.IsAdmissible)
    (hB : P.toLP.IsFeasibleBasis B) (j : Fin n) :
    IsLinoptChoice P.atom (hat B) (Fin.castSucc j) ↔ P.toLP.IsDantzigChoice B j := by
  exact linopt_hat_iff_of_nondegenerate hP.1 hB (hP.2.2.2 B hB) j

theorem leastLabel_hat_iff {B : Finset (Fin n)} (hP : P.IsAdmissible)
    (hB : P.toLP.IsFeasibleBasis B) (ρ : Fin (n + 1) → ℕ) (j : Fin n) :
    IsLeastLabelChoice P.atom ρ (hat B) (Fin.castSucc j) ↔
      P.toLP.IsBlandChoice (fun k ↦ ρ (Fin.castSucc k)) B j := by
  unfold IsLeastLabelChoice LP.IsBlandChoice
  rw [improving_hat hB hP.1, show Fin.castSucc j = Fin.castSuccEmb j from rfl, Finset.mem_map',
    Finset.forall_mem_map]
  simp only [Fin.coe_castSuccEmb]

end IntLP

/-! ### Part 2: transfer of simplex runs between `Q` and `P` -/

namespace LP

section Transfer

variable (P : LP m n) (Q : LP (m + 1) (n + 1))

/-- A pivot of `Q` at `B̂` is the hat of a pivot of `P` at `B`. -/
lemma transfer_pivot_spec
    (himp : ∀ B, P.IsFeasibleBasis B → Q.improving (hat B) = (P.improving B).map Fin.castSuccEmb)
    (hleave : ∀ B, P.IsFeasibleBasis B → ∀ j ∈ P.improving B, ∀ i' : Fin (n + 1),
      Q.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔ ∃ i, i' = Fin.castSucc i ∧ P.IsLeavingLabel B j i)
    {B : Finset (Fin n)} (hB : P.IsFeasibleBasis B) {j' : Fin (n + 1)}
    {S' : Finset (Fin (n + 1))} (h : Q.IsPivot (hat B) j' S') :
    ∃ j i, j' = Fin.castSucc j ∧ j ∈ P.improving B ∧ P.IsLeavingLabel B j i ∧
      S' = hat (insert j (B.erase i)) := by
  obtain ⟨-, hj', -, i', hi', heq⟩ := h
  rw [himp _ hB] at hj'
  obtain ⟨j, hj, hjj⟩ := Finset.mem_map.1 hj'
  obtain rfl : Fin.castSucc j = j' := hjj
  obtain ⟨i, rfl, hi⟩ := (hleave _ hB j hj i').1 hi'
  exact ⟨j, i, rfl, hj, hi, by rw [heq, hat_insert_erase]⟩

/-- The hat of a pivot of `P` at `B` is a pivot of `Q` at `B̂`. -/
lemma transfer_pivot_from
    (hfeas : ∀ B, P.IsFeasibleBasis B → Q.IsFeasibleBasis (hat B))
    (himp : ∀ B, P.IsFeasibleBasis B → Q.improving (hat B) = (P.improving B).map Fin.castSuccEmb)
    (hleave : ∀ B, P.IsFeasibleBasis B → ∀ j ∈ P.improving B, ∀ i' : Fin (n + 1),
      Q.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔ ∃ i, i' = Fin.castSucc i ∧ P.IsLeavingLabel B j i)
    {B B'' : Finset (Fin n)} {j : Fin n} (h : P.IsPivot B j B'') :
    Q.IsPivot (hat B) (Fin.castSucc j) (hat B'') := by
  obtain ⟨hB, hj, hjB, i, hi, rfl⟩ := h
  refine ⟨hfeas B hB, ?_, ?_, Fin.castSucc i, (hleave B hB j hj _).2 ⟨i, rfl, hi⟩,
    (hat_insert_erase B j i).symm⟩
  · rw [himp B hB]; exact Finset.mem_map_of_mem _ hj
  · rw [IntLP.castSucc_mem_hat]; exact hjB

lemma transfer_pivot_of
    (hfeas : ∀ B', Q.IsFeasibleBasis B' ↔ ∃ B, P.IsFeasibleBasis B ∧ B' = hat B)
    (himp : ∀ B, P.IsFeasibleBasis B → Q.improving (hat B) = (P.improving B).map Fin.castSuccEmb)
    (hleave : ∀ B, P.IsFeasibleBasis B → ∀ j ∈ P.improving B, ∀ i' : Fin (n + 1),
      Q.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔ ∃ i, i' = Fin.castSucc i ∧ P.IsLeavingLabel B j i)
    {B B'' : Finset (Fin n)} {j : Fin n} (h : P.IsPivot B j B'') :
    Q.IsPivot (hat B) (Fin.castSucc j) (hat B'') := by
  exact transfer_pivot_from P Q (fun B hB ↦ (hfeas _).2 ⟨B, hB, rfl⟩) himp hleave h

theorem transfer_partialRun_from_iff
    (hfeas : ∀ B, P.IsFeasibleBasis B → Q.IsFeasibleBasis (hat B))
    (himp : ∀ B, P.IsFeasibleBasis B → Q.improving (hat B) = (P.improving B).map Fin.castSuccEmb)
    (hleave : ∀ B, P.IsFeasibleBasis B → ∀ j ∈ P.improving B, ∀ i' : Fin (n + 1),
      Q.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔ ∃ i, i' = Fin.castSucc i ∧ P.IsLeavingLabel B j i)
    (qch : Finset (Fin (n + 1)) → Fin (n + 1) → Prop) (pch : Finset (Fin n) → Fin n → Prop)
    (hch : ∀ B, P.IsFeasibleBasis B → ∀ j : Fin n, qch (hat B) (Fin.castSucc j) ↔ pch B j)
    (B₀ : Finset (Fin n)) (hB₀ : P.IsFeasibleBasis B₀) (f : ℕ) (B' : ℕ → Finset (Fin (n + 1))) :
    (Q.IsPartialSimplexRunWith qch f B' ∧ B' 0 = hat B₀) ↔
      ∃ B, P.IsPartialSimplexRunWith pch f B ∧ B 0 = B₀ ∧ ∀ k ≤ f, B' k = hat (B k) := by
  constructor
  · rintro ⟨⟨-, hpiv⟩, hB'0⟩
    set B : ℕ → Finset (Fin n) := fun k ↦ IntLP.unhat (B' k)
    have key : ∀ k ≤ f, P.IsFeasibleBasis (B k) ∧ B' k = hat (B k) := by
      intro k
      induction k with
      | zero => intro _; simp only [B, hB'0, IntLP.unhat_hat]; exact ⟨hB₀, trivial⟩
      | succ k ih =>
        intro hk
        obtain ⟨hBk, hSk⟩ := ih (by omega)
        obtain ⟨j', -, hj'⟩ := hpiv k (by omega)
        rw [hSk] at hj'
        obtain ⟨j, i, -, hj, hi, hS'⟩ := transfer_pivot_spec P Q himp hleave hBk hj'
        simp only [B, hS', IntLP.unhat_hat]
        exact ⟨(pivot_spec hBk hj hi).1, trivial⟩
    refine ⟨B, ⟨fun k hk ↦ (key k hk).1, fun k hk ↦ ?_⟩, by simp [B, hB'0, IntLP.unhat_hat],
      fun k hk ↦ (key k hk).2⟩
    obtain ⟨hBk, hSk⟩ := key k hk.le
    obtain ⟨j', hqj, hj'⟩ := hpiv k hk
    rw [hSk] at hj' hqj
    obtain ⟨j, i, rfl, hj, hi, hS'⟩ := transfer_pivot_spec P Q himp hleave hBk hj'
    refine ⟨j, (hch _ hBk j).1 hqj, hBk, hj, hBk.1.not_mem_of_mem_improving hj, i, hi, ?_⟩
    simp only [B, hS', IntLP.unhat_hat]
  · rintro ⟨B, ⟨hPfeas, hpiv⟩, hB0, hS⟩
    refine ⟨⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩, by rw [hS 0 (Nat.zero_le _), hB0]⟩
    · rw [hS k hk]; exact hfeas _ (hPfeas k hk)
    · obtain ⟨j, hpj, hpk⟩ := hpiv k hk
      refine ⟨Fin.castSucc j, ?_, ?_⟩
      · rw [hS k hk.le]; exact (hch _ (hPfeas k hk.le) j).2 hpj
      · rw [hS k hk.le, hS (k + 1) hk]
        exact transfer_pivot_from P Q hfeas himp hleave hpk

theorem transfer_partialRun_iff
    (hfeas : ∀ B', Q.IsFeasibleBasis B' ↔ ∃ B, P.IsFeasibleBasis B ∧ B' = hat B)
    (himp : ∀ B, P.IsFeasibleBasis B → Q.improving (hat B) = (P.improving B).map Fin.castSuccEmb)
    (hleave : ∀ B, P.IsFeasibleBasis B → ∀ j ∈ P.improving B, ∀ i' : Fin (n + 1),
      Q.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔ ∃ i, i' = Fin.castSucc i ∧ P.IsLeavingLabel B j i)
    (qch : Finset (Fin (n + 1)) → Fin (n + 1) → Prop) (pch : Finset (Fin n) → Fin n → Prop)
    (hch : ∀ B, P.IsFeasibleBasis B → ∀ j : Fin n, qch (hat B) (Fin.castSucc j) ↔ pch B j)
    (B₀ : Finset (Fin n)) (hB₀ : P.IsFeasibleBasis B₀) (f : ℕ) (B' : ℕ → Finset (Fin (n + 1))) :
    (Q.IsPartialSimplexRunWith qch f B' ∧ B' 0 = hat B₀) ↔
      ∃ B, P.IsPartialSimplexRunWith pch f B ∧ B 0 = B₀ ∧ ∀ k ≤ f, B' k = hat (B k) := by
  exact transfer_partialRun_from_iff P Q (fun B hB ↦ (hfeas _).2 ⟨B, hB, rfl⟩)
    himp hleave qch pch hch B₀ hB₀ f B'

theorem transfer_run_from_iff
    (hfeas : ∀ B, P.IsFeasibleBasis B → Q.IsFeasibleBasis (hat B))
    (himp : ∀ B, P.IsFeasibleBasis B → Q.improving (hat B) = (P.improving B).map Fin.castSuccEmb)
    (hleave : ∀ B, P.IsFeasibleBasis B → ∀ j ∈ P.improving B, ∀ i' : Fin (n + 1),
      Q.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔ ∃ i, i' = Fin.castSucc i ∧ P.IsLeavingLabel B j i)
    (qch : Finset (Fin (n + 1)) → Fin (n + 1) → Prop) (pch : Finset (Fin n) → Fin n → Prop)
    (hch : ∀ B, P.IsFeasibleBasis B → ∀ j : Fin n, qch (hat B) (Fin.castSucc j) ↔ pch B j)
    (B₀ : Finset (Fin n)) (hB₀ : P.IsFeasibleBasis B₀) (f : ℕ) (B' : ℕ → Finset (Fin (n + 1))) :
    (Q.IsSimplexRunWith qch f B' ∧ B' 0 = hat B₀) ↔
      ∃ B, P.IsSimplexRunWith pch f B ∧ B 0 = B₀ ∧ ∀ k ≤ f, B' k = hat (B k) := by
  constructor
  · rintro ⟨⟨hrun, hlast⟩, hS0⟩
    obtain ⟨B, hBrun, hB0, hSB⟩ :=
      (transfer_partialRun_from_iff P Q hfeas himp hleave qch pch hch B₀ hB₀ f B').1 ⟨hrun, hS0⟩
    refine ⟨B, ⟨hBrun, ?_⟩, hB0, hSB⟩
    rw [hSB f le_rfl, himp _ (hBrun.1 f le_rfl), Finset.map_eq_empty] at hlast
    exact hlast
  · rintro ⟨B, ⟨hBrun, hlast⟩, hB0, hSB⟩
    obtain ⟨hrun, hS0⟩ :=
      (transfer_partialRun_from_iff P Q hfeas himp hleave qch pch hch B₀ hB₀ f B').2
        ⟨B, hBrun, hB0, hSB⟩
    refine ⟨⟨hrun, ?_⟩, hS0⟩
    rw [hSB f le_rfl, himp _ (hBrun.1 f le_rfl), hlast, Finset.map_empty]

theorem transfer_run_iff
    (hfeas : ∀ B', Q.IsFeasibleBasis B' ↔ ∃ B, P.IsFeasibleBasis B ∧ B' = hat B)
    (himp : ∀ B, P.IsFeasibleBasis B → Q.improving (hat B) = (P.improving B).map Fin.castSuccEmb)
    (hleave : ∀ B, P.IsFeasibleBasis B → ∀ j ∈ P.improving B, ∀ i' : Fin (n + 1),
      Q.IsLeavingLabel (hat B) (Fin.castSucc j) i' ↔ ∃ i, i' = Fin.castSucc i ∧ P.IsLeavingLabel B j i)
    (qch : Finset (Fin (n + 1)) → Fin (n + 1) → Prop) (pch : Finset (Fin n) → Fin n → Prop)
    (hch : ∀ B, P.IsFeasibleBasis B → ∀ j : Fin n, qch (hat B) (Fin.castSucc j) ↔ pch B j)
    (B₀ : Finset (Fin n)) (hB₀ : P.IsFeasibleBasis B₀) (f : ℕ) (B' : ℕ → Finset (Fin (n + 1))) :
    (Q.IsSimplexRunWith qch f B' ∧ B' 0 = hat B₀) ↔
      ∃ B, P.IsSimplexRunWith pch f B ∧ B 0 = B₀ ∧ ∀ k ≤ f, B' k = hat (B k) := by
  exact transfer_run_from_iff P Q (fun B hB ↦ (hfeas _).2 ⟨B, hB, rfl⟩)
    himp hleave qch pch hch B₀ hB₀ f B'

theorem dantzig_transfer (Δ : ℝ) (hΔ : 0 < Δ)
    (himp : ∀ B, P.IsFeasibleBasis B → Q.improving (hat B) = (P.improving B).map Fin.castSuccEmb)
    (hrc : ∀ B, P.IsFeasibleBasis B → ∀ j : Fin n,
      Q.reducedCost (hat B) (Fin.castSucc j) = Δ * P.reducedCost B j)
    (B : Finset (Fin n)) (hB : P.IsFeasibleBasis B) (j : Fin n) :
    Q.IsDantzigChoice (hat B) (Fin.castSucc j) ↔ P.IsDantzigChoice B j := by
  unfold IsDantzigChoice
  rw [himp B hB, show Fin.castSucc j = Fin.castSuccEmb j from rfl, Finset.mem_map',
    Finset.forall_mem_map]
  simp only [Fin.coe_castSuccEmb, hrc B hB]
  constructor
  · rintro ⟨hj, h⟩
    exact ⟨hj, fun i hi ↦ le_of_mul_le_mul_left (h i hi) hΔ⟩
  · rintro ⟨hj, h⟩
    exact ⟨hj, fun i hi ↦ mul_le_mul_of_nonneg_left (h i hi) hΔ.le⟩

theorem bland_transfer
    (himp : ∀ B, P.IsFeasibleBasis B → Q.improving (hat B) = (P.improving B).map Fin.castSuccEmb)
    (ρ : Fin (n + 1) → ℕ) (B : Finset (Fin n)) (hB : P.IsFeasibleBasis B) (j : Fin n) :
    Q.IsBlandChoice ρ (hat B) (Fin.castSucc j) ↔ P.IsBlandChoice (fun k ↦ ρ (Fin.castSucc k)) B j := by
  unfold IsBlandChoice
  rw [himp B hB, show Fin.castSucc j = Fin.castSuccEmb j from rfl, Finset.mem_map',
    Finset.forall_mem_map]
  simp only [Fin.coe_castSuccEmb]

end Transfer

/-! ### Part 3: simplex runs visit distinct bases -/

/-- A pivot at a nondegenerate feasible basis strictly decreases the objective value. -/
lemma objValue_lt_of_isPivot {P : LP m n} {B B' : Finset (Fin n)} {j : Fin n}
    (hnd : P.IsNondegenerate B) (h : P.IsPivot B j B') : P.objValue B' < P.objValue B := by
  obtain ⟨hB, hj, hjB, i, hi, rfl⟩ := h
  have hrc : P.reducedCost B j < 0 := by simpa [improving] using hj
  have hθ : 0 < P.basicSol B i / (-P.basicDir B j i) :=
    div_pos (hnd i hi.1) (neg_pos.2 hi.2.1)
  rw [objValue, objValue, (pivot_spec hB hj hi).2, dotProduct_add, dotProduct_smul,
    hB.1.cost_basicDir hjB, smul_eq_mul]
  linarith [mul_neg_of_pos_of_neg hθ hrc]

theorem partialRun_injOn (P : LP m n)
    (hnd : ∀ B, P.IsFeasibleBasis B → P.IsNondegenerate B)
    (ch : Finset (Fin n) → Fin n → Prop) (f : ℕ) (B : ℕ → Finset (Fin n))
    (h : P.IsPartialSimplexRunWith ch f B) : Set.InjOn B (Set.Iic f) := by
  obtain ⟨hfeas, hpiv⟩ := h
  have hstep : ∀ k < f, P.objValue (B (k + 1)) < P.objValue (B k) := by
    intro k hk
    obtain ⟨j, -, hp⟩ := hpiv k hk
    exact objValue_lt_of_isPivot (hnd _ (hfeas k hk.le)) hp
  have hlt : ∀ a b, a < b → b ≤ f → P.objValue (B b) < P.objValue (B a) := by
    intro a b hab hb
    induction b, hab using Nat.le_induction with
    | base => exact hstep a (by omega)
    | succ b hab ih => exact (hstep b (by omega)).trans (ih (by omega))
  intro a ha b hb hab
  simp only [Set.mem_Iic] at ha hb
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := hlt a b h hb; rw [hab] at this; exact lt_irrefl _ this
  · have := hlt b a h ha; rw [hab] at this; exact lt_irrefl _ this

end LP

end WolfeSimplex

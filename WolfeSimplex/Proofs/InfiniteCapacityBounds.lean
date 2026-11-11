import WolfeSimplex.Proofs.InfiniteCapacity

/-! Binary bounds for the uncapacitated-network normalization. One flag per
arc records whether its upper bound is absent. No source run is encoded. -/
namespace WolfeSimplex.ExtendedNetwork
open Finset
variable {v n : ℕ} (Q : ExtendedNetwork v n)

def inputSize : ℕ := Q.data.inputSize + n

theorem dimensions_le : v + n + 2 ≤ Q.inputSize :=
  Q.data.dimensions_le.trans (by unfold inputSize; omega)

theorem entries_bounded : Q.data.EntriesBounded (2 ^ Q.inputSize) := by
  have h := Q.data.entries_bounded
  have hp : 2 ^ Q.data.inputSize ≤ 2 ^ Q.inputSize :=
    Nat.pow_le_pow_right (by decide) (by unfold inputSize; omega)
  exact ⟨fun w ↦ ⟨(h.1 w).1.trans hp, (h.1 w).2.trans hp⟩,
    fun e ↦ ⟨(h.2.1 e).1.trans hp, (h.2.1 e).2.trans hp⟩,
    fun e ↦ ⟨(h.2.2 e).1.trans hp, (h.2.2 e).2.trans hp⟩⟩

theorem bound_le : Q.bound ≤ 2 ^ (3 * (1 + Q.inputSize)) := by
  let B := 2 ^ Q.inputSize
  have hB : 1 ≤ B := Nat.one_le_pow _ _ (by decide)
  have hv : v ≤ B := (by have := Q.dimensions_le; omega : v ≤ Q.inputSize).trans
    Nat.lt_two_pow_self.le
  have hs : (∑ w, (Q.data.supply w).num.natAbs) ≤ v * B := by
    calc _ ≤ ∑ _ : Fin v, B := sum_le_sum (fun w _ ↦ (Q.entries_bounded.1 w).1)
         _ = _ := by simp
  have hm : Q.bound ≤ 1 + B * B := by unfold bound; nlinarith
  calc Q.bound ≤ 4 * (B * B) := hm.trans (by nlinarith)
       _ = 2 ^ (2 * Q.inputSize + 2) := by
         dsimp [B]; rw [pow_add, pow_two]; ring
       _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem finite_entries : Q.finite.EntriesBounded (2 ^ (3 * (1 + Q.inputSize))) := by
  have hp : 2 ^ Q.inputSize ≤ 2 ^ (3 * (1 + Q.inputSize)) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hB : 1 ≤ 2 ^ (3 * (1 + Q.inputSize)) := Nat.one_le_pow _ _ (by decide)
  refine ⟨fun w ↦ ⟨(Q.entries_bounded.1 w).1.trans hp,
      (Q.entries_bounded.1 w).2.trans hp⟩,
    fun e ↦ ⟨(Q.entries_bounded.2.1 e).1.trans hp,
      (Q.entries_bounded.2.1 e).2.trans hp⟩, fun e ↦ ?_⟩
  by_cases he : e ∈ Q.infinite
  · simpa [finite, he] using And.intro Q.bound_le hB
  · simpa [finite, he] using And.intro ((Q.entries_bounded.2.2 e).1.trans hp)
      ((Q.entries_bounded.2.2 e).2.trans hp)

private theorem scalar_entries (R : RationalNetwork v n) (B : ℕ)
    (h : R.EntriesBounded B) : R.scalars.EntriesBounded B := by
  refine ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i, ?_⟩
  intro j
  refine Fin.addCases (fun w ↦ ?_) (fun e ↦ ?_) j
  · simpa [RationalNetwork.scalars] using h.1 w
  · refine Fin.addCases (fun e ↦ ?_) (fun e ↦ ?_) e
    · simpa [RationalNetwork.scalars, -Fin.natAdd_eq_addNat] using h.2.1 e
    · simpa [RationalNetwork.scalars, -Fin.natAdd_eq_addNat] using h.2.2 e

theorem finite_inputSize : Q.finite.inputSize ≤ 10 ^ 6 * (1 + Q.inputSize) ^ 3 := by
  have hs := Q.finite.scalars.inputSize_le (3 * (1 + Q.inputSize))
    (scalar_entries Q.finite _ Q.finite_entries)
  have hd := Q.dimensions_le
  have he : ((List.ofFn Q.data.tail).flatMap
      (fun w ↦ Construction.encodeNat w.val)).length +
      ((List.ofFn Q.data.head).flatMap
      (fun w ↦ Construction.encodeNat w.val)).length ≤ Q.inputSize := by
    have hi : Q.data.inputSize ≤ Q.inputSize := by unfold inputSize; omega
    simp only [RationalNetwork.inputSize, RationalNetwork.encoding, List.length_append] at hi
    omega
  have hshape : 0 + (v + (n + n)) + 3 * (1 + Q.inputSize) + 3 ≤
      6 * (1 + Q.inputSize) := by omega
  have hb : Q.finite.scalars.inputSize ≤ 21600 * (1 + Q.inputSize) ^ 3 := by
    calc _ ≤ 100 * (6 * (1 + Q.inputSize)) ^ 3 :=
          hs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hshape _))
         _ = _ := by ring
  have hp : Q.inputSize ≤ (1 + Q.inputSize) ^ 3 :=
    (by omega : Q.inputSize ≤ 1 + Q.inputSize).trans (by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 1 + Q.inputSize) (by decide : 1 ≤ 3))
  change Q.finite.encoding.length ≤ _
  simp only [RationalNetwork.encoding, List.length_append]
  change Q.finite.scalars.inputSize + _ + _ ≤ _
  have ht : (List.ofFn Q.finite.tail) = List.ofFn Q.data.tail := rfl
  have hh : (List.ofFn Q.finite.head) = List.ofFn Q.data.head := rfl
  rw [ht, hh]
  nlinarith

end WolfeSimplex.ExtendedNetwork

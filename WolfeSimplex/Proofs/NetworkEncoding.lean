import WolfeSimplex.Proofs.Corollary4Count
import WolfeSimplex.Proofs.Corollary4Resources

set_option maxRecDepth 8000
set_option exponentiation.threshold 1024

namespace WolfeSimplex.RationalNetwork
open Finset
variable {v n m c : ℕ} (Q : RationalNetwork v n) (D : Q.toNetwork.RowDeletion m c)

/-- For the connected hard family, delete the last conservation row. The
retained-row enumeration is the literal index inclusion, with no graph search
or noncomputable selection in the reduction. -/
def deleteLast (Q : RationalNetwork (m + 1) n) : Q.toNetwork.RowDeletion m 1 where
  component := fun _ ↦ 0
  root := fun _ ↦ Fin.last m
  root_component := fun k ↦ Fin.eq_zero k |>.symm
  arc_component := fun _ ↦ rfl
  rows :=
    { toFun := fun i ↦ ⟨i.castSucc, Fin.castSucc_ne_last i⟩
      invFun := fun w ↦ w.val.castPred w.property
      left_inv := fun i ↦ Fin.castPred_castSucc
      right_inv := fun w ↦ Subtype.ext (Fin.castSucc_castPred _ _) }

@[simp] theorem deleteLast_row (Q : RationalNetwork (m + 1) n) (i : Fin m) :
    ((Q.deleteLast).rows i).val = i.castSucc := rfl

def EntriesBounded (B : ℕ) : Prop :=
  (∀ w, (Q.supply w).num.natAbs ≤ B ∧ (Q.supply w).den ≤ B) ∧
    (∀ e, (Q.cost e).num.natAbs ≤ B ∧ (Q.cost e).den ≤ B) ∧
    (∀ e, (Q.capacity e).num.natAbs ≤ B ∧ (Q.capacity e).den ≤ B)

theorem standard_entries (B : ℕ) (hB : 1 ≤ B) (hQ : Q.EntriesBounded B) :
    (Q.standard D).EntriesBounded B := by
  refine ⟨?_, ?_, ?_⟩
  · intro r j
    refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r <;>
      refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp only [standard, Fin.addCases_left, Fin.addCases_right] <;>
      (try split_ifs) <;> norm_num <;> omega
  · intro r
    refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r
    · simpa only [standard, Fin.append_left] using hQ.1 (D.rows i).val
    · simpa only [standard, Fin.append_right] using hQ.2.2 e
  · intro j
    refine Fin.addCases (fun e ↦ ?_) (fun e ↦ ?_) j
    · simpa only [standard, Fin.append_left] using hQ.2.1 e
    · simp only [standard, Fin.append_right, Pi.zero_apply]; norm_num; omega

/-- The scalar part of a native network encoding; endpoints follow as binary
indices. The unary headers remain linear in the network's explicit data. -/
def scalars : RatLP 0 (v + (n + n)) where
  A := Fin.elim0
  b := Fin.elim0
  c := Fin.append Q.supply (Fin.append Q.cost Q.capacity)

def encoding : List Bool := Q.scalars.encoding ++
  (List.ofFn Q.tail).flatMap (fun w ↦ Construction.encodeNat w.val) ++
  (List.ofFn Q.head).flatMap (fun w ↦ Construction.encodeNat w.val)

def inputSize : ℕ := Q.encoding.length

theorem scalar_size_le : Q.scalars.inputSize ≤ Q.inputSize := by
  simp only [inputSize, encoding, RatLP.inputSize, List.length_append]
  omega

theorem dimensions_le : v + n + 2 ≤ Q.inputSize := by
  have hs := Q.scalars.dimensions_le
  have he := Q.scalar_size_le
  omega

theorem entries_bounded : Q.EntriesBounded (2 ^ Q.inputSize) := by
  have h := Q.scalars.entries_bounded
  have hp : 2 ^ Q.scalars.inputSize ≤ 2 ^ Q.inputSize :=
    Nat.pow_le_pow_right (by decide) Q.scalar_size_le
  have hc : ∀ j, (Q.scalars.c j).num.natAbs ≤ 2 ^ Q.inputSize ∧
      (Q.scalars.c j).den ≤ 2 ^ Q.inputSize :=
    fun j ↦ ⟨((h.2.2 j).1.trans hp), ((h.2.2 j).2.trans hp)⟩
  refine ⟨fun w ↦ ?_, fun e ↦ ?_, fun e ↦ ?_⟩
  · simpa only [scalars, Fin.append_left] using hc (Fin.castAdd (n + n) w)
  · simpa only [scalars, Fin.append_right, Fin.append_left] using
      hc (Fin.natAdd v (Fin.castAdd n e))
  · simpa only [scalars, Fin.append_right] using hc (Fin.natAdd v (Fin.natAdd n e))

theorem reduced_rows_le (D : Q.toNetwork.RowDeletion m c) : m ≤ v := by
  have hinj : Function.Injective (fun i : Fin m ↦ (D.rows i).val) :=
    Subtype.val_injective.comp D.rows.injective
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj

end WolfeSimplex.RationalNetwork

import WolfeSimplex.Proofs.NetworkPreparation
import WolfeSimplex.Proofs.Corollary4Resources

set_option maxRecDepth 8000
set_option exponentiation.threshold 1024

namespace WolfeSimplex.RationalNetwork
open Finset
variable {v n m c : ℕ} (Q : RationalNetwork v n) (D : Q.toNetwork.RowDeletion m c)

/-- Actual interpreted bit work for dense network conversion and the initial
support. This is measured execution cost, not an assigned polynomial charge. -/
def preparationCost (S : BoundedLP.State n) : ℕ := Q.executedPreparationCost D S

def reductionCost (S : BoundedLP.State n) : ℕ := Q.preparationCost D S +
  PaperCorollary4.Resources.countCost (Q.standard D)

theorem reductionCost_bound (S : BoundedLP.State n) (hn : 1 ≤ n) :
    Q.reductionCost D S ≤ 10 ^ 301 * (1 + Q.inputSize) ^ 200 := by
  have hr := Q.reduced_rows_le D
  have hd := Q.dimensions_le
  have hdata := Q.standard_entries D (2 ^ Q.inputSize)
    (Nat.one_le_pow _ _ (by decide)) Q.entries_bounded
  have hp := (PaperCorollary4.Resources.pipelines (Q.standard D) (by omega)
    (fun _ ↦ Fin.last (n + n)) Q.inputSize hdata).1
  have hshape : (m + n) + (n + n) + Q.inputSize + 3 ≤ 4 * (1 + Q.inputSize) := by omega
  have hpc : PaperCorollary4.Resources.countCost (Q.standard D) ≤
      (10 ^ 100 * 4 ^ 200) * (1 + Q.inputSize) ^ 200 := by
    calc _ ≤ 10 ^ 100 * ((m + n) + (n + n) + Q.inputSize + 3) ^ 200 := hp
         _ ≤ 10 ^ 100 * (4 * (1 + Q.inputSize)) ^ 200 :=
           Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hshape _)
         _ = _ := by rw [mul_pow, Nat.mul_assoc]
  have hprep : Q.preparationCost D S ≤ 10 ^ 31 * (1 + Q.inputSize) ^ 200 := by
    have hp20 : (1 + Q.inputSize) ^ 20 ≤ (1 + Q.inputSize) ^ 200 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    exact (Q.executedPreparationCost_bound D S).trans (Nat.mul_le_mul_left _ hp20)
  calc Q.reductionCost D S ≤ (10 ^ 31 + 10 ^ 100 * 4 ^ 200) * (1 + Q.inputSize) ^ 200 := by
        unfold reductionCost
        rw [Nat.add_mul]
        exact Nat.add_le_add hprep hpc
       _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

end WolfeSimplex.RationalNetwork

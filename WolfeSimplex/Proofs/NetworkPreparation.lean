import WolfeSimplex.Execution.NetworkBounds
import WolfeSimplex.Execution.NetworkMask

/-! The preprocessing cost is the interpreter's measured bit work, including
construction of the actual initial support. No polynomial report is supplied
as an input or substituted for an executed program. -/
namespace WolfeSimplex.RationalNetwork
open Execution
variable {v n m c : ℕ} (Q : RationalNetwork v n) (D : Q.toNetwork.RowDeletion m c)

def executedPreparationCost (S : BoundedLP.State n) : ℕ :=
  (Network.code v m n).bitWork (Network.input Q D) +
    (Network.maskCode n).bitWork (Network.maskInput S)

theorem executedPreparationCost_bound (S : BoundedLP.State n) :
    Q.executedPreparationCost D S ≤ 10 ^ 31 * (1 + Q.inputSize) ^ 20 := by
  have hg := Network.code_bitWork Q D
  have hm := Network.mask_bitWork S
  have hd := Q.dimensions_le
  have hn : n + 1 ≤ 1 + Q.inputSize := by omega
  have h6 : (1 + Q.inputSize) ^ 6 ≤ (1 + Q.inputSize) ^ 20 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hm' : (Network.maskCode n).bitWork (Network.maskInput S) ≤
      10 ^ 12 * (1 + Q.inputSize) ^ 20 :=
    hm.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hn _).trans h6))
  calc Q.executedPreparationCost D S ≤
        (10 ^ 30 + 10 ^ 12) * (1 + Q.inputSize) ^ 20 := by
          unfold executedPreparationCost
          rw [Nat.add_mul]
          exact Nat.add_le_add hg hm'
       _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

/-- Native network preprocessing produces exactly the rational standard LP
and initial Wolfe support used in the count correspondence, in polynomial
measured bit work. The source flow/run is not inspected. -/
theorem preparation_certificate (S : BoundedLP.State n) :
    (Network.code v m n).eval (Network.input Q D) = Network.raw (Q.standard D) ∧
    (Network.maskCode n).eval (Network.maskInput S) =
      List.ofFn (fun j : Fin (n + n + 2) ↦
        if j ∈ hat (hat S.basis) then (1 : ℤ) else 0) ∧
    Q.executedPreparationCost D S ≤ 10 ^ 31 * (1 + Q.inputSize) ^ 20 :=
  ⟨Network.correct Q D, Network.mask_correct S, Q.executedPreparationCost_bound D S⟩

end WolfeSimplex.RationalNetwork

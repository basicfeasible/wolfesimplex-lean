import WolfeSimplex.Proofs.NetworkPreparation
import WolfeSimplex.AxiomAudit

/-! Execute preprocessing with permuted retained rows, a self-loop, negative
and positive incidence entries, nontrivial denominators and an upper-bound arc. -/
namespace WolfeSimplex.NetworkPreparationCheck
open Execution Execution.Network Finset

private def net : RationalNetwork 3 3 where
  tail := ![0, 0, 1]
  head := ![1, 0, 2]
  supply := ![-2/3, 2/5, 4/15]
  cost := ![-1/5, 0, 2/7]
  capacity := ![4/3, 1, 1/11]

private def deletion : net.toNetwork.RowDeletion 2 1 :=
  { net.deleteLast with rows :=
    (Equiv.swap (0 : Fin 2) 1).trans net.deleteLast.rows }

private def initial : BoundedLP.State 3 where
  tree := {0}
  atUpper := {2}
  flow := 0

#guard ((input net deletion)[8]?.getD []) == [1, 0]
#guard ((code 3 2 3).eval (input net deletion)).take 30 ==
  [1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0,
   1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1]
#guard (((code 3 2 3).eval (input net deletion)).drop 30).take 30 == List.replicate 30 1
#guard (((code 3 2 3).eval (input net deletion)).drop 60).take 5 == [2, -2, 4, 1, 1]
#guard (((code 3 2 3).eval (input net deletion)).drop 65).take 5 == [5, 3, 3, 1, 11]
#guard (((code 3 2 3).eval (input net deletion)).drop 70).take 6 == [-1, 0, 2, 0, 0, 0]
#guard ((code 3 2 3).eval (input net deletion)).drop 76 == [5, 1, 7, 1, 1, 1]
#guard ((code 3 2 3).run (input net deletion)).peak == 15
#guard (maskCode 3).eval (maskInput initial) == [1, 0, 1, 1, 1, 0, 1, 1]
#guard ((maskCode 3).run (maskInput initial)).peak == 1

example : (code 3 2 3).eval (input net deletion) = raw (net.standard deletion) :=
  (net.preparation_certificate deletion initial).1

example : net.executedPreparationCost deletion initial ≤
    10 ^ 31 * (1 + net.inputSize) ^ 20 :=
  (net.preparation_certificate deletion initial).2.2

end WolfeSimplex.NetworkPreparationCheck

run_cmd WolfeSimplex.Audit.project

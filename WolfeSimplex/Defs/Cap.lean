import WolfeSimplex.Defs.Induced

/-!
# The cap constraint (paper: Appendix C.2 (`app:cor-rules`) (cap argument))

Trusted definition of the capped LP of Appendix C.2 (`app:cor-rules`) (cap argument): for an LP with
integer data whose
absolute values are at most `U`, add a variable `x_cap` with cost `0` and the constraint
`1ᵀx + x_cap = m(mU)^m + 1`.

## Conventions

* The new variable `x_cap` is the label `Fin.last n`; the original label `k` is
  `Fin.castSucc k`. So for a label set `B ⊆ [n]`, the set `B ∪ {cap}` is `hat B`
  (`Defs/Induced.lean`).
* The new constraint is the last row `Fin.last m`; row `Fin.castSucc i` is row `i` of `A`,
  with the entry `0` in the column of `x_cap`.
* `U` is `IntLP.U` (the largest absolute value of an entry of `A` or `b`, at least `1`).
-/

namespace WolfeSimplex

namespace IntLP

variable {m n : ℕ} (P : IntLP m n)

/-- The bound `M = m (mU)^m` on `1ᵀx^B` for the basic solutions `x^B` (paper: Appendix C.2
(`app:cor-rules`) (cap argument)). -/
def capBound : ℕ := m * (m * P.U) ^ m

/-- The capped LP (paper: Appendix C.2 (`app:cor-rules`) (cap argument)): the variable `x_cap`
(label `Fin.last n`, cost
`0`, entry `0` in the old rows) and the constraint `1ᵀx + x_cap = M + 1` (last row
`Fin.last m`) are added. -/
def cap : IntLP (m + 1) (n + 1) where
  A := Matrix.of fun r k ↦
    Fin.snoc (α := fun _ ↦ Fin (n + 1) → ℤ)
      (fun i ↦ Fin.snoc (α := fun _ ↦ ℤ) (fun k' ↦ P.A i k') 0)
      (fun _ ↦ 1)
      r k
  b := Fin.snoc (α := fun _ ↦ ℤ) P.b ((P.capBound : ℤ) + 1)
  c := Fin.snoc (α := fun _ ↦ ℤ) P.c 0

end IntLP

end WolfeSimplex

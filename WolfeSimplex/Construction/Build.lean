import WolfeSimplex.Construction.Cost
import WolfeSimplex.Proofs.BitSize

/-!
# Executable integer construction

Scalar constants and finite tables are cached before the output is materialized.
No real arithmetic, choice, admissibility decision or LP solver is executed.
-/

namespace WolfeSimplex.Construction

open Finset WolfeSimplex.Construction.Computation
variable {m n : ℕ}

/-- Dense input entries whose absolute maximum defines `U`. -/
def constraintData (P : IntLP m n) : List ℤ :=
  (List.ofFn fun i : Fin m ↦ List.ofFn fun j : Fin n ↦ P.A i j).flatten ++ List.ofFn P.b

/-- Six cell/control charges per dense input entry, including list materialization. -/
def uScan (P : IntLP m n) :=
  materialize (6 * (m * n + m + 1)) (maxAbs (constraintData P))
def cScan (P : IntLP m n) :=
  materialize (4 * (n + 1)) (scanMax (List.ofFn P.c))

def gammaTable (P : IntLP m n) (c : ℤ) : Computation (Vector ℤ (n + 1)) :=
  table fun j ↦ add c (Fin.snoc (α := fun _ ↦ ℤ) P.c 0 j)

def alphaTable (P : IntLP m n) (t : ℤ) :
    Computation (Vector (Vector ℤ m) (n + 1)) :=
  table fun j ↦ table fun i ↦ do
    let ta ← mul t (Fin.snoc (α := fun _ ↦ ℤ) (fun k ↦ P.A i k) 0 j)
    sub ta (P.b i)

def kScan (g : Vector ℤ (n + 1)) (a : Vector (Vector ℤ m) (n + 1)) :=
  materialize (6 * (n + 1) * (m + 1))
    (maxAbs (g.toList ++ (a.toList.map Vector.toList).flatten))

/-- Compute and materialize all `(n+1)(m+1)` integer atom coordinates. -/
def run (P : IntLP m n) : Computation (Vector (Vector ℤ (m + 1)) (n + 1)) := do
  let u ← uScan P
  let cmax ← cScan P
  let c ← add 1 cmax
  let twom ← mul 2 m
  let mu ← mul m u
  let mupow ← power mu m
  let tprod ← mul twom mupow
  let t ← add tprod 1
  let g ← gammaTable P c
  let a ← alphaTable P t
  let k ← kScan g a
  let ksq ← mul k k
  let hbase ← mul (m + 1 : ℕ) ksq
  let h ← power hbase (m + 1)
  let hcube ← power h 3
  let q ← mul twom hcube
  let nn ← mul q t
  let factor ← mul nn q
  table fun j ↦ table fun i ↦
    Fin.cases (mul nn g[j]) (fun r ↦ mul factor a[j][r]) i

/-- Integer output of the construction, projected from its resource annotations. -/
def atoms (P : IntLP m n) : Vector (Vector ℤ (m + 1)) (n + 1) := (run P).value

end WolfeSimplex.Construction

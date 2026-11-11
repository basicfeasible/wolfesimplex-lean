import WolfeSimplex.Defs.Rules

/-!
# Capacitated flow LPs and their bounded-variable simplex states

For a network, `A` is its incidence matrix after one conservation row per
component has been deleted. A spanning forest gives a basis of this reduced
matrix. The conversion results also hold for any matrix with such a basis.

The network simplex method keeps every non-tree arc at zero or at capacity.
An improving arc releases its active bound; augmentation follows its fundamental
direction until a new bound is reached. This includes a bound flip on the
entering arc. These definitions describe that bounded-variable algorithm before
conversion to the ordinary nonnegative-variable simplex method.
-/

namespace WolfeSimplex

open Finset Matrix

/-- A capacitated LP `min cᵀx`, `Ax = b`, `0 ≤ x ≤ u`. -/
structure BoundedLP (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ
  u : Fin n → ℝ

namespace BoundedLP

variable {m n : ℕ}

def toLP (P : BoundedLP m n) : LP m n := ⟨P.A, P.b, P.c⟩

def IsFeasible (P : BoundedLP m n) (x : Fin n → ℝ) : Prop :=
  P.A *ᵥ x = P.b ∧ ∀ j, 0 ≤ x j ∧ x j ≤ P.u j

/-- Original-variable and capacity-slack labels. -/
def lower (j : Fin n) : Fin (n + n) := Fin.castAdd n j
def upper (j : Fin n) : Fin (n + n) := Fin.natAdd n j

/-- Add one capacity slack per arc: `Ax = b`, `x + s = u`. -/
def standard (P : BoundedLP m n) : LP (m + n) (n + n) where
  A := fun r j ↦ Fin.addCases
    (fun i ↦ Fin.addCases (fun k ↦ P.A i k) (fun _ ↦ 0) j)
    (fun i ↦ Fin.addCases (fun k ↦ if i = k then 1 else 0)
      (fun k ↦ if i = k then 1 else 0) j) r
  b := Fin.append P.b P.u
  c := Fin.append P.c 0

def lift (P : BoundedLP m n) (x : Fin n → ℝ) : Fin (n + n) → ℝ :=
  Fin.append x (P.u - x)

def liftDir (d : Fin n → ℝ) : Fin (n + n) → ℝ := Fin.append d (-d)

structure State (n : ℕ) where
  tree : Finset (Fin n)
  atUpper : Finset (Fin n)
  flow : Fin n → ℝ

namespace State

/-- Active nonnegativity/capacity bounds, indexed by the associated slack in
standard form: a lower bound has label `lower j`, an upper bound `upper j`. -/
def activeBounds (S : State n) : Finset (Fin (n + n)) :=
  ((univ \ (S.tree ∪ S.atUpper)).map (Fin.castAddEmb n)) ∪
    S.atUpper.map (Fin.natAddEmb n)

/-- The basis asserted in the paper: tree arcs have both variables basic;
upper non-tree arcs have their original variable basic; the other non-tree
arcs have their capacity slack basic. -/
def basis (S : State n) : Finset (Fin (n + n)) := univ \ S.activeBounds

def entering (S : State n) (j : Fin n) : Fin (n + n) :=
  if j ∈ S.atUpper then upper j else lower j

end State

def IsState (P : BoundedLP m n) (S : State n) : Prop :=
  P.toLP.IsBasis S.tree ∧ Disjoint S.tree S.atUpper ∧ P.IsFeasible S.flow ∧
    ∀ j ∉ S.tree, S.flow j = if j ∈ S.atUpper then P.u j else 0

def IsNondegenerate (P : BoundedLP m n) (S : State n) : Prop :=
  ∀ j ∈ S.tree, 0 < S.flow j ∧ S.flow j < P.u j

def sign (S : State n) (j : Fin n) : ℝ := if j ∈ S.atUpper then -1 else 1

noncomputable def direction (P : BoundedLP m n) (S : State n) (j : Fin n) : Fin n → ℝ :=
  sign S j • P.toLP.basicDir S.tree j

noncomputable def reducedCost (P : BoundedLP m n) (S : State n) (j : Fin n) : ℝ :=
  sign S j * P.toLP.reducedCost S.tree j

def IsImproving (P : BoundedLP m n) (S : State n) (j : Fin n) : Prop :=
  j ∉ S.tree ∧ P.reducedCost S j < 0

/-- Dantzig chooses an improving non-tree arc of greatest absolute reduced
cost; an upper arc improves by decreasing its flow. -/
def IsDantzigChoice (P : BoundedLP m n) (S : State n) (j : Fin n) : Prop :=
  P.IsImproving S j ∧ ∀ k, P.IsImproving S k →
    |P.toLP.reducedCost S.tree k| ≤ |P.toLP.reducedCost S.tree j|

/-- The minimum ratio over all bounds met in the augmentation direction.
For a lower bound the residual is `x_i` and its slope is `d_i`; for an upper
bound they are `u_i - x_i` and `-d_i`. -/
noncomputable def IsLeavingBound (P : BoundedLP m n) (S : State n) (j : Fin n)
    (l : Fin (n + n)) : Prop :=
  liftDir (P.direction S j) l < 0 ∧
    ∀ k, liftDir (P.direction S j) k < 0 →
      P.lift S.flow l / (-liftDir (P.direction S j) l) ≤
        P.lift S.flow k / (-liftDir (P.direction S j) k)

/-- One augmentation releases the entering arc's bound and activates the first
new bound. The flow moves by the corresponding ratio-test step. -/
noncomputable def IsPivot (P : BoundedLP m n) (S : State n) (j : Fin n) (S' : State n) : Prop :=
  P.IsImproving S j ∧ ∃ l, P.IsLeavingBound S j l ∧
    S'.activeBounds = insert l (S.activeBounds.erase (S.entering j)) ∧
    S'.flow = S.flow +
      (P.lift S.flow l / (-liftDir (P.direction S j) l)) • P.direction S j

noncomputable def IsDantzigRun (P : BoundedLP m n) (f : ℕ) (S : ℕ → State n) : Prop :=
  (∀ k ≤ f, P.IsState (S k)) ∧
    (∀ k < f, ∃ j, P.IsDantzigChoice (S k) j ∧ P.IsPivot (S k) j (S (k + 1))) ∧
    ∀ j, ¬ P.IsImproving (S f) j

end BoundedLP
end WolfeSimplex

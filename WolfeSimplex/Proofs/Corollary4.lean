import WolfeSimplex.Proofs.Corollary4Queries
import WolfeSimplex.Proofs.Corollary4NetworkResources

/-!
# Corollary 4: polynomial reductions for linopt

The external inputs are the Fearnley--Savani PSPACE-hard queried-label families
(Theorems 1.1/1.2, robust to tie resolution) and the Disser--Skutella NP-hard
network-simplex counting family. Their proofs and a Turing-machine definition
of NP/PSPACE are outside this development. Here the reductions, event equivalences,
exact counts, initialization and uniform binary resource bounds are proved.
In particular, neither a Wolfe hardness claim nor a polynomial bound on the
new reduction is an input premise.
-/
namespace WolfeSimplex.PaperCorollary4
open Finset Wolfe Efficiency

inductive QueryMode where
  | ever
  | final
  deriving DecidableEq

def sourceEvent {m n : ℕ} (mode : QueryMode) (P : LP m n) (f : ℕ)
    (B : ℕ → Finset (Fin n)) (j : Fin n) : Prop :=
  match mode with
  | .ever => ∃ k < f, P.IsPivot (B k) j (B (k + 1))
  | .final => j ∈ B f

def targetEvent {N D : ℕ} (mode : QueryMode) (p : Fin N → Fin D → ℝ) (f : ℕ)
    (S : ℕ → Finset (Fin N)) (j : Fin N) : Prop :=
  match mode with
  | .ever => ∃ k < f, MajorCycle p (S k) j (S (k + 1))
  | .final => j ∈ S f

structure QueryInstance where
  rows : ℕ
  cols : ℕ
  input : QueryInput rows cols
  queried : Fin cols

namespace QueryInstance
variable (x : QueryInstance)

abbrev label : Fin (x.cols + 3) := x.queried.castSucc.castSucc.castSucc

def targetQuestion (mode : QueryMode) : Prop :=
  ∃ g S, IsWolfeRunWith x.input.target.atom (IsIndexLinoptChoice x.input.target.atom) g S ∧
    S 0 = {Fin.last (x.cols + 2)} ∧ targetEvent mode x.input.target.atom g S x.label

def sourceCorrect (mode : QueryMode) (answer : Prop) : Prop :=
  ∀ f B, x.input.lp.toLP.IsSimplexRunWith x.input.lp.toLP.IsDantzigChoice f B →
    B 0 = basisOf x.input.initial →
    (sourceEvent mode x.input.lp.toLP f B x.queried ↔ answer)

theorem rows_positive : 1 ≤ x.rows := by
  have := (x.input.owner x.queried).isLt
  omega

/-- The actual target question, with a fixed index tie rule, has exactly the
source answer. For BasisEntry the queried variable must initially be nonbasic;
the final-basis question has no such restriction. -/
theorem answer_transfer (mode : QueryMode)
    (hvalid : mode = .ever → x.queried ∉ basisOf x.input.initial)
    (answer : Prop) (hexternal : x.sourceCorrect mode answer) :
    x.targetQuestion mode ↔ answer := by
  have hall : ∀ g S,
      IsWolfeRunWith x.input.target.atom (IsIndexLinoptChoice x.input.target.atom) g S →
      S 0 = {Fin.last (x.cols + 2)} →
      (targetEvent mode x.input.target.atom g S x.label ↔ answer) := by
    intro g S hS h0
    have hlin := index_run_is_linopt hS
    cases mode with
    | ever =>
      obtain ⟨B, hB, hB0, he, _⟩ := x.input.queries x.queried (hvalid rfl) g S hlin h0
      exact he.trans (hexternal _ B hB hB0)
    | final =>
      obtain ⟨hg, _, B, hB, hB0, hSB⟩ := x.input.trace g S hlin h0
      have he := hSB (g - (x.rows + 2)) le_rfl
      rw [show x.rows + 2 + (g - (x.rows + 2)) = g by omega] at he
      change x.label ∈ S g ↔ answer
      rw [he]
      simpa only [label, IntLP.castSucc_mem_hat, sourceEvent] using hexternal _ B hB hB0
  constructor
  · rintro ⟨g, S, hS, h0, he⟩; exact (hall g S hS h0).1 he
  · intro ha
    obtain ⟨g, S, hS, h0⟩ := exists_index_run x.input.target.atom
      {Fin.last (x.cols + 2)} ((wolfe_well_defined_main _).1 _)
    exact ⟨g, S, hS, h0, (hall g S hS h0).2 ha⟩

def reductionCost : ℕ := Resources.queryCost x.input.lp (capEnum x.input.initial)

theorem reductionCost_bound :
    x.reductionCost ≤ 10 ^ 400 * (1 + x.input.lp.inputSize) ^ 200 :=
  (Resources.binary_pipelines x.input.lp x.rows_positive (capEnum x.input.initial)).2

/-- The entire queried-label reduction, including the unique shortest start.
The sole answer premise concerns rational source simplex runs. -/
theorem certificate (mode : QueryMode)
    (hvalid : mode = .ever → x.queried ∉ basisOf x.input.initial)
    (answer : Prop) (hexternal : x.sourceCorrect mode answer) :
    (∀ j k, ∃ z : ℤ, x.input.target.atom j k = z) ∧
    (∀ j ≠ Fin.last (x.cols + 2),
      normSq (x.input.target.atom (Fin.last (x.cols + 2))) < normSq (x.input.target.atom j)) ∧
    (x.targetQuestion mode ↔ answer) ∧
    x.reductionCost ≤ 10 ^ 400 * (1 + x.input.lp.inputSize) ^ 200 :=
  ⟨x.input.target_integer, x.input.unique_shortest,
    x.answer_transfer mode hvalid answer hexternal, x.reductionCost_bound⟩

end QueryInstance

/-- Native network input and the promises of the cited hard family. The run
itself is only an existential proof: the reduction reads the network and the
initial tree/bound sets, never the source run or its unknown length. -/
structure NetworkInput where
  vertices : ℕ
  arcs : ℕ
  rows : ℕ
  components : ℕ
  network : RationalNetwork vertices arcs
  deletion : network.toNetwork.RowDeletion rows components
  initial : BoundedLP.State arcs
  nonempty : 1 ≤ arcs
  balanced : deletion.Balanced
  capacity : ∀ e, 0 < (network.capacity e : ℝ)
  execution : ∃ f S, deletion.IsDantzigRun f S ∧ S 0 = initial ∧
    (∀ k ≤ f, ∀ e ∈ (S k).tree, 0 < (S k).flow e ∧
      (S k).flow e < (network.capacity e : ℝ)) ∧
    (∀ k < f, ∀ j j', network.toNetwork.IsDantzigChoice (S k) j →
      network.toNetwork.IsDantzigChoice (S k) j' → j = j')

namespace NetworkInput
variable (x : NetworkInput)

noncomputable def points := (x.network.target x.deletion).atom
def start := hat (hat x.initial.basis)

def IsTargetCount (f : ℕ) : Prop :=
  ∃ S, IsWolfeRunWith x.points (IsIndexLinoptChoice x.points) f S ∧ S 0 = x.start

/-- Exact many-one counting transfer for any run satisfying the native DS18
promises. Every complete fixed-index target run has this count, and at least
one such run exists. Bound flips are included in the native pivot definition. -/
theorem count_transfer (f : ℕ) (S : ℕ → BoundedLP.State x.arcs)
    (hS : x.deletion.IsDantzigRun f S) (h0 : S 0 = x.initial)
    (hnd : ∀ k ≤ f, ∀ e ∈ (S k).tree, 0 < (S k).flow e ∧
      (S k).flow e < (x.network.capacity e : ℝ))
    (hu : ∀ k < f, ∀ j j', x.network.toNetwork.IsDantzigChoice (S k) j →
      x.network.toNetwork.IsDantzigChoice (S k) j' → j = j') :
    x.IsTargetCount f ∧ ∀ g, x.IsTargetCount g → g = f := by
  have ht := x.network.count_transfer x.deletion f S x.balanced hS x.capacity hnd hu
  have hcor : IsCorral x.points x.start := by
    have hc := ht.1.1.1 0 (Nat.zero_le _)
    simpa only [points, start, h0] using hc
  obtain ⟨g, T, hT, hT0⟩ := exists_index_run x.points x.start hcor
  have hlen : g = f := (ht.2 g T (index_run_is_linopt hT) (by
    simpa only [start, h0] using hT0)).1
  refine ⟨hlen ▸ ⟨T, hT, hT0⟩, ?_⟩
  rintro g ⟨T, hT, hT0⟩
  exact (ht.2 g T (index_run_is_linopt hT) (by simpa only [start, h0] using hT0)).1

theorem count_exists_unique : ∃! f, x.IsTargetCount f := by
  obtain ⟨f, S, hS, h0, hnd, hu⟩ := x.execution
  obtain ⟨hf, hu⟩ := x.count_transfer f S hS h0 hnd hu
  exact ⟨f, hf, hu⟩

def reductionCost := x.network.reductionCost x.deletion x.initial

theorem reductionCost_bound :
    x.reductionCost ≤ 10 ^ 301 * (1 + x.network.inputSize) ^ 200 :=
  x.network.reductionCost_bound x.deletion x.initial x.nonempty

/-- Executed preprocessing produces exactly the rational LP and starting
support used by the mathematical reduction, within the measured bit budget. -/
theorem preprocessing_certificate :
    (Execution.Network.code x.vertices x.rows x.arcs).eval
      (Execution.Network.input x.network x.deletion) =
        Execution.Network.raw (x.network.standard x.deletion) ∧
    (Execution.Network.maskCode x.arcs).eval (Execution.Network.maskInput x.initial) =
      List.ofFn (fun j : Fin (x.arcs + x.arcs + 2) ↦
        if j ∈ x.start then (1 : ℤ) else 0) ∧
    x.reductionCost ≤ 10 ^ 301 * (1 + x.network.inputSize) ^ 200 :=
  ⟨(x.network.preparation_certificate x.deletion x.initial).1,
    (x.network.preparation_certificate x.deletion x.initial).2.1, x.reductionCost_bound⟩

/-- The count reduction produces `2n+2` integer points in `m+n+2`
dimensions, starts at a corral, and has polynomial binary construction cost. -/
theorem certificate :
    (∀ j k, ∃ z : ℤ, x.points j k = z) ∧ IsCorral x.points x.start ∧
    (∃! f, x.IsTargetCount f) ∧
    x.reductionCost ≤ 10 ^ 301 * (1 + x.network.inputSize) ^ 200 := by
  obtain ⟨f, S, hS, h0, hnd, hu⟩ := x.execution
  have ht := x.network.count_transfer x.deletion f S x.balanced hS x.capacity hnd hu
  exact ⟨(x.network.target x.deletion).atom_integral,
    by simpa only [points, start, h0] using ht.1.1.1 0 (Nat.zero_le _),
    x.count_exists_unique, x.reductionCost_bound⟩

end NetworkInput

/-- Polynomial reductions compose with the source constructions in the cited
hardness theorems. Their size bounds are external; the Wolfe reduction's cost
bound is derived here and is not an external hypothesis. -/
theorem query_family_polynomial {X : Type} (size : X → ℕ) (family : X → QueryInstance)
    (hs : PolynomialBound size (fun x ↦ (family x).input.lp.inputSize)) :
    PolynomialBound size (fun x ↦ (family x).reductionCost) :=
  (show PolynomialBound (fun x : QueryInstance ↦ x.input.lp.inputSize)
    QueryInstance.reductionCost from ⟨10 ^ 400, 200, QueryInstance.reductionCost_bound⟩).comp family hs

theorem count_family_polynomial {X : Type} (size : X → ℕ) (family : X → NetworkInput)
    (hs : PolynomialBound size (fun x ↦ (family x).network.inputSize)) :
    PolynomialBound size (fun x ↦ (family x).reductionCost) :=
  (show PolynomialBound (fun x : NetworkInput ↦ x.network.inputSize)
    NetworkInput.reductionCost from ⟨10 ^ 301, 200, NetworkInput.reductionCost_bound⟩).comp family hs

/-- Corollary 4(a,b), with FS15's source correctness and polynomial family
size as explicit premises. This is the many-one reduction for either queried
event, with a single fixed index tie rule on every Wolfe input. -/
theorem corollary4_queries {X : Type} (size : X → ℕ) (problem : X → Prop)
    (family : X → QueryInstance) (mode : QueryMode)
    (hsize : PolynomialBound size (fun x ↦ (family x).input.lp.inputSize))
    (hvalid : ∀ x, mode = .ever →
      (family x).queried ∉ basisOf (family x).input.initial)
    (hFS15 : ∀ x, (family x).sourceCorrect mode (problem x)) :
    (∀ x, (family x).targetQuestion mode ↔ problem x) ∧
      PolynomialBound size (fun x ↦ (family x).reductionCost) :=
  ⟨fun x ↦ (family x).answer_transfer mode (hvalid x) (problem x) (hFS15 x),
    query_family_polynomial size family hsize⟩

/-- Corollary 4(c), with the native DS18 run and its source counting answer
as explicit premises. The new integer-point reduction and its bit bound are
proved, rather than included among the literature hypotheses. -/
theorem corollary4_count {X : Type} (size : X → ℕ) (problem : X → ℕ)
    (family : X → NetworkInput)
    (hsize : PolynomialBound size (fun x ↦ (family x).network.inputSize))
    (hDS18 : ∀ x, ∃ S, (family x).deletion.IsDantzigRun (problem x) S ∧
      S 0 = (family x).initial ∧
      (∀ k ≤ problem x, ∀ e ∈ (S k).tree, 0 < (S k).flow e ∧
        (S k).flow e < ((family x).network.capacity e : ℝ)) ∧
      (∀ k < problem x, ∀ j j',
        (family x).network.toNetwork.IsDantzigChoice (S k) j →
        (family x).network.toNetwork.IsDantzigChoice (S k) j' → j = j')) :
    (∀ x f, (family x).IsTargetCount f ↔ f = problem x) ∧
      PolynomialBound size (fun x ↦ (family x).reductionCost) := by
  refine ⟨?_, count_family_polynomial size family hsize⟩
  intro x f
  obtain ⟨S, hS, h0, hnd, hu⟩ := hDS18 x
  obtain ⟨hc, he⟩ := (family x).count_transfer (problem x) S hS h0 hnd hu
  exact ⟨he f, fun h ↦ h ▸ hc⟩

end WolfeSimplex.PaperCorollary4

import WolfeSimplex.Proofs.Corollary4
import WolfeSimplex.Execution.InfiniteCapacity

/-! Corollary 4 directly from native source networks with absent upper bounds.
Finite replacement, preservation of the source run and the complete polynomial
preprocessing bound are derived here, not assumed from DS18. -/
namespace WolfeSimplex.PaperCorollary4
open Finset Wolfe Efficiency

structure ExtendedNetworkInput where
  vertices : ℕ
  arcs : ℕ
  rows : ℕ
  components : ℕ
  network : ExtendedNetwork vertices arcs
  deletion : network.data.toNetwork.RowDeletion rows components
  initial : BoundedLP.State arcs
  nonempty : 1 ≤ arcs
  balanced : deletion.Balanced
  terminal : network.Terminal
  capacity : ∀ e ∉ network.infinite, 0 < (network.data.capacity e : ℝ)
  execution : ∃ f S, network.IsDantzigRun deletion f S ∧ S 0 = initial ∧
    (∀ k ≤ f, network.IsNondegenerate (S k)) ∧
    (∀ k < f, ∀ j j', network.data.toNetwork.IsDantzigChoice (S k) j →
      network.data.toNetwork.IsDantzigChoice (S k) j' → j = j')

namespace ExtendedNetworkInput
variable (x : ExtendedNetworkInput)

theorem normalized_execution : ∃ f S,
    (x.network.deletion x.deletion).IsDantzigRun f S ∧ S 0 = x.initial ∧
    (∀ k ≤ f, ∀ e ∈ (S k).tree, 0 < (S k).flow e ∧
      (S k).flow e < (x.network.finite.capacity e : ℝ)) ∧
    (∀ k < f, ∀ j j', x.network.finite.toNetwork.IsDantzigChoice (S k) j →
      x.network.finite.toNetwork.IsDantzigChoice (S k) j' → j = j') := by
  obtain ⟨f, S, hS, h0, hnd, hu⟩ := x.execution
  exact ⟨f, S, x.network.run_to_finite x.deletion x.terminal f S hS, h0,
    fun k hk ↦ x.network.nondegenerate_to_finite x.deletion x.terminal _ (hS.1 k hk) (hnd k hk),
    hu⟩

/-- Every field of the old finite-capacity interface is discharged from the
native uncapacitated source. In particular its run is proved, not supplied. -/
def normalize : NetworkInput where
  vertices := x.vertices
  arcs := x.arcs
  rows := x.rows
  components := x.components
  network := x.network.finite
  deletion := x.network.deletion x.deletion
  initial := x.initial
  nonempty := x.nonempty
  balanced := x.network.balanced x.deletion x.balanced
  capacity := x.network.finite_positive x.capacity
  execution := x.normalized_execution

def inputSize : ℕ := x.network.inputSize

def normalizationCost : ℕ :=
  (Execution.InfiniteCapacity.code x.vertices x.arcs).bitWork
    (Execution.InfiniteCapacity.input x.network)

def reductionCost : ℕ := x.normalizationCost + x.normalize.reductionCost

theorem count_transfer (f : ℕ) (S : ℕ → BoundedLP.State x.arcs)
    (hS : x.network.IsDantzigRun x.deletion f S) (h0 : S 0 = x.initial)
    (hnd : ∀ k ≤ f, x.network.IsNondegenerate (S k))
    (hu : ∀ k < f, ∀ j j', x.network.data.toNetwork.IsDantzigChoice (S k) j →
      x.network.data.toNetwork.IsDantzigChoice (S k) j' → j = j') :
    x.normalize.IsTargetCount f ∧ ∀ g, x.normalize.IsTargetCount g → g = f :=
  x.normalize.count_transfer f S
    (x.network.run_to_finite x.deletion x.terminal f S hS) h0
    (fun k hk ↦ x.network.nondegenerate_to_finite x.deletion x.terminal _ (hS.1 k hk) (hnd k hk)) hu

/-- The numeric arrays consumed by the old reduction are exactly the executed
normalization's output. Endpoints, supplies, costs and retained rows are shared. -/
theorem normalization_correct :
    (Execution.InfiniteCapacity.code x.vertices x.arcs).eval
      (Execution.InfiniteCapacity.input x.network) =
        List.ofFn (fun e ↦ (x.normalize.network.capacity e).num) ++
          List.ofFn (fun e ↦ ((x.normalize.network.capacity e).den : ℤ)) :=
  Execution.InfiniteCapacity.correct x.network

/-- Both charges are interpreted program costs. Their polynomial bound follows
by composing the normalized binary input-size bound with the existing pipeline. -/
theorem construction_polynomial :
    PolynomialBound inputSize reductionCost := by
  have hn : PolynomialBound inputSize normalizationCost :=
    ⟨10 ^ 30, 12, fun x ↦ Execution.InfiniteCapacity.code_bitWork x.network⟩
  have hs : PolynomialBound inputSize (fun x ↦ x.normalize.network.inputSize) :=
    ⟨10 ^ 6, 3, fun x ↦ x.network.finite_inputSize⟩
  have hc : PolynomialBound (fun y : NetworkInput ↦ y.network.inputSize)
      NetworkInput.reductionCost := ⟨10 ^ 301, 200, NetworkInput.reductionCost_bound⟩
  exact hn.add (hc.comp normalize hs)

theorem certificate :
    (∀ j k, ∃ z : ℤ, x.normalize.points j k = z) ∧
    IsCorral x.normalize.points x.normalize.start ∧
    (∃! f, x.normalize.IsTargetCount f) := by
  have h := x.normalize.certificate
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end ExtendedNetworkInput

/-- The count reduction including native infinite-capacity normalization. The
only source promises concern DS18's original graph, original unbounded-arc
ratio test, nondegeneracy, unique entering choices, answers and input size. -/
theorem corollary4_count_extended {X : Type} (size : X → ℕ) (problem : X → ℕ)
    (family : X → ExtendedNetworkInput)
    (hsize : PolynomialBound size (fun x ↦ (family x).inputSize))
    (hDS18 : ∀ x, ∃ S, (family x).network.IsDantzigRun (family x).deletion (problem x) S ∧
      S 0 = (family x).initial ∧
      (∀ k ≤ problem x, (family x).network.IsNondegenerate (S k)) ∧
      (∀ k < problem x, ∀ j j',
        (family x).network.data.toNetwork.IsDantzigChoice (S k) j →
        (family x).network.data.toNetwork.IsDantzigChoice (S k) j' → j = j')) :
    (∀ x f, (family x).normalize.IsTargetCount f ↔ f = problem x) ∧
      PolynomialBound size (fun x ↦ (family x).reductionCost) := by
  refine ⟨?_, ExtendedNetworkInput.construction_polynomial.comp family hsize⟩
  intro x f
  obtain ⟨S, hS, h0, hnd, hu⟩ := hDS18 x
  obtain ⟨hc, he⟩ := (family x).count_transfer (problem x) S hS h0 hnd hu
  exact ⟨he f, fun h ↦ h ▸ hc⟩

end WolfeSimplex.PaperCorollary4

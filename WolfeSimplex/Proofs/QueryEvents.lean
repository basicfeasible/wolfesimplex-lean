import WolfeSimplex.Proofs.InitRuns
import WolfeSimplex.Proofs.AffineMin

/-! Queried insertion events, including the initialization prefix. -/
namespace WolfeSimplex
open Finset Wolfe

namespace Wolfe
variable {N D : ℕ} {p : Fin N → Fin D → ℝ}

theorem MajorCycle.support_subset {S T : Finset (Fin N)} {j : Fin N}
    (h : MajorCycle p S j T) : T ⊆ insert j S := by
  obtain ⟨_, _, l, h, _⟩ := h
  have hs : ∀ s t : State N, Relation.ReflTransGen (MinorCycle p) s t → t.S ⊆ s.S := by
    intro s t h
    induction h with
    | refl => exact Subset.rfl
    | @tail t u h hu ih =>
      obtain ⟨_, _, i, _, _, he⟩ := hu
      rw [he]
      exact (erase_subset _ _).trans ih
  exact hs _ _ h

/-- If a completed step retains a fresh label, its inserted label is forced. -/
theorem MajorCycle.label_eq_of_fresh {S T : Finset (Fin N)} {j l : Fin N}
    (h : MajorCycle p S j T) (hl : l ∈ T) (hn : l ∉ S) : j = l := by
  have := mem_insert.mp (h.support_subset hl)
  exact (this.resolve_right hn).symm

/-- A fixed numerical tie rule refines linopt. No assumption about uniqueness
of the minimum dot product is made. -/
def IsIndexLinoptChoice (p : Fin N → Fin D → ℝ) (S : Finset (Fin N)) (j : Fin N) : Prop :=
  IsLinoptChoice p S j ∧ ∀ i, IsLinoptChoice p S i → j.val ≤ i.val

theorem index_run_is_linopt {f : ℕ} {S : ℕ → Finset (Fin N)}
    (h : IsWolfeRunWith p (IsIndexLinoptChoice p) f S) :
    IsWolfeRunWith p (IsLinoptChoice p) f S := by
  refine ⟨⟨h.1.1, ?_⟩, h.2⟩
  intro k hk
  obtain ⟨j, hj, hp⟩ := h.1.2 k hk
  exact ⟨j, hj.1, hp⟩

theorem index_choice_exists (p : Fin N → Fin D → ℝ) (S : Finset (Fin N))
    (hi : (improving p (affineMin p S)).Nonempty) :
    ∃ j, IsIndexLinoptChoice p S j := by
  classical
  obtain ⟨j, hj, hm⟩ := Finset.exists_min_image _ (fun j ↦ p j ⬝ᵥ affineMin p S) hi
  let C := univ.filter (IsLinoptChoice p S)
  have hC : C.Nonempty := ⟨j, mem_filter.mpr ⟨mem_univ _, hj, hm⟩⟩
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image C (fun j ↦ j.val) hC
  exact ⟨k, (mem_filter.mp hk).2,
    fun i hi ↦ hmin i (mem_filter.mpr ⟨mem_univ _, hi⟩)⟩

/-- Total improving choices and the finite-run bound give a complete run.
This prevents queried-event reductions from relying on a vacuous universal
quantification over nonexistent executions. -/
theorem exists_complete_run (p : Fin N → Fin D → ℝ)
    (ch : Finset (Fin N) → Fin N → Prop)
    (total : ∀ S, IsCorral p S → (improving p (affineMin p S)).Nonempty →
      ∃ j, ch S j ∧ j ∈ improving p (affineMin p S))
    (S₀ : Finset (Fin N)) (hS₀ : IsCorral p S₀) :
    ∃ f S, IsWolfeRunWith p ch f S ∧ S 0 = S₀ := by
  classical
  by_contra hnone
  have hext : ∀ f, ∃ S, IsPartialWolfeRunWith p ch f S ∧ S 0 = S₀ := by
    intro f
    induction f with
    | zero => exact ⟨fun _ ↦ S₀, ⟨fun _ _ ↦ hS₀, by omega⟩, rfl⟩
    | succ f ih =>
      obtain ⟨S, hS, h0⟩ := ih
      have hn : improving p (affineMin p (S f)) ≠ ∅ := by
        intro ht; exact hnone ⟨f, S, ⟨hS, ht⟩, h0⟩
      obtain ⟨j, hj, hi⟩ := total _ (hS.1 f le_rfl) (nonempty_iff_ne_empty.mpr hn)
      obtain ⟨T, hT⟩ := (wolfe_well_defined_main p).2.1 _ j (hS.1 f le_rfl) hi
      let S' : ℕ → Finset (Fin N) := fun k ↦ if k ≤ f then S k else T
      have hold : ∀ k ≤ f, S' k = S k := fun k hk ↦ if_pos hk
      have hnew : S' (f + 1) = T := if_neg (by omega)
      refine ⟨S', ⟨?_, ?_⟩, by rw [hold 0 (by omega), h0]⟩
      · intro k hk
        by_cases h : k ≤ f
        · rw [hold k h]; exact hS.1 k h
        · have : k = f + 1 := by omega
          rw [this, hnew]; exact hT.2.2.choose_spec.2
      · intro k hk
        by_cases h : k < f
        · rw [hold k h.le, hold (k + 1) (by omega)]; exact hS.2 k h
        · have : k = f := by omega
          rw [this, hold f le_rfl, hnew]; exact ⟨j, hj, hT⟩
  obtain ⟨S, hS, _⟩ := hext (2 ^ N)
  have hb := (wolfe_well_defined_main p).2.2.2.2.2 ch _ S hS
  omega

theorem exists_index_run (p : Fin N → Fin D → ℝ) (S₀ : Finset (Fin N))
    (hS₀ : IsCorral p S₀) :
    ∃ f S, IsWolfeRunWith p (IsIndexLinoptChoice p) f S ∧ S 0 = S₀ := by
  apply exists_complete_run p _ _ S₀ hS₀
  intro S _ hi
  obtain ⟨j, hj⟩ := index_choice_exists p S hi
  exact ⟨j, hj, hj.1.1⟩

end Wolfe

namespace LP
variable {m n : ℕ} {P : LP m n}

theorem IsPivot.fresh {B C : Finset (Fin n)} {j : Fin n}
    (h : P.IsPivot B j C) : j ∈ C ∧ j ∉ B := by
  obtain ⟨_, _, hn, i, _, rfl⟩ := h
  exact ⟨mem_insert_self _ _, hn⟩

theorem pivot_iff_fresh {B C : Finset (Fin n)}
    (hs : ∃ l, P.IsPivot B l C) (j : Fin n) :
    P.IsPivot B j C ↔ j ∈ C ∧ j ∉ B := by
  refine ⟨IsPivot.fresh, ?_⟩
  rintro ⟨hj, hn⟩
  obtain ⟨l, hp⟩ := hs
  have hp' := hp
  obtain ⟨_, _, _, i, _, he⟩ := hp'
  rw [he, mem_insert] at hj
  rcases hj with h | h
  · exact h ▸ hp
  · exact (hn (mem_of_mem_erase h)).elim
end LP

end WolfeSimplex

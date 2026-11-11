import WolfeSimplex.Efficiency.Procedure

namespace WolfeSimplex.Efficiency

/-- Read the entering label from adjacent basis masks. This is an executable
linear scan, not a call to a simplex ratio test or a choice operator. -/
def nextLabel {n : ℕ} (b b' : Mask n) : Option (Fin n) :=
  (List.finRange n).find? fun j ↦ decide (b[j] = false ∧ b'[j] = true)

/-- A stateful pivot rule may retain this plan and a cursor. All work to produce
it is charged up front, including the complete supplied Wolfe execution. -/
def pivotPlan {n : ℕ} (xs : List (Mask n)) : List (Option (Fin n)) :=
  List.zipWith nextLabel xs xs.tail

@[simp] theorem pivotPlan_length {n : ℕ} (xs : List (Mask n)) :
    (pivotPlan xs).length = xs.length - 1 := by
  simp only [pivotPlan, List.length_zipWith, List.length_tail]
  omega

theorem pivotPlan_get {n : ℕ} (xs : List (Mask n)) (k : ℕ)
    (hk : k < xs.length - 1) :
    (pivotPlan xs)[k]'(by rw [pivotPlan_length]; exact hk) =
      nextLabel (xs[k]'(by omega)) (xs[k + 1]'(by omega)) := by
  simp only [pivotPlan, List.getElem_zipWith, List.getElem_tail]

theorem nextLabel_correct {m n : ℕ} (P : LP m n)
    (B B' : Finset (Fin n)) (j : Fin n) (h : P.IsPivot B j B') :
    nextLabel (mask B) (mask B') = some j := by
  obtain ⟨_, _, hj, i, hi, heq⟩ := h
  have hp (k : Fin n) :
      decide ((mask B)[k] = false ∧ (mask B')[k] = true) = decide (k = j) := by
    simp only [mask_get, decide_eq_false_iff_not, decide_eq_true_eq]
    congr 1
    rw [heq]
    simp only [Finset.mem_insert, Finset.mem_erase]
    aesop
  unfold nextLabel
  cases hf : (List.finRange n).find? (fun k ↦
      decide ((mask B)[k] = false ∧ (mask B')[k] = true)) with
  | none =>
    have hn := List.find?_eq_none.mp hf j (by simp)
    rw [hp] at hn
    simp at hn
  | some k =>
    have hk := List.find?_some hf
    rw [hp] at hk
    have he : k = j := of_decide_eq_true hk
    exact congrArg some he

/-- Concrete execution output: the projected bases and their entering labels. -/
def execute (A : WolfeProcedure) (i : Source) : Report i.n × List (Option (Fin i.n)) :=
  let r := induce A i
  (r, pivotPlan r.trace)

/-- Every adjacent pair used by the executable plan specifies a valid pivot.
The same source run is the output of the concrete trace projection. -/
theorem induced_choices (A : WolfeProcedure) (hA : CorrectWolfe A) (i : Source) :
    ∃ f B, (induce A i).trace = List.ofFn (fun k : Fin (f + 1) ↦ mask (B k)) ∧
      B 0 = support i.initial ∧ i.lp.toLP.IsSimplexRun f B ∧
      ∀ k < f, ∃ j, nextLabel (mask (B k)) (mask (B (k + 1))) = some j ∧
        i.lp.toLP.IsPivot (B k) j (B (k + 1)) := by
  obtain ⟨f, B, hB, h0, htrace⟩ := induce_correct A hA i
  refine ⟨f, B, htrace, h0, hB, fun k hk ↦ ?_⟩
  obtain ⟨j, _, hj⟩ := hB.2.1 k hk
  exact ⟨j, nextLabel_correct _ _ _ _ hj, hj⟩

/-- The actual executable plan has one valid entering label for every source
pivot, with no failed scans. This is stronger than merely producing a run witness. -/
theorem execute_correct (A : WolfeProcedure) (hA : CorrectWolfe A) (i : Source) :
    ∃ f B, (execute A i).1.trace = List.ofFn (fun k : Fin (f + 1) ↦ mask (B k)) ∧
      B 0 = support i.initial ∧ i.lp.toLP.IsSimplexRun f B ∧
      ∀ k < f, ∃ j, (execute A i).2[k]? = some (some j) ∧
        i.lp.toLP.IsPivot (B k) j (B (k + 1)) := by
  obtain ⟨f, B, htrace, h0, hB, hchoices⟩ := induced_choices A hA i
  refine ⟨f, B, htrace, h0, hB, fun k hk ↦ ?_⟩
  obtain ⟨j, hj, hp⟩ := hchoices k hk
  refine ⟨j, ?_, hp⟩
  have hlen : (induce A i).trace.length = f + 1 := by rw [htrace]; simp
  have hidx : k < (induce A i).trace.length - 1 := by omega
  change (pivotPlan (induce A i).trace)[k]? = _
  rw [List.getElem?_eq_getElem (by rw [pivotPlan_length]; exact hidx),
    pivotPlan_get _ _ hidx]
  simp only [htrace, List.getElem_ofFn]
  exact congrArg some hj

end WolfeSimplex.Efficiency

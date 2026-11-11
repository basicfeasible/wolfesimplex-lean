import WolfeSimplex.Execution.Budget

/-! Executed construction of a cap/atom-augmented initial support from its
source bit mask. Only copying and appending two one bits are performed. -/
namespace WolfeSimplex.Execution.Support
open Code Finset
variable {n : ℕ}

def input (B : Finset (Fin n)) : Env :=
  [List.ofFn fun j ↦ if j ∈ B then (1 : ℤ) else 0]

def code (n : ℕ) : Code :=
  par (readAt 0 (List.range n)) (par (literal 1) (literal 1))

theorem correct (B : Finset (Fin n)) :
    (code n).eval (input B) = List.ofFn (fun j : Fin (n + 2) ↦
      if j ∈ hat (hat B) then (1 : ℤ) else 0) := by
  have hr : (readAt 0 (List.range n)).eval (input B) =
      List.ofFn (fun j : Fin n ↦ if j ∈ B then (1 : ℤ) else 0) := by
    change (read (List.range n)).eval (input B) = _
    simpa only [input, List.length_ofFn] using read_range
      (List.ofFn (fun j : Fin n ↦ if j ∈ B then (1 : ℤ) else 0)) []
  have hh {k : ℕ} (A : Finset (Fin k)) :
      List.ofFn (fun j : Fin (k + 1) ↦ if j ∈ hat A then (1 : ℤ) else 0) =
        List.ofFn (fun j : Fin k ↦ if j ∈ A then (1 : ℤ) else 0) ++ [1] := by
    rw [List.ofFn_succ']
    simp only [IntLP.castSucc_mem_hat, IntLP.last_mem_hat, ite_true, List.concat_eq_append]
  simp only [code, eval_par, hr, eval_literal]
  rw [hh, hh, List.append_assoc]

theorem work (B : Finset (Fin n)) : ((code n).run (input B)).work = 4 * n + 16 := by
  simp [code, Code.run, input, List.length_range]
  ring

theorem peak (B : Finset (Fin n)) : ((code n).run (input B)).peak ≤ 1 := by
  have hr : ((readAt 0 (List.range n)).run (input B)).peak ≤ 1 := by
    apply peak_readAt
    intro i hi
    have hn := List.mem_range.mp hi
    simp only [input, List.getElem?_cons_zero, Option.getD_some, List.getElem?_ofFn,
      dite_eq_left hn]
    split_ifs <;> norm_num
  simpa only [code, peak_par, peak_literal, Int.natAbs_one, max_self, max_le_iff] using
    And.intro hr (le_refl 1)

theorem address (n : ℕ) : (code n).addressBound ≤ n + 1 := by
  have hr : (readAt 0 (List.range n)).addressBound ≤ n + 1 := by
    change max 0 (read (List.range n)).addressBound ≤ _
    exact max_le (by omega) ((address_range n).trans (by omega))
  exact max_le hr (by simp [Code.addressBound])

theorem bitWork (B : Finset (Fin n)) :
    (code n).bitWork (input B) ≤ 10 ^ 4 * (n + 1) ^ 3 := by
  have hw := work B
  have hp : Nat.size ((code n).run (input B)).peak ≤ 1 :=
    Nat.size_le.mpr ((peak B).trans_lt (by norm_num))
  have ha : Nat.size (code n).addressBound ≤ n + 1 :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (address n)
  have hc : Nat.size ((code n).run (input B)).work ≤ 4 * n + 16 := by
    rw [← hw]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hword : (code n).wordWidth (input B) ≤ 20 * (n + 1) := by
    change 1 + Nat.size ((code n).run (input B)).peak +
      Nat.size (code n).addressBound + Nat.size ((code n).run (input B)).work ≤ _
    omega
  have hpoly : (20 * (n + 1)) * (20 * (n + 1)) ^ 2 = 8000 * (n + 1) ^ 3 := by ring
  calc _ ≤ (20 * (n + 1)) * (20 * (n + 1)) ^ 2 :=
        Nat.mul_le_mul (by rw [hw]; omega) (Nat.pow_le_pow_left hword _)
       _ ≤ 10 ^ 4 * (n + 1) ^ 3 := by nlinarith [hpoly]

end WolfeSimplex.Execution.Support

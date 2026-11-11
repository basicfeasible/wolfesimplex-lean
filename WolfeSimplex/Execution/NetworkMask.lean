import WolfeSimplex.Execution.Network

/-! Executed construction of the initial standard-basis/cap/atom mask. -/
namespace WolfeSimplex.Execution.Network
open Code Finset
variable {n : ℕ}

def maskInput (S : BoundedLP.State n) : Env :=
  [List.ofFn (fun e ↦ if e ∈ S.tree then (1 : ℤ) else 0),
   List.ofFn (fun e ↦ if e ∈ S.atUpper then (1 : ℤ) else 0)]

def maskCode (n : ℕ) : Code :=
  par (table (List.ofFn fun e : Fin n ↦ Code.max (slot 0 e.val) (slot 1 e.val)))
    (par (table (List.ofFn fun e : Fin n ↦ sub (literal 1) (slot 1 e.val)))
      (par (literal 1) (literal 1)))

theorem mask_correct (S : BoundedLP.State n) :
    (maskCode n).eval (maskInput S) =
      List.ofFn (fun e : Fin (n + n + 2) ↦
        if e ∈ hat (hat S.basis) then (1 : ℤ) else 0) := by
  have hlo (e : Fin n) :
      (Code.max (slot 0 e.val) (slot 1 e.val)).eval (maskInput S) =
        [if BoundedLP.lower e ∈ S.basis then (1 : ℤ) else 0] := by
    have he := max_eval (a := slot 0 e.val) (b := slot 1 e.val)
      (env := maskInput S) (x := if e ∈ S.tree then 1 else 0)
      (y := if e ∈ S.atUpper then 1 else 0) (by simp [maskInput]) (by simp [maskInput])
    rw [he]
    simp only [BoundedLP.mem_basis_lower]
    split_ifs <;> simp_all
  have hhi (e : Fin n) :
      (sub (literal 1) (slot 1 e.val)).eval (maskInput S) =
        [if BoundedLP.upper e ∈ S.basis then (1 : ℤ) else 0] := by
    have he := sub_eval (eval_literal 1 (maskInput S))
      (a := literal 1) (b := slot 1 e.val)
      (x := 1) (y := if e ∈ S.atUpper then 1 else 0) (by simp [maskInput])
    rw [he]
    simp only [BoundedLP.mem_basis_upper]
    split_ifs <;> simp_all
  have ht : (maskCode n).eval (maskInput S) =
      List.ofFn (fun e : Fin (n + n) ↦ if e ∈ S.basis then (1 : ℤ) else 0) ++ [1, 1] := by
    simp only [maskCode, eval_par]
    rw [table_ofFn_eval _ _ _ hlo, table_ofFn_eval _ _ _ hhi]
    rw [List.ofFn_add]
    simp only [BoundedLP.lower, BoundedLP.upper, List.append_assoc]
    rfl
  rw [ht]
  have hhat {k : ℕ} (B : Finset (Fin k)) :
      List.ofFn (fun e : Fin (k + 1) ↦ if e ∈ hat B then (1 : ℤ) else 0) =
        List.ofFn (fun e : Fin k ↦ if e ∈ B then (1 : ℤ) else 0) ++ [1] := by
    rw [List.ofFn_succ']
    simp only [IntLP.castSucc_mem_hat, IntLP.last_mem_hat, ite_true, List.concat_eq_append]
  rw [hhat, hhat, List.append_assoc]
  rfl

theorem mask_size (n : ℕ) : (maskCode n).size = 15 * n + 7 := by
  have ht (f : Fin n → Code) (k : ℕ) (h : ∀ e, (f e).size = k) :
      (table (List.ofFn f)).size = n * (k + 1) + 1 := by
    have tt (cs : List Code) : (table cs).size = (cs.map fun c ↦ c.size + 1).sum + 1 := by
      induction cs with
      | nil => rfl
      | cons a cs ih =>
        simp only [Code.table, List.foldr_cons, Code.size] at ih ⊢
        simp only [List.map_cons, List.sum_cons]
        omega
    rw [tt]
    simp [List.map_ofFn, h, List.sum_ofFn]
  have hl := ht (fun e : Fin n ↦ Code.max (slot 0 e.val) (slot 1 e.val)) 7 (by simp)
  have hu := ht (fun e : Fin n ↦ sub (literal 1) (slot 1 e.val)) 6 (by simp [Code.size])
  simp only [maskCode, Code.size, hl, hu]
  ring

theorem mask_peak (S : BoundedLP.State n) : ((maskCode n).run (maskInput S)).peak ≤ 1 := by
  have ha (e : Fin n) : ScalarBound 1 (maskInput S) (slot 0 e.val)
      (if e ∈ S.tree then 1 else 0) := by
    apply ScalarBound.slot
    · split_ifs <;> norm_num
    · simp [maskInput]
  have hb (e : Fin n) : ScalarBound 1 (maskInput S) (slot 1 e.val)
      (if e ∈ S.atUpper then 1 else 0) := by
    apply ScalarBound.slot
    · split_ifs <;> norm_num
    · simp [maskInput]
  have hlo (e : Fin n) : ((Code.max (slot 0 e.val) (slot 1 e.val)).run (maskInput S)).peak ≤ 1 :=
    ((ha e).max (hb e)).peak
  have hhi (e : Fin n) : ((sub (literal 1) (slot 1 e.val)).run (maskInput S)).peak ≤ 1 := by
    apply ((ScalarBound.literal 1 (by norm_num)).sub (hb e) ?_).peak
    split_ifs <;> norm_num
  have hl := peak_table (List.ofFn fun e : Fin n ↦ Code.max (slot 0 e.val) (slot 1 e.val))
    (maskInput S) 1 (by intro c hc; obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hc; exact hlo e)
  have hu := peak_table (List.ofFn fun e : Fin n ↦ sub (literal 1) (slot 1 e.val))
    (maskInput S) 1 (by intro c hc; obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hc; exact hhi e)
  simpa only [maskCode, peak_par, peak_literal, Int.natAbs_one, max_self, max_le_iff] using
    And.intro hl (And.intro hu (le_refl 1))

theorem mask_address (n : ℕ) : (maskCode n).addressBound ≤ n + 1 := by
  have hs (b : ℕ) (e : Fin n) (hb : b ≤ 1) : (slot b e.val).addressBound ≤ n + 1 :=
    address_slot _ _ _ (by omega) (by have := e.isLt; omega)
  have hl := address_table (List.ofFn fun e : Fin n ↦ Code.max (slot 0 e.val) (slot 1 e.val))
    (n + 1) (by
      intro c hc; obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hc
      exact address_max (by omega) (hs 0 e (by decide)) (hs 1 e (by decide)))
  have hu := address_table (List.ofFn fun e : Fin n ↦ sub (literal 1) (slot 1 e.val))
    (n + 1) (by
      intro c hc; obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hc
      exact address_sub (by omega) (by simp [Code.addressBound]) (hs 1 e (by decide)))
  exact max_le hl (max_le hu (by simp [Code.addressBound]))

theorem mask_bitWork (S : BoundedLP.State n) :
    (maskCode n).bitWork (maskInput S) ≤ 10 ^ 12 * (n + 1) ^ 6 := by
  let L := n + 1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hw := work_bound (maskCode n) (maskInput S)
  simp only [mask_size, maskInput, List.length_cons, List.length_nil] at hw
  have hwork : ((maskCode n).run (maskInput S)).work ≤ 5000 * L ^ 2 := by
    apply hw.trans
    dsimp [L]; nlinarith
  have hbits : Nat.size ((maskCode n).run (maskInput S)).peak ≤ 1 := by
    exact Nat.size_le.mpr ((mask_peak S).trans_lt (by norm_num))
  have haddr : Nat.size (maskCode n).addressBound ≤ L :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (mask_address n)
  have hctr : Nat.size ((maskCode n).run (maskInput S)).work ≤ 5000 * L ^ 2 :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans hwork
  have hword : (maskCode n).wordWidth (maskInput S) ≤ 6000 * L ^ 2 := by
    change 1 + Nat.size ((maskCode n).run (maskInput S)).peak +
      Nat.size (maskCode n).addressBound + Nat.size ((maskCode n).run (maskInput S)).work ≤ _
    nlinarith
  calc _ ≤ (5000 * L ^ 2) * (6000 * L ^ 2) ^ 2 :=
        Nat.mul_le_mul hwork (Nat.pow_le_pow_left hword _)
       _ ≤ 10 ^ 12 * L ^ 6 := by nlinarith [show (5000 * L ^ 2) * (6000 * L ^ 2) ^ 2 =
          180000000000 * L ^ 6 by ring]

end WolfeSimplex.Execution.Network

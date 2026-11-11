import WolfeSimplex.Proofs.InfiniteCapacityBounds
import WolfeSimplex.Execution.NetworkBounds

/-! Executed finite-capacity normalization. The input has four arrays: supply
numerators, capacity numerators, capacity denominators and absent-bound flags.
Other network arrays are shared unchanged with the existing network converter.
The output is the two actual replacement capacity arrays. -/
namespace WolfeSimplex.Execution.InfiniteCapacity
open Code Finset
variable {v n : ℕ}

def input (Q : ExtendedNetwork v n) : Env :=
  [List.ofFn fun w ↦ (Q.data.supply w).num,
   List.ofFn fun e ↦ (Q.data.capacity e).num,
   List.ofFn fun e ↦ ((Q.data.capacity e).den : ℤ),
   List.ofFn fun e ↦ if e ∈ Q.infinite then (1 : ℤ) else 0]

def boundCode (v : ℕ) : Code :=
  add (literal 1) (Code.sum (List.ofFn fun w : Fin v ↦ abs (slot 0 w.val)))

def numerator (v i : ℕ) : Code :=
  add (mul (slot 3 i) (boundCode v))
    (mul (sub (literal 1) (slot 3 i)) (slot 1 i))

def denominator (i : ℕ) : Code :=
  add (slot 3 i) (mul (sub (literal 1) (slot 3 i)) (slot 2 i))

def code (v n : ℕ) : Code :=
  par (table (List.ofFn fun e : Fin n ↦ numerator v e.val))
    (table (List.ofFn fun e : Fin n ↦ denominator e.val))

theorem bound_correct (Q : ExtendedNetwork v n) :
    (boundCode v).eval (input Q) = [(Q.bound : ℤ)] := by
  have hh (w : Fin v) : (abs (slot 0 w.val)).eval (input Q) = [|(Q.data.supply w).num|] :=
    abs_eval (by simp [input])
  have hs := sum_eval (List.finRange v) (fun w ↦ abs (slot 0 w.val))
    (fun w ↦ |(Q.data.supply w).num|) (input Q) (fun w _ ↦ hh w)
  simp only [List.finRange, List.map_ofFn, Function.comp_def, List.sum_ofFn] at hs
  have he := add_eval (eval_literal 1 (input Q)) hs
  simpa [boundCode, ExtendedNetwork.bound, Nat.cast_sum, Nat.cast_natAbs] using he

theorem correct (Q : ExtendedNetwork v n) : (code v n).eval (input Q) =
    List.ofFn (fun e ↦ (Q.finite.capacity e).num) ++
      List.ofFn (fun e ↦ ((Q.finite.capacity e).den : ℤ)) := by
  have hf (e : Fin n) : (slot 3 e.val).eval (input Q) =
      [if e ∈ Q.infinite then (1 : ℤ) else 0] := by simp [input]
  have hc (e : Fin n) : (slot 1 e.val).eval (input Q) = [(Q.data.capacity e).num] := by
    simp [input]
  have hd (e : Fin n) : (slot 2 e.val).eval (input Q) = [((Q.data.capacity e).den : ℤ)] := by
    simp [input]
  have hnum (e : Fin n) : (numerator v e.val).eval (input Q) = [(Q.finite.capacity e).num] := by
    have he := add_eval (mul_eval (hf e) (bound_correct Q))
      (mul_eval (sub_eval (eval_literal 1 (input Q)) (hf e)) (hc e))
    change (numerator v e.val).eval (input Q) = _ at he
    by_cases hi : e ∈ Q.infinite <;> simpa [ExtendedNetwork.finite, hi] using he
  have hden (e : Fin n) : (denominator e.val).eval (input Q) = [((Q.finite.capacity e).den : ℤ)] := by
    have he := add_eval (hf e) (mul_eval (sub_eval (eval_literal 1 (input Q)) (hf e)) (hd e))
    change (denominator e.val).eval (input Q) = _ at he
    by_cases hi : e ∈ Q.infinite <;> simpa [ExtendedNetwork.finite, hi] using he
  simp only [code, eval_par, table_ofFn_eval _ _ _ hnum, table_ofFn_eval _ _ _ hden]

theorem code_size (v n : ℕ) : (code v n).size ≤ 100 * (v + n + 1) ^ 2 := by
  have hb : (boundCode v).size = 7 * v + 5 := by
    simp [boundCode, sum_size, List.map_ofFn, List.sum_ofFn, Code.size]; ring
  have hn (e : Fin n) : (numerator v e.val).size = 7 * v + 24 := by
    simp [numerator, hb, Code.size]; omega
  have hd (e : Fin n) : (denominator e.val).size = 16 := by
    simp [denominator, Code.size]
  have hs : (code v n).size = n * (7 * v + 42) + 3 := by
    simp [code, Code.size, table_size, List.map_ofFn, List.sum_ofFn, hn, hd]; ring
  rw [hs]; nlinarith

theorem code_growth (v n B : ℕ) (hB : 1 ≤ B) :
    GrowthCert B 2 (2 * v + 8) (code v n) := by
  have sl (b i : ℕ) := GrowthCert.slot b i B
  have one := GrowthCert.literal (B := B) 1 (by simpa using hB)
  have hs := GrowthCert.sum (List.finRange v) (fun w ↦ abs (slot 0 w.val)) 1 0
    (by decide) (fun w _ ↦ (sl 0 w.val).abs)
  have hb : GrowthCert B 1 (v + 2) (boundCode v) := by
    have hh := one.add hs
    simpa [boundCode, List.finRange, List.map_ofFn, Function.comp_def] using hh
  have hn (e : Fin n) : GrowthCert B 2 (2 * v + 8) (numerator v e.val) := by
    have h := ((sl 3 e.val).mul hb).add ((one.sub (sl 3 e.val)).mul (sl 1 e.val))
    apply h.mono (by simp)
    omega
  have hd (e : Fin n) : GrowthCert B 2 (2 * v + 8) (denominator e.val) := by
    have h := (sl 3 e.val).add ((one.sub (sl 3 e.val)).mul (sl 2 e.val))
    apply h.mono (by simp)
    omega
  have ht (f : Fin n → Code) (h : ∀ e, GrowthCert B 2 (2 * v + 8) (f e)) :=
    GrowthCert.table (List.finRange n) f 2 (2 * v + 8) (by decide) (fun e _ ↦ h e)
  have h := (ht _ hn).par (ht _ hd)
  simpa [code, List.finRange, List.map_ofFn, Function.comp_def] using h

theorem code_address (v n : ℕ) : (code v n).addressBound ≤ v + n + 5 := by
  let R := v + n + 5
  have hR : 1 ≤ R := by dsimp [R]; omega
  have sl (b i : ℕ) (hb : b ≤ 3) (hi : i < v ∨ i < n) : (slot b i).addressBound ≤ R :=
    address_slot b i R (by dsimp [R]; omega) (by dsimp [R]; omega)
  have hb : (boundCode v).addressBound ≤ R := by
    apply address_add hR (by simpa [Code.addressBound] using hR)
    apply address_sum _ _ hR
    intro a ha
    obtain ⟨w, rfl⟩ := List.mem_ofFn.mp ha
    exact address_abs (sl 0 w.val (by decide) (Or.inl w.isLt))
  have hn (e : Fin n) : (numerator v e.val).addressBound ≤ R := by
    have hf := sl 3 e.val (by decide) (Or.inr e.isLt)
    exact address_add hR (address_mul hR hf hb)
      (address_mul hR (address_sub hR (by simpa [Code.addressBound] using hR) hf)
        (sl 1 e.val (by decide) (Or.inr e.isLt)))
  have hd (e : Fin n) : (denominator e.val).addressBound ≤ R := by
    have hf := sl 3 e.val (by decide) (Or.inr e.isLt)
    exact address_add hR hf
      (address_mul hR (address_sub hR (by simpa [Code.addressBound] using hR) hf)
        (sl 2 e.val (by decide) (Or.inr e.isLt)))
  apply max_le <;> apply address_table
  · intro a ha; obtain ⟨e, rfl⟩ := List.mem_ofFn.mp ha; exact hn e
  · intro a ha; obtain ⟨e, rfl⟩ := List.mem_ofFn.mp ha; exact hd e

theorem input_bound (Q : ExtendedNetwork v n) : envBounded (input Q) (2 ^ Q.inputSize) := by
  have hB : 1 ≤ 2 ^ Q.inputSize := Nat.one_le_pow _ _ (by decide)
  intro xs hx z hz
  simp only [input, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  · exact (Q.entries_bounded.1 i).1
  · exact (Q.entries_bounded.2.2 i).1
  · simpa using (Q.entries_bounded.2.2 i).2
  · split_ifs <;> simp_all

theorem code_peak (Q : ExtendedNetwork v n) : ((code v n).run (input Q)).peak ≤
    2 ^ ((Q.inputSize + 1) * (2 * v + 10)) := by
  let B := 2 ^ (Q.inputSize + 1)
  have hB : 2 ≤ B := by dsimp [B]; rw [pow_succ]; have := Nat.one_le_pow Q.inputSize 2 (by decide); omega
  have hg := code_growth v n B (by omega)
  have hi : envBounded (input Q) (B ^ 1) := by
    intro xs hx z hz
    have hp : 2 ^ Q.inputSize ≤ B ^ 1 := by
      dsimp [B]
      simp only [pow_one]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (input_bound Q xs hx z hz).trans hp
  have h := (growth_bound _ _ B 1 hB hg.literals hi).1
  have he : (code v n).factor * 1 + (code v n).offset ≤ 2 * v + 10 := by
    have := hg.factor; have := hg.offset; omega
  exact h.trans ((Nat.pow_le_pow_right (by omega) he).trans (by dsimp [B]; rw [← pow_mul]))

theorem code_work (Q : ExtendedNetwork v n) :
    ((code v n).run (input Q)).work ≤ 10 ^ 6 * (1 + Q.inputSize) ^ 4 := by
  have hw := work_bound (code v n) (input Q)
  have hs := code_size v n
  have hd := Q.dimensions_le
  have hc : (code v n).size ≤ 100 * (1 + Q.inputSize) ^ 2 :=
    hs.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  simp only [input, List.length_cons, List.length_nil] at hw
  have h24 : (1 + Q.inputSize) ^ 2 ≤ (1 + Q.inputSize) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  calc _ ≤ 10 * (100 * (1 + Q.inputSize) ^ 2) * (4 + 100 * (1 + Q.inputSize) ^ 2 + 1) :=
        hw.trans (by gcongr)
       _ = 100000 * (1 + Q.inputSize) ^ 4 + 5000 * (1 + Q.inputSize) ^ 2 := by ring
       _ ≤ _ := by nlinarith

theorem code_bitWork (Q : ExtendedNetwork v n) :
    (code v n).bitWork (input Q) ≤ 10 ^ 30 * (1 + Q.inputSize) ^ 12 := by
  let L := 1 + Q.inputSize
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hd := Q.dimensions_le
  have hw := code_work Q
  have hp := code_peak Q
  have hb : Nat.size ((code v n).run (input Q)).peak ≤ 20 * L ^ 2 := by
    have ht : ((code v n).run (input Q)).peak <
        2 ^ ((Q.inputSize + 1) * (2 * v + 10) + 1) := by
      apply hp.trans_lt
      rw [pow_succ]; have := Nat.one_le_pow ((Q.inputSize + 1) * (2 * v + 10)) 2 (by decide); omega
    exact (Nat.size_le.mpr ht).trans (by dsimp [L]; nlinarith)
  have ha : Nat.size (code v n).addressBound ≤ 5 * L :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans ((code_address v n).trans (by dsimp [L]; omega))
  have hc : Nat.size ((code v n).run (input Q)).work ≤ 10 ^ 6 * L ^ 4 :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans hw
  have h24 : L ^ 2 ≤ L ^ 4 := Nat.pow_le_pow_right hL (by decide)
  have h14 : L ≤ L ^ 4 := by simpa using Nat.pow_le_pow_right hL (by decide : 1 ≤ 4)
  have hword : (code v n).wordWidth (input Q) ≤ 2000000 * L ^ 4 := by
    change 1 + Nat.size ((code v n).run (input Q)).peak +
      Nat.size (code v n).addressBound + Nat.size ((code v n).run (input Q)).work ≤ _
    nlinarith [Nat.one_le_pow 4 L hL]
  calc _ ≤ (10 ^ 6 * L ^ 4) * (2000000 * L ^ 4) ^ 2 :=
        Nat.mul_le_mul hw (Nat.pow_le_pow_left hword _)
       _ = 4000000000000000000 * L ^ 12 := by ring
       _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

end WolfeSimplex.Execution.InfiniteCapacity

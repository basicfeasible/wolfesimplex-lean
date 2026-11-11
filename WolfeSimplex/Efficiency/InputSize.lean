import WolfeSimplex.Efficiency.Trace
import WolfeSimplex.Construction.Work

namespace WolfeSimplex.Efficiency

open WolfeSimplex.Construction
variable {m n N D : ℕ}

/-- Both dimensions, all dense integer coordinates, and the initial support mask. -/
def pointEncoding (v : Points N D) (b : Mask N) : List Bool :=
  encodeNat N ++ encodeNat D ++
    ((v.toList.map Vector.toList).flatten.flatMap encodeInt) ++ b.toList

def pointSize (v : Points N D) : ℕ :=
  (encodeNat N).length + (encodeNat D).length +
    ((v.toList.map Vector.toList).flatten.flatMap encodeInt).length + N

@[simp] theorem pointEncoding_length (v : Points N D) (b : Mask N) :
    (pointEncoding v b).length = pointSize v := by simp [pointEncoding, pointSize]; omega

private theorem encoded_list_le (xs : List ℤ) (w : ℕ)
    (h : ∀ a ∈ xs, 1 + Nat.size a.natAbs ≤ w) :
    (xs.flatMap encodeInt).length ≤ 2 * w * xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb ↦ h b (by simp [hb]))
    simp only [List.flatMap_cons, List.length_append, encodeInt_length, List.length_cons]
    nlinarith

private theorem coordinate_width (P : IntLP m n) (hP : P.IsAdmissible)
    (j : Fin (n + 1)) (i : Fin (m + 1)) :
    1 + Nat.size ((atoms P)[j][i]).natAbs ≤
      1 + 36 * (m + 1) ^ 2 * Nat.size ((m + 1) * P.maxEntry) := by
  have hmag := P.atom_size hP.1 j i
  rw [← atoms_correct P j i, ← Int.cast_abs, Int.abs_eq_natAbs] at hmag
  have hi : ((atoms P)[j][i]).natAbs ≤
      ((m + 1) * P.maxEntry) ^ (36 * (m + 1) ^ 2) := by exact_mod_cast hmag
  exact Nat.add_le_add_left (IntLP.magnitude_bits_le (by positivity) hi) 1

/-- The reduction's complete target input, including its start, has polynomial
binary length in the source input length. -/
theorem pointSize_atoms (P : IntLP m n) (hP : P.IsAdmissible) :
    pointSize (atoms P) ≤ 100 * (3 * (1 + inputSize P)) ^ 5 := by
  let L := sizeParameter P
  have hL : 1 ≤ L := by dsimp [L, sizeParameter]; omega
  have hmL : m + 1 ≤ L := by dsimp [L, sizeParameter]; omega
  have hnL : n + 1 ≤ L := by dsimp [L, sizeParameter]; omega
  have hbase := base_size_le P
  have hL3 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ hL
  have hwidth : ∀ (j : Fin (n + 1)) (i : Fin (m + 1)),
      1 + Nat.size ((atoms P)[j][i]).natAbs ≤ 37 * L ^ 3 := by
    intro j i
    calc _ ≤ 1 + 36 * (m + 1) ^ 2 * Nat.size ((m + 1) * P.maxEntry) :=
               coordinate_width P hP j i
         _ ≤ 1 + 36 * L ^ 2 * L := by gcongr
         _ ≤ _ := by nlinarith [hL3]
  have he : (((atoms P).toList.map Vector.toList).flatten.flatMap encodeInt).length ≤
      2 * (37 * L ^ 3) * ((n + 1) * (m + 1)) := by
    have h := encoded_list_le (((atoms P).toList.map Vector.toList).flatten)
      (37 * L ^ 3) ?_
    · simpa [List.length_flatten, List.map_map, Function.comp_def] using h
    · intro a ha
      obtain ⟨row, hr, ha⟩ := List.mem_flatten.mp ha
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
      obtain ⟨j, hj, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hv)
      obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp ha)
      exact hwidth ⟨j, hj⟩ ⟨i, hi⟩
  have hsN : Nat.size (n + 1) ≤ n + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have hsD : Nat.size (m + 1) ≤ m + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have he' : (((atoms P).toList.map Vector.toList).flatten.flatMap encodeInt).length ≤
      74 * L ^ 5 := by
    apply he.trans
    calc _ ≤ 2 * (37 * L ^ 3) * (L * L) := by gcongr
         _ = _ := by ring
  have hL5 : L ≤ L ^ 5 := by
    calc L = L ^ 1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right hL (by omega)
  have hsmall : pointSize (atoms P) ≤ 100 * L ^ 5 := by
    simp only [pointSize, encodeNat_length]
    nlinarith
  have hs : L ≤ 3 * (1 + inputSize P) := (sizeParameter_le P).trans (by omega)
  exact hsmall.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 5))

end WolfeSimplex.Efficiency

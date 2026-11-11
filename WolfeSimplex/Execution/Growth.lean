import WolfeSimplex.Execution.Peak

/-! Compositional bounds for the numeric growth of straight-line programs.
Addition increases a base-B exponent by one; multiplication adds exponents.
These bounds are used between the separately checked determinant and atom code. -/
namespace WolfeSimplex.Execution.Code

def factor : Code → ℕ
  | .read _ | .readAt _ _ | .literal _ | .unary _ _ => 1
  | .binary .mul _ _ => 2
  | .binary _ _ _ => 1
  | .seq a b | .extend a b => a.factor * b.factor
  | .par a b => Max.max a.factor b.factor

def offset : Code → ℕ
  | .read _ | .readAt _ _ | .unary _ _ => 0
  | .literal _ => 1
  | .binary .add _ _ | .binary .sub _ _ => 1
  | .binary _ _ _ => 0
  | .seq a b | .extend a b => a.offset * b.factor + b.offset
  | .par a b => Max.max a.offset b.offset

def literalsBounded (B : ℕ) : Code → Prop
  | .literal z => z.natAbs ≤ B
  | .read _ | .readAt _ _ | .unary _ _ | .binary _ _ _ => True
  | .seq a b | .par a b | .extend a b => a.literalsBounded B ∧ b.literalsBounded B

def envBounded (env : Env) (R : ℕ) : Prop := ∀ xs ∈ env, ∀ z ∈ xs, z.natAbs ≤ R

theorem factor_pos (c : Code) : 1 ≤ c.factor := by
  induction c with
  | read _ | readAt _ _ | literal _ | unary _ _ => exact le_rfl
  | binary op a b => cases op <;> simp [factor]
  | seq a b ia ib | extend a b ia ib => exact Nat.mul_le_mul ia ib
  | par a b ia ib => exact ia.trans (le_max_left _ _)

private theorem get_bound (xs : List ℤ) (i R : ℕ) (h : ∀ z ∈ xs, z.natAbs ≤ R) :
    (xs[i]?.getD 0).natAbs ≤ R := by
  cases he : xs[i]? with
  | none => simp
  | some z => simpa only [Option.getD_some] using h z (List.mem_of_getElem? he)

private theorem frame_bound (env : Env) (block R : ℕ) (h : envBounded env R) :
    ∀ z ∈ env[block]?.getD [], z.natAbs ≤ R := by
  cases he : env[block]? with
  | none => simp
  | some xs => exact h xs (List.mem_of_getElem? he)

/-- Bounds both every primitive numeric operation and the returned cells. -/
theorem growth_bound (c : Code) (env : Env) (B M : ℕ) (hB : 2 ≤ B)
    (hc : c.literalsBounded B) (he : envBounded env (B ^ M)) :
    (c.run env).peak ≤ B ^ (c.factor * M + c.offset) ∧
      ∀ z ∈ c.eval env, z.natAbs ≤ B ^ (c.factor * M + c.offset) := by
  have hB1 : 1 ≤ B := by omega
  induction c generalizing env M with
  | read is =>
    have hcell (i : ℕ) : ((current env)[i]?.getD 0).natAbs ≤ B ^ M :=
      get_bound _ _ _ (frame_bound env 0 _ he)
    have ho : ∀ z ∈ (read is).eval env, z.natAbs ≤ B ^ M := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
      exact hcell i
    simpa only [factor, offset, one_mul, Nat.add_zero, eval, run] using
      And.intro ((magnitude_le _ _).mpr ho) ho
  | readAt block is =>
    have ho : ∀ z ∈ (readAt block is).eval env, z.natAbs ≤ B ^ M := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
      exact get_bound _ _ _ (frame_bound env block _ he)
    simpa only [factor, offset, one_mul, Nat.add_zero, eval, run] using
      And.intro ((magnitude_le _ _).mpr ho) ho
  | literal z =>
    have hz : z.natAbs ≤ B ^ (M + 1) := hc.trans (by
      simpa only [pow_one] using Nat.pow_le_pow_right hB1 (by omega : 1 ≤ M + 1))
    simpa [factor, offset, run, eval] using hz
  | unary op a =>
    have hx := get_bound (current env) a (B ^ M) (frame_bound env 0 _ he)
    have hy : (unaryValue op ((current env)[a]?.getD 0)).natAbs ≤ B ^ M := by
      cases op with
      | neg => simpa [unaryValue] using hx
      | abs => simpa only [unaryValue, Int.abs_eq_natAbs, Int.natAbs_natCast] using hx
      | sign =>
        have hs : (((current env)[a]?.getD 0).sign).natAbs ≤ 1 := by
          rcases lt_trichotomy ((current env)[a]?.getD 0) 0 with h | h | h
          · simp [Int.sign_eq_neg_one_of_neg h]
          · simp [h]
          · simp [Int.sign_eq_one_of_pos h]
        exact hs.trans (Nat.one_le_pow _ _ hB1)
    simpa [factor, offset, run, eval, max_le_iff] using And.intro hx hy
  | binary op a b =>
    have hx := get_bound (current env) a (B ^ M) (frame_bound env 0 _ he)
    have hy := get_bound (current env) b (B ^ M) (frame_bound env 0 _ he)
    have hmono : B ^ M ≤ B ^ ((binary op a b).factor * M + (binary op a b).offset) := by
      apply Nat.pow_le_pow_right hB1
      cases op <;> simp [factor, offset] <;> omega
    have hz : (binaryValue op ((current env)[a]?.getD 0) ((current env)[b]?.getD 0)).natAbs ≤
        B ^ ((binary op a b).factor * M + (binary op a b).offset) := by
      cases op with
      | mul =>
        simp only [binaryValue, Int.natAbs_mul, factor, offset, Nat.add_zero]
        calc _ ≤ B ^ M * B ^ M := Nat.mul_le_mul hx hy
             _ = _ := by rw [← pow_add]; congr 1; omega
      | add =>
        have ha := Int.natAbs_add_le ((current env)[a]?.getD 0) ((current env)[b]?.getD 0)
        simp only [binaryValue, factor, offset, one_mul]
        calc _ ≤ B ^ M + B ^ M := ha.trans (Nat.add_le_add hx hy)
             _ = B ^ M * 2 := by ring
             _ ≤ B ^ M * B := Nat.mul_le_mul_left _ hB
             _ = _ := (pow_succ _ _).symm
      | sub =>
        have ha := Int.natAbs_sub_le ((current env)[a]?.getD 0) ((current env)[b]?.getD 0)
        simp only [binaryValue, factor, offset, one_mul]
        calc _ ≤ B ^ M + B ^ M := ha.trans (Nat.add_le_add hx hy)
             _ = B ^ M * 2 := by ring
             _ ≤ B ^ M * B := Nat.mul_le_mul_left _ hB
             _ = _ := (pow_succ _ _).symm
      | max => exact max_natAbs _ _ _ (hx.trans hmono) (hy.trans hmono)
    constructor
    · exact max_le (hx.trans hmono) (max_le (hy.trans hmono) hz)
    · intro z hm
      have heq : z = binaryValue op ((current env)[a]?.getD 0) ((current env)[b]?.getD 0) :=
        List.mem_singleton.mp hm
      simpa only [heq] using hz
  | par a b ia ib =>
    have ha := ia env M hc.1 he
    have hb := ib env M hc.2 he
    have hEa : a.factor * M + a.offset ≤ (par a b).factor * M + (par a b).offset := by
      dsimp [factor, offset]
      exact Nat.add_le_add (Nat.mul_le_mul_right _ (le_max_left _ _)) (le_max_left _ _)
    have hEb : b.factor * M + b.offset ≤ (par a b).factor * M + (par a b).offset := by
      dsimp [factor, offset]
      exact Nat.add_le_add (Nat.mul_le_mul_right _ (le_max_right _ _)) (le_max_right _ _)
    have hpa := Nat.pow_le_pow_right hB1 hEa
    have hpb := Nat.pow_le_pow_right hB1 hEb
    constructor
    · exact max_le (ha.1.trans hpa) (hb.1.trans hpb)
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact (ha.2 z hz).trans hpa
      · exact (hb.2 z hz).trans hpb
  | seq a b ia ib | extend a b ia ib =>
    have ha := ia env M hc.1 he
    have hM : M ≤ a.factor * M + a.offset := by have := factor_pos a; nlinarith
    have he' : envBounded (a.eval env :: env) (B ^ (a.factor * M + a.offset)) := by
      intro xs hxs
      rcases List.mem_cons.mp hxs with rfl | hxs
      · exact ha.2
      · intro z hz
        exact (he xs hxs z hz).trans (Nat.pow_le_pow_right hB1 hM)
    have hb := ib (a.eval env :: env) (a.factor * M + a.offset) hc.2 he'
    have hdeg : b.factor * (a.factor * M + a.offset) + b.offset =
        a.factor * b.factor * M + (a.offset * b.factor + b.offset) := by ring
    rw [hdeg] at hb
    have hdeg' : a.factor * M + a.offset ≤
        a.factor * b.factor * M + (a.offset * b.factor + b.offset) := by
      have := factor_pos b
      nlinarith
    exact ⟨max_le (ha.1.trans (Nat.pow_le_pow_right hB1 hdeg')) hb.1, hb.2⟩

end WolfeSimplex.Execution.Code

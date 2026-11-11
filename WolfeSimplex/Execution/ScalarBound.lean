import WolfeSimplex.Execution.Peak

namespace WolfeSimplex.Execution.Code

/-- A value together with a bound on every executed operand and result. -/
structure ScalarBound (R : ℕ) (env : Env) (c : Code) (v : ℤ) : Prop where
  value : c.eval env = [v]
  peak : (c.run env).peak ≤ R
  magnitude : v.natAbs ≤ R

namespace ScalarBound
variable {R : ℕ} {env : Env} {a b : Code} {x y : ℤ}

theorem literal (z : ℤ) (hz : z.natAbs ≤ R) : ScalarBound R env (.literal z) z :=
  ⟨rfl, hz, hz⟩

theorem slot (block i : ℕ) (v : ℤ) (hv : v.natAbs ≤ R)
    (he : (Code.slot block i).eval env = [v]) : ScalarBound R env (Code.slot block i) v :=
  ⟨he, by rw [peak_slot he]; exact hv, hv⟩

theorem copy (i : ℕ) (v : ℤ) (hv : v.natAbs ≤ R)
    (he : (Code.copy i).eval env = [v]) : ScalarBound R env (Code.copy i) v :=
  ⟨he, by rw [peak_copy he]; exact hv, hv⟩

theorem mul (ha : ScalarBound R env a x) (hb : ScalarBound R env b y)
    (hz : (x * y).natAbs ≤ R) : ScalarBound R env (Code.mul a b) (x * y) :=
  ⟨mul_eval ha.value hb.value,
    scalar_binary_peak Binary.mul R ha.value hb.value ha.peak hb.peak
      ha.magnitude hb.magnitude hz, hz⟩

theorem add (ha : ScalarBound R env a x) (hb : ScalarBound R env b y)
    (hz : (x + y).natAbs ≤ R) : ScalarBound R env (Code.add a b) (x + y) :=
  ⟨add_eval ha.value hb.value,
    scalar_binary_peak Binary.add R ha.value hb.value ha.peak hb.peak
      ha.magnitude hb.magnitude hz, hz⟩

theorem sub (ha : ScalarBound R env a x) (hb : ScalarBound R env b y)
    (hz : (x - y).natAbs ≤ R) : ScalarBound R env (Code.sub a b) (x - y) :=
  ⟨sub_eval ha.value hb.value,
    scalar_binary_peak Binary.sub R ha.value hb.value ha.peak hb.peak
      ha.magnitude hb.magnitude hz, hz⟩

theorem max (ha : ScalarBound R env a x) (hb : ScalarBound R env b y) :
    ScalarBound R env (Code.max a b) (Max.max x y) := by
  have hz := max_natAbs x y R ha.magnitude hb.magnitude
  exact ⟨max_eval ha.value hb.value,
    scalar_binary_peak Binary.max R ha.value hb.value ha.peak hb.peak
      ha.magnitude hb.magnitude hz, hz⟩

theorem neg (ha : ScalarBound R env a x) : ScalarBound R env (Code.neg a) (-x) := by
  have hz : (-x).natAbs ≤ R := by simpa only [Int.natAbs_neg] using ha.magnitude
  exact ⟨neg_eval ha.value, scalar_unary_peak Unary.neg R ha.value ha.peak ha.magnitude hz, hz⟩

theorem abs (ha : ScalarBound R env a x) : ScalarBound R env (Code.abs a) |x| := by
  have hz : |x|.natAbs ≤ R := by simpa only [Int.abs_eq_natAbs, Int.natAbs_natCast] using ha.magnitude
  exact ⟨abs_eval ha.value, scalar_unary_peak Unary.abs R ha.value ha.peak ha.magnitude hz, hz⟩

/-- The extra exponent covers the base and accumulator at every power stage. -/
theorem power (ha : ScalarBound R env a x) (arity n : ℕ) (hx : 1 ≤ x.natAbs)
    (hp : x.natAbs ^ (n + 1) ≤ R) : ScalarBound R env (Code.power arity a n) (x ^ n) := by
  have hv : (x ^ n).natAbs ≤ R := by
    rw [Int.natAbs_pow]
    exact (Nat.pow_le_pow_right hx (by omega : n ≤ n + 1)).trans hp
  exact ⟨power_eval arity n a env x ha.value,
    (power_peak arity n ha.value hx).trans (max_le ha.peak hp), hv⟩

end ScalarBound
end WolfeSimplex.Execution.Code

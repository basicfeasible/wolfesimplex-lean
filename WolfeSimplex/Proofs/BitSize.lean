import WolfeSimplex.Proofs.Numbers
import Mathlib.Data.Nat.Size

/-!
# Explicit binary length bound for Lemma 10 and Theorem 1

`Nat.size z.natAbs` counts the binary magnitude digits (zero has length zero).
We add one bit for a sign. This is an encoding bound, not a running-time model.
-/

namespace WolfeSimplex.IntLP

/-- An integer of magnitude at most `b^e` needs at most `e * Nat.size b`
magnitude bits. The positive exponent allows a strict power-of-two bound. -/
theorem magnitude_bits_le {z : ℤ} {b e : ℕ} (he : e ≠ 0)
    (hz : z.natAbs ≤ b ^ e) : Nat.size z.natAbs ≤ e * Nat.size b := by
  apply Nat.size_le.mpr
  calc
    z.natAbs ≤ b ^ e := hz
    _ < (2 ^ Nat.size b) ^ e := Nat.pow_lt_pow_left (Nat.lt_size_self b) he
    _ = 2 ^ (e * Nat.size b) := by rw [← pow_mul, Nat.mul_comm]

/-- Lemma 10 / Theorem 1: each atom coordinate has an integer representation
with at most `1 + 36(m+1)^2 * Nat.size ((m+1)W)` bits, including a sign bit. -/
theorem atom_bitLength {m n : ℕ} (P : IntLP m n) (hP : P.IsAdmissible) :
    ∀ j k, ∃ z : ℤ, P.atom j k = z ∧
      1 + Nat.size z.natAbs ≤
        1 + 36 * (m + 1) ^ 2 * Nat.size ((m + 1) * P.maxEntry) := by
  intro j k
  obtain ⟨z, hz⟩ := P.atom_integral j k
  refine ⟨z, hz, Nat.add_le_add_left (magnitude_bits_le (by positivity) ?_) 1⟩
  have h := P.atom_size hP.1 j k
  rw [hz, ← Int.cast_abs, Int.abs_eq_natAbs] at h
  exact_mod_cast h

end WolfeSimplex.IntLP

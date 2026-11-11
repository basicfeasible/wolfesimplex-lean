import WolfeSimplex.Proofs.Corollary2Families

/-!
# The quantitative randomized entries of Table 1

`StretchedExponentialBound p` spells out `2^{tilde-Omega(N^p)}`: a positive
constant in the exponent, a fixed power of the logarithm in the denominator,
a positive multiplicative constant and an eventual threshold. The harmless
`N+1,N+2` shifts make the formula defined at zero. The cited source lower
bounds are premises; preservation of their exact exponents is proved here.
-/
namespace WolfeSimplex.PaperCorollary2
open Finset Wolfe Transfers

noncomputable def stretchedRate (p a : ℝ) (k N : ℕ) : ℝ :=
  (2 : ℝ) ^ (a * ((N : ℝ) + 1) ^ p / (Real.log ((N : ℝ) + 2)) ^ k)

def StretchedExponentialBound (p : ℝ) (size : ℕ → ℕ) (count : ℕ → ENNReal) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ k : ℕ, ∃ b : ℝ, 0 < b ∧ ∃ R : ℕ,
    ∀ r ≥ R, ENNReal.ofReal (stretchedRate p a k (size r)) ≤ ENNReal.ofReal b * count r

theorem stretchedRate_add_two (p a : ℝ) (k N : ℕ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (ha : 0 ≤ a) :
    stretchedRate p (a / 3) k (N + 2) ≤ stretchedRate p a k N := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hroot : ((N : ℝ) + 3) ^ p ≤ 3 * ((N : ℝ) + 1) ^ p := by
    calc _ ≤ (3 * ((N : ℝ) + 1)) ^ p :=
          Real.rpow_le_rpow (by positivity) (by linarith) hp
         _ = (3 : ℝ) ^ p * ((N : ℝ) + 1) ^ p := Real.mul_rpow (by norm_num) (by positivity)
         _ ≤ 3 * ((N : ℝ) + 1) ^ p := by
          have hh : (3 : ℝ) ^ p ≤ 3 := by
            simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hp1
          exact mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (by positivity) _)
  have hlog : Real.log ((N : ℝ) + 2) ≤ Real.log ((N : ℝ) + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogpos : 0 < Real.log ((N : ℝ) + 2) := Real.log_pos (by linarith)
  have hden : (Real.log ((N : ℝ) + 2)) ^ k ≤ (Real.log ((N : ℝ) + 4)) ^ k := by
    exact pow_le_pow_left₀ hlogpos.le hlog _
  have hdenpos : 0 < (Real.log ((N : ℝ) + 2)) ^ k := pow_pos hlogpos _
  have hn : a / 3 * ((N : ℝ) + 3) ^ p ≤ a * ((N : ℝ) + 1) ^ p := by
    have hh := mul_le_mul_of_nonneg_left hroot (show 0 ≤ a / 3 by positivity)
    nlinarith
  have he : a / 3 * ((N : ℝ) + 3) ^ p / (Real.log ((N : ℝ) + 4)) ^ k ≤
      a * ((N : ℝ) + 1) ^ p / (Real.log ((N : ℝ) + 2)) ^ k := by
    exact (div_le_div_of_nonneg_right hn (hdenpos.le.trans hden)).trans
      (div_le_div_of_nonneg_left (mul_nonneg ha (Real.rpow_nonneg (by positivity) _)) hdenpos hden)
  unfold stretchedRate
  simp only [Nat.cast_add, Nat.cast_ofNat]
  convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he using 1 <;> ring_nf

theorem stretched_exponential_add_two {p : ℝ} {size : ℕ → ℕ} {count : ℕ → ENNReal}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (h : StretchedExponentialBound p size count) :
    StretchedExponentialBound p (fun r ↦ size r + 2) count := by
  obtain ⟨a, ha, k, b, hb, R, hR⟩ := h
  refine ⟨a / 3, by positivity, k, b, hb, R, fun r hr ↦ ?_⟩
  exact (ENNReal.ofReal_le_ofReal (stretchedRate_add_two p a k (size r) hp hp1 ha.le)).trans (hR r hr)

private noncomputable def rateIntegerFamily {m n : ℕ → ℕ}
    (R : ∀ r, RationalInput (m r) (n r)) : ∀ r, LiteratureInput (m r) (n r) :=
  fun r ↦ Classical.choose (integerize (R r))

private noncomputable def rateTargetFamily {m n : ℕ → ℕ}
    (R : ∀ r, RationalInput (m r) (n r)) : IntegralFamily m n where
  points r := (rateIntegerFamily R r).points
  start r := (rateIntegerFamily R r).start
  integral r := (rateIntegerFamily R r).integral
  corral r := (rateIntegerFamily R r).start_corral

/-- Exact expectations without any growth hypothesis. This permits transfer
of the quantitative source rates, independently of generic superpolynomiality. -/
theorem random_families_exact {m n : ℕ → ℕ} (R : ∀ r, RationalInput (m r) (n r)) :
    ∃ T : IntegralFamily m n,
      (∀ r, expectedLength (fun k ↦ randomRun (T.points r) (randomInsertion (T.points r)) k
        (T.start r)) = expectedLength (fun k ↦ (R r).lp.randomRun (R r).lp.randomEdge k (R r).initial)) ∧
      (∀ r, expectedLength (fun k ↦ randomOrderRun (T.points r) k (T.start r)) =
        expectedLength (fun k ↦ (R r).lp.randomBlandRun k (R r).initial)) := by
  refine ⟨rateTargetFamily R, ?_, ?_⟩
  · intro r
    change expectedLength (fun k ↦ randomRun (rateIntegerFamily R r).points
      (randomInsertion (rateIntegerFamily R r).points) k (rateIntegerFamily R r).start) = _
    rw [(rateIntegerFamily R r).random_edge_expected]
    apply expected_eq_of_prefix
    intro k
    have hs := Classical.choose_spec (integerize (R r))
    dsimp only [rateIntegerFamily]
    rw [hs.1]
    exact hs.2.2.2.1 k
  · intro r
    change expectedLength (fun k ↦ randomOrderRun (rateIntegerFamily R r).points k
      (rateIntegerFamily R r).start) = _
    rw [(rateIntegerFamily R r).random_bland_expected]
    apply expected_eq_of_prefix
    intro k
    have hs := Classical.choose_spec (integerize (R r))
    dsimp only [rateIntegerFamily]
    rw [hs.1]
    exact hs.2.2.2.2 k

/-- Table 1, random insertion: `2^{tilde-Omega(N^(1/4))}` in the number
`N = n+2` of target points. Only the cited rational Random-Edge family/rate
is assumed, not a Wolfe lower bound. -/
theorem random_edge_table1 {m n : ℕ → ℕ} (R : ∀ r, RationalInput (m r) (n r))
    (unbounded : ∀ r, r ≤ n r)
    (source : StretchedExponentialBound (1 / 4 : ℝ) n (fun r ↦ expectedLength
      (fun k ↦ (R r).lp.randomRun (R r).lp.randomEdge k (R r).initial))) :
    ∃ T : IntegralFamily m n, (∀ r, r ≤ n r + 2) ∧
      (∀ r, expectedLength (fun k ↦ randomRun (T.points r) (randomInsertion (T.points r)) k
        (T.start r)) = expectedLength (fun k ↦ (R r).lp.randomRun (R r).lp.randomEdge k (R r).initial)) ∧
      StretchedExponentialBound (1 / 4 : ℝ) (fun r ↦ n r + 2) (fun r ↦ expectedLength
        (fun k ↦ randomRun (T.points r) (randomInsertion (T.points r)) k (T.start r))) := by
  obtain ⟨T, he, _⟩ := random_families_exact R
  refine ⟨T, fun r ↦ (unbounded r).trans (by omega), he, ?_⟩
  simpa only [he] using stretched_exponential_add_two (by norm_num : (0 : ℝ) ≤ 1/4)
    (by norm_num : (1/4 : ℝ) ≤ 1) source

/-- Table 1, random order: `2^{tilde-Omega(sqrt N)}`. The one-permutation
source process is Random-Bland, not Random-Facet or a resampled order. -/
theorem random_bland_table1 {m n : ℕ → ℕ} (R : ∀ r, RationalInput (m r) (n r))
    (unbounded : ∀ r, r ≤ n r)
    (source : StretchedExponentialBound (1 / 2 : ℝ) n (fun r ↦ expectedLength
      (fun k ↦ (R r).lp.randomBlandRun k (R r).initial))) :
    ∃ T : IntegralFamily m n, (∀ r, r ≤ n r + 2) ∧
      (∀ r, expectedLength (fun k ↦ randomOrderRun (T.points r) k (T.start r)) =
        expectedLength (fun k ↦ (R r).lp.randomBlandRun k (R r).initial)) ∧
      StretchedExponentialBound (1 / 2 : ℝ) (fun r ↦ n r + 2) (fun r ↦ expectedLength
        (fun k ↦ randomOrderRun (T.points r) k (T.start r))) := by
  obtain ⟨T, _, he⟩ := random_families_exact R
  refine ⟨T, fun r ↦ (unbounded r).trans (by omega), he, ?_⟩
  simpa only [he] using stretched_exponential_add_two (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) source

end WolfeSimplex.PaperCorollary2

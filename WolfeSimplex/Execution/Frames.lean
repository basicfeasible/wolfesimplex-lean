import WolfeSimplex.Execution.Growth

namespace WolfeSimplex.Execution.Code

/-- A sequence of materialized caches, followed by a continuation. -/
def cacheChain (cs : List Code) (body : Code) : Code := cs.foldr extend body

def frames : List Code → Env → Env
  | [], env => env
  | c :: cs, env => frames cs (c.eval env :: env)

def prefixPeak : List Code → Env → ℕ
  | [], _ => 0
  | c :: cs, env => Max.max (c.run env).peak (prefixPeak cs (c.eval env :: env))

@[simp] theorem prefix_eval (cs : List Code) (body : Code) (env : Env) :
    (cacheChain cs body).eval env = body.eval (frames cs env) := by
  induction cs generalizing env <;> simp_all [cacheChain, frames]

@[simp] theorem prefix_peak (cs : List Code) (body : Code) (env : Env) :
    ((cacheChain cs body).run env).peak =
      Max.max (prefixPeak cs env) (body.run (frames cs env)).peak := by
  induction cs generalizing env <;> simp_all [cacheChain, frames, prefixPeak, max_assoc]

/-- A fixed number of cache stages preserves polynomial exponent bounds.
No growth bound is assumed for the continuation; it is checked separately. -/
theorem frames_growth (cs : List Code) (env : Env) (B M q : ℕ) (hB : 2 ≤ B)
    (hc : ∀ c ∈ cs, c.factor ≤ q ∧ c.offset ≤ q ∧ c.literalsBounded B)
    (he : envBounded env (B ^ M)) :
    prefixPeak cs env ≤ B ^ ((q + 1) ^ cs.length * (M + 1)) ∧
      envBounded (frames cs env) (B ^ ((q + 1) ^ cs.length * (M + 1))) := by
  have hB1 : 1 ≤ B := by omega
  induction cs generalizing env M with
  | nil =>
    constructor
    · exact Nat.zero_le _
    · intro xs hxs z hz
      exact (he xs hxs z hz).trans (Nat.pow_le_pow_right hB1 (by simp))
  | cons c cs ih =>
    obtain ⟨hf, ho, hl⟩ := hc c (by simp)
    have hg := growth_bound c env B M hB hl he
    let D := c.factor * M + c.offset
    have hMD : M ≤ D := by have := factor_pos c; dsimp [D]; nlinarith
    have hnext : envBounded (c.eval env :: env) (B ^ D) := by
      intro xs hxs
      rcases List.mem_cons.mp hxs with rfl | hxs
      · exact hg.2
      · intro z hz
        exact (he xs hxs z hz).trans (Nat.pow_le_pow_right hB1 hMD)
    have ht := ih (c.eval env :: env) D (fun c hc' ↦ hc c (by simp [hc'])) hnext
    have hD : D + 1 ≤ (q + 1) * (M + 1) := by dsimp [D]; nlinarith
    have hpow : 1 ≤ (q + 1) ^ cs.length := Nat.one_le_pow _ _ (by omega)
    have hdeg : (q + 1) ^ cs.length * (D + 1) ≤
        (q + 1) ^ (cs.length + 1) * (M + 1) := by
      calc _ ≤ (q + 1) ^ cs.length * ((q + 1) * (M + 1)) := Nat.mul_le_mul_left _ hD
           _ = _ := by rw [pow_succ]; ring
    have hcdeg : D ≤ (q + 1) ^ (cs.length + 1) * (M + 1) :=
      (by nlinarith : D ≤ (q + 1) ^ cs.length * (D + 1)).trans hdeg
    constructor
    · exact max_le (hg.1.trans (Nat.pow_le_pow_right hB1 hcdeg))
        (ht.1.trans (Nat.pow_le_pow_right hB1 hdeg))
    · intro xs hxs z hz
      exact (ht.2 xs hxs z hz).trans (Nat.pow_le_pow_right hB1 hdeg)

end WolfeSimplex.Execution.Code

import WolfeSimplex.Execution.Scalar

namespace WolfeSimplex.Execution.Code

private theorem foldl_max_le (xs : List ℕ) (a b : ℕ) :
    xs.foldl Max.max a ≤ b ↔ a ≤ b ∧ ∀ z ∈ xs, z ≤ b := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, max_le_iff, and_assoc, and_left_comm]

theorem magnitude_le (xs : List ℤ) (b : ℕ) :
    magnitude xs ≤ b ↔ ∀ z ∈ xs, z.natAbs ≤ b := by
  simp [magnitude, foldl_max_le]

@[simp] theorem peak_literal (z : ℤ) (env : Env) : ((literal z).run env).peak = z.natAbs := rfl
@[simp] theorem peak_seq (a b : Code) (env : Env) :
    ((seq a b).run env).peak = Max.max (a.run env).peak (b.run (a.eval env :: env)).peak := rfl
@[simp] theorem peak_extend (a b : Code) (env : Env) :
    ((extend a b).run env).peak = Max.max (a.run env).peak (b.run (a.eval env :: env)).peak := rfl
@[simp] theorem peak_par (a b : Code) (env : Env) :
    ((par a b).run env).peak = Max.max (a.run env).peak (b.run env).peak := rfl

theorem peak_readAt (block : ℕ) (is : List ℕ) (env : Env) (R : ℕ)
    (h : ∀ i ∈ is, ((env[block]?.getD [])[i]?.getD 0).natAbs ≤ R) :
    ((readAt block is).run env).peak ≤ R := by
  apply (magnitude_le _ _).mpr
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
  exact h i hi

theorem peak_copy {i : ℕ} {env : Env} {z : ℤ} (h : (copy i).eval env = [z]) :
    ((copy i).run env).peak = z.natAbs := by
  have hz := List.cons.inj h |>.1
  simp only [copy, run, magnitude, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_nil, Nat.zero_max]
  exact congrArg Int.natAbs hz

theorem peak_slot {block i : ℕ} {env : Env} {z : ℤ} (h : (slot block i).eval env = [z]) :
    ((slot block i).run env).peak = z.natAbs := by
  have hz := List.cons.inj h |>.1
  simp only [slot, run, magnitude, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_nil, Nat.zero_max]
  exact congrArg Int.natAbs hz

theorem peak_binary {a b : Code} {env : Env} {x y : ℤ} (op : Binary)
    (ha : a.eval env = [x]) (hb : b.eval env = [y]) :
    ((seq (par a b) (binary op 0 1)).run env).peak =
      Max.max (a.run env).peak (Max.max (b.run env).peak
        (Max.max x.natAbs (Max.max y.natAbs (binaryValue op x y).natAbs))) := by
  unfold eval at ha hb
  simp [run, current, ha, hb, max_assoc, max_left_comm, max_comm]

theorem peak_unary {a : Code} {env : Env} {x : ℤ} (op : Unary)
    (ha : a.eval env = [x]) :
    ((seq a (unary op 0)).run env).peak =
      Max.max (a.run env).peak (Max.max x.natAbs (unaryValue op x).natAbs) := by
  unfold eval at ha
  simp [run, current, ha]

/-- All scalar subprograms and all concatenations are executed. -/
theorem peak_table (cs : List Code) (env : Env) (R : ℕ)
    (h : ∀ c ∈ cs, (c.run env).peak ≤ R) : ((table cs).run env).peak ≤ R := by
  induction cs with
  | nil => simp [table, run, magnitude]
  | cons c cs ih =>
    simp only [table, List.foldr_cons, peak_par, max_le_iff]
    exact ⟨h c (by simp), ih (fun c hc ↦ h c (by simp [hc]))⟩

theorem scalar_binary_peak {a b : Code} {env : Env} {x y : ℤ} (op : Binary) (R : ℕ)
    (ha : a.eval env = [x]) (hb : b.eval env = [y])
    (hpa : (a.run env).peak ≤ R) (hpb : (b.run env).peak ≤ R)
    (hx : x.natAbs ≤ R) (hy : y.natAbs ≤ R)
    (hz : (binaryValue op x y).natAbs ≤ R) :
    ((seq (par a b) (binary op 0 1)).run env).peak ≤ R := by
  rw [peak_binary op ha hb]
  exact max_le hpa (max_le hpb (max_le hx (max_le hy hz)))

theorem scalar_unary_peak {a : Code} {env : Env} {x : ℤ} (op : Unary) (R : ℕ)
    (ha : a.eval env = [x]) (hpa : (a.run env).peak ≤ R)
    (hx : x.natAbs ≤ R) (hz : (unaryValue op x).natAbs ≤ R) :
    ((seq a (unary op 0)).run env).peak ≤ R := by
  rw [peak_unary op ha]
  exact max_le hpa (max_le hx hz)

/-- Partial sums as well as the final sum are bounded. -/
theorem sum_peak {α : Type} (as : List α) (f : α → Code) (v : α → ℤ)
    (env : Env) (M : ℕ) (he : ∀ a ∈ as, (f a).eval env = [v a])
    (hp : ∀ a ∈ as, ((f a).run env).peak ≤ M)
    (hv : ∀ a ∈ as, (v a).natAbs ≤ M) :
    ((sum (as.map f)).run env).peak ≤ (as.length + 1) * M ∧
      ((as.map v).sum).natAbs ≤ as.length * M := by
  induction as with
  | nil => simp [sum, run]
  | cons a as ih =>
    have hpa := hp a (by simp)
    have hva := hv a (by simp)
    have ht := ih (fun b hb ↦ he b (by simp [hb]))
      (fun b hb ↦ hp b (by simp [hb])) (fun b hb ↦ hv b (by simp [hb]))
    have heq := sum_eval as f v env (fun b hb ↦ he b (by simp [hb]))
    have hsum : (v a + (as.map v).sum).natAbs ≤ (as.length + 1) * M := by
      have h := Int.natAbs_add_le (v a) ((as.map v).sum)
      nlinarith [ht.2]
    constructor
    · simp only [List.map_cons, sum, add, List.length_cons]
      exact scalar_binary_peak Binary.add _ (he a (by simp)) heq
        (by nlinarith) (by nlinarith [ht.1]) (by nlinarith) (by nlinarith [ht.2])
        (by simpa only [binaryValue] using hsum.trans (by nlinarith))
    · simpa only [List.map_cons, List.sum_cons, List.length_cons] using hsum

theorem max_natAbs (x y : ℤ) (R : ℕ) (hx : x.natAbs ≤ R) (hy : y.natAbs ≤ R) :
    (Max.max x y).natAbs ≤ R := by
  rcases le_total x y with h | h
  · simpa only [max_eq_right h] using hy
  · simpa only [max_eq_left h] using hx

/-- Maximum scans never create an integer larger than a scanned magnitude. -/
theorem maxList_peak {α : Type} (as : List α) (f : α → Code) (v : α → ℤ)
    (env : Env) (M : ℕ) (he : ∀ a ∈ as, (f a).eval env = [v a])
    (hp : ∀ a ∈ as, ((f a).run env).peak ≤ M)
    (hv : ∀ a ∈ as, (v a).natAbs ≤ M) :
    ((maxList (as.map f)).run env).peak ≤ M ∧
      ((as.map v).foldr Max.max 0).natAbs ≤ M := by
  induction as with
  | nil => simp [maxList, run]
  | cons a as ih =>
    have ht := ih (fun b hb ↦ he b (by simp [hb]))
      (fun b hb ↦ hp b (by simp [hb])) (fun b hb ↦ hv b (by simp [hb]))
    have heq := maxList_eval as f v env (fun b hb ↦ he b (by simp [hb]))
    have hmax := max_natAbs _ _ M (hv a (by simp)) ht.2
    constructor
    · simp only [List.map_cons, maxList, max]
      exact scalar_binary_peak Binary.max M (he a (by simp)) heq
        (hp a (by simp)) ht.1 (hv a (by simp)) ht.2 hmax
    · simpa only [List.map_cons, List.foldr_cons] using hmax

private def powerStep := par (copy 0) (mul (copy 0) (copy 1))

private theorem powerStep_peak (b a : ℤ) (env : Env) :
    (powerStep.run ([b, a] :: env)).peak =
      Max.max b.natAbs (Max.max a.natAbs (b * a).natAbs) := by
  have hm := peak_binary Binary.mul (a := copy 0) (b := copy 1)
    (env := [b, a] :: env) (x := b) (y := a) (by rfl) (by rfl)
  simp only [powerStep, peak_par, mul, hm]
  rw [peak_copy (by rfl : (copy 0).eval ([b, a] :: env) = [b]),
    peak_copy (by rfl : (copy 1).eval ([b, a] :: env) = [a])]
  simp [binaryValue, max_assoc, max_left_comm, max_comm]

private theorem iterate_power_peak (b a : ℤ) (n : ℕ) (env : Env)
    (hb : 1 ≤ b.natAbs) :
    ((iterateCode powerStep n).run ([b, a] :: env)).peak ≤
      Max.max b.natAbs (Max.max a.natAbs (b.natAbs ^ n * a.natAbs)) := by
  induction n generalizing a env with
  | zero =>
    simp [iterateCode, powerStep, outputs, copy, mul, run, current, magnitude,
      List.range_succ, max_assoc, max_left_comm, max_comm]
  | succ n ih =>
    have he : powerStep.eval ([b, a] :: env) = [b, b * a] := by
      simp only [powerStep, eval_par]
      rw [mul_eval (by rfl : (copy 0).eval ([b, a] :: env) = [b])
        (by rfl : (copy 1).eval ([b, a] :: env) = [a])]
      rfl
    rw [iterateCode, peak_seq, he, powerStep_peak]
    have ht := ih (b * a) ([b, a] :: env)
    have hp : a.natAbs ≤ b.natAbs ^ (n + 1) * a.natAbs := by
      exact le_mul_of_one_le_left (Nat.zero_le _) (Nat.one_le_pow _ _ hb)
    have hprod : (b * a).natAbs ≤ b.natAbs ^ (n + 1) * a.natAbs := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul_right _ (by
        simpa only [pow_one] using Nat.pow_le_pow_right hb (by omega : 1 ≤ n + 1))
    have hpow : b.natAbs ^ n * (b * a).natAbs = b.natAbs ^ (n + 1) * a.natAbs := by
      rw [Int.natAbs_mul, pow_succ]
      ring
    apply max_le
    · exact max_le (le_max_left _ _) (max_le (le_trans hp (le_trans (le_max_right _ _)
        (le_max_right _ _))) (le_trans hprod (le_trans (le_max_right _ _) (le_max_right _ _))))
    · apply ht.trans
      rw [hpow]
      exact max_le (le_max_left _ _)
        (max_le (hprod.trans ((le_max_right _ _).trans (le_max_right _ _)))
          ((le_max_right _ _).trans (le_max_right _ _)))

/-- Cached powers also monitor all accumulators and operands. -/
theorem power_peak {base : Code} {env : Env} {b : ℤ} (arity n : ℕ)
    (he : base.eval env = [b]) (hb : 1 ≤ b.natAbs) :
    ((power arity base n).run env).peak ≤
      Max.max (base.run env).peak (b.natAbs ^ (n + 1)) := by
  have hp := iterate_power_peak b 1 n ([b] :: env) hb
  have hfinal : b.natAbs ^ n ≤ b.natAbs ^ (n + 1) :=
    Nat.pow_le_pow_right hb (by omega)
  have hbase : b.natAbs ≤ b.natAbs ^ (n + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hb (by omega : 1 ≤ n + 1)
  have hone : 1 ≤ b.natAbs ^ (n + 1) := Nat.one_le_pow _ _ hb
  simp only [Int.natAbs_one, mul_one] at hp
  unfold power
  simp only [peak_extend, he, peak_seq]
  have hinit : (par (copy 0) (literal 1)).eval ([b] :: env) = [b, 1] := rfl
  rw [hinit]
  have hi : ((par (copy 0) (literal 1)).run ([b] :: env)).peak ≤ b.natAbs ^ (n + 1) := by
    rw [peak_par, peak_copy (by rfl : (copy 0).eval ([b] :: env) = [b]), peak_literal]
    exact max_le hbase hone
  have hlast : ((copy 1).run
    ((iterateCode powerStep n).eval ([b, 1] :: ([b] :: env)) :: [b, 1] :: [b] :: env)).peak ≤
      b.natAbs ^ (n + 1) := by
    have hcopy : (copy 1).eval
      ((iterateCode powerStep n).eval ([b, 1] :: ([b] :: env)) :: [b, 1] :: [b] :: env) =
        [b ^ n] := by
      simp only [powerStep, repeat_power, mul_one]
      rfl
    rw [peak_copy hcopy]
    simpa only [Int.natAbs_pow] using hfinal
  apply max_le (le_max_left _ _) (le_trans ?_ (le_max_right _ _))
  exact max_le hi (max_le (hp.trans (max_le hbase (max_le hone hfinal))) hlast)

end WolfeSimplex.Execution.Code

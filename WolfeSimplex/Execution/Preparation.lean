import WolfeSimplex.Execution.GrowthRules
import WolfeSimplex.Execution.BirdPeak
import WolfeSimplex.Execution.AtomPeak
import WolfeSimplex.Execution.Resources
import WolfeSimplex.Execution.InitialBounds
import WolfeSimplex.Proofs.Shield

namespace WolfeSimplex.Execution
open Code
variable {m n : ℕ}

/-- Exactly five copies present the prepared LP in A,b,c order. -/
def finishCaches (m n : ℕ) : List Code :=
  [par (readAt 4 (List.range m)) (literal 1),
    par (readAt 4 (List.range n)) (literal 0),
    readAt 0 (List.range (n + 1)), readAt 2 (List.range (m + 1)),
    readAt 4 (List.range ((m + 1) * (n + 1)))]

def preparationCaches (e : Fin m → Fin n) (matrix : Code) : List Code :=
  [canonicalA m n, canonicalB m, canonicalC e, shieldCoefficient e, shieldWeight e,
    matrix] ++ finishCaches m n

theorem shieldCode_prefix (e : Fin m → Fin n) : shieldCode e =
    cacheChain [basisCode e, determinant m, gCode m]
      (cacheChain (preparationCaches e (shieldMatrix e)) (atomCode (m + 1) (n + 1))) := rfl

theorem weightedCode_prefix (e : Fin m → Fin n) (σ : Equiv.Perm (Fin n)) : weightedCode e σ =
    cacheChain [basisCode e, determinant m, gCode m]
      (cacheChain (preparationCaches e (weightedMatrix e σ)) (atomCode (m + 1) (n + 1))) := rfl

private theorem table_cert {r B q o : ℕ} (f : Fin r → Code) (hq : 1 ≤ q)
    (h : ∀ i, GrowthCert B q o (f i)) : GrowthCert B q o (table (List.ofFn f)) := by
  have hs := GrowthCert.table (List.finRange r) f q o hq (fun i _ ↦ h i)
  simpa only [List.finRange, List.map_ofFn, Function.comp_def] using hs

private theorem canonicalA_cert (m n B : ℕ) : GrowthCert B 2 (m + 1) (canonicalA m n) := by
  apply table_cert _ (by decide)
  intro ij
  have h := GrowthCert.sum (List.finRange m)
    (fun k ↦ mul (slot 0 (m * ij.divNat.val + k.val)) (slot 3 (n * k.val + ij.modNat.val)))
    2 0 (by decide) (by
      intro k _
      have hk := (GrowthCert.slot 0 (m * ij.divNat.val + k.val) B).mul
        (GrowthCert.slot 3 (n * k.val + ij.modNat.val) B)
      simpa using hk)
  simpa only [List.length_finRange, Nat.zero_add, one_mul] using h

private theorem canonicalB_cert (m B : ℕ) (hB : 2 ≤ B) :
    GrowthCert B 4 (2 * (m + 1)) (canonicalB m) := by
  apply table_cert _ (by decide)
  intro i
  have hs := GrowthCert.sum (List.finRange m)
    (fun k ↦ mul (slot 1 (m * i.val + k.val)) (slot 5 k.val)) 2 0 (by decide)
    (by
      intro k _
      have hk := (GrowthCert.slot 1 (m * i.val + k.val) B).mul (GrowthCert.slot 5 k.val B)
      simpa using hk)
  simp only [List.length_finRange, Nat.zero_add, one_mul] at hs
  have hp := (GrowthCert.literal (B := B) 2 hB).mul hs
  apply hp.mono (by decide)
  omega

private theorem canonicalC_cert (e : Fin m → Fin n) (B : ℕ) :
    GrowthCert B 2 (m + 2) (canonicalC e) := by
  apply table_cert _ (by decide)
  intro j
  have hs := GrowthCert.sum (List.finRange m)
    (fun i ↦ mul (slot 1 (n * i.val + j.val)) (slot 7 (e i).val)) 2 0 (by decide)
    (by
      intro i _
      have hi := (GrowthCert.slot 1 (n * i.val + j.val) B).mul (GrowthCert.slot 7 (e i).val B)
      simpa using hi)
  simp only [List.length_finRange, Nat.zero_add, one_mul] at hs
  have hp := ((GrowthCert.slot 3 0 B).abs.mul (GrowthCert.slot 7 j.val B)).sub hs
  apply hp.mono (by decide)
  omega

private theorem nonbasicMax_cert (e : Fin m → Fin n) (f : Fin n → Code) (B q o : ℕ)
    (hq : 1 ≤ q) (h : ∀ j, GrowthCert B q o (f j)) :
    GrowthCert B q (o + 2) (nonbasicMax e f) := by
  apply GrowthCert.maxList _ _ q (o + 1) hq
  intro j _
  split
  · exact (GrowthCert.literal 0 (by simp)).mono hq (by omega)
  · exact ((h j).max (GrowthCert.literal 0 (by simp))).mono (by omega) (by omega)

private theorem coefficient_cert (e : Fin m → Fin n) (B : ℕ) :
    GrowthCert B 2 (3 * m + 4) (shieldCoefficient e) := by
  have hs := nonbasicMax_cert e (fun j ↦ Code.sum ((List.finRange m).map fun i ↦
    mul (slot 1 i.val) (max (slot 2 (n * i.val + j.val)) (literal 0)))) B 2 (3 * m + 1)
    (by decide) (by
      intro j
      have ht := GrowthCert.sum (List.finRange m)
        (fun i ↦ mul (slot 1 i.val) (max (slot 2 (n * i.val + j.val)) (literal 0)))
        2 2 (by decide) (by
          intro i _
          have hc := (GrowthCert.slot 1 i.val B).mul
            ((GrowthCert.slot 2 (n * i.val + j.val) B).max (GrowthCert.literal 0 (by simp)))
          simpa using hc)
      simpa only [List.length_finRange, Nat.reduceAdd] using ht)
  have hp := (GrowthCert.slot 4 0 B).abs.add hs
  apply hp.mono (by decide)
  omega

private theorem weight_cert (e : Fin m → Fin n) (B : ℕ) :
    GrowthCert B 2 (m + 4) (shieldWeight e) := by
  have hs := nonbasicMax_cert e (fun j ↦ Code.sum ((List.finRange m).map fun i ↦
    mul (slot 3 (n * i.val + j.val)) (slot 3 (n * i.val + j.val)))) B 2 (m + 1)
    (by decide) (by
      intro j
      have ht := GrowthCert.sum (List.finRange m)
        (fun i ↦ mul (slot 3 (n * i.val + j.val)) (slot 3 (n * i.val + j.val)))
        2 0 (by decide) (by intro i _; simpa using
          (GrowthCert.slot 3 (n * i.val + j.val) B).mul (GrowthCert.slot 3 (n * i.val + j.val) B))
      simpa only [List.length_finRange, Nat.zero_add, one_mul] using ht)
  have hp := (GrowthCert.slot 0 0 B).add hs
  apply hp.mono (by decide)
  omega

private theorem shieldMatrix_cert (e : Fin m → Fin n) (B : ℕ) :
    GrowthCert B 2 2 (shieldMatrix e) := by
  apply table_cert _ (by decide)
  intro ij
  unfold shieldEntry
  split_ifs
  all_goals first
    | exact (GrowthCert.slot _ _ B).mono (by decide) (by decide)
    | exact (GrowthCert.literal 0 (by simp)).mono (by decide) (by decide)
    | exact (GrowthCert.slot _ _ B).neg.mono (by decide) (by decide)
    | exact (GrowthCert.slot _ _ B).abs.mono (by decide) (by decide)

private theorem weightedMatrix_cert (e : Fin m → Fin n) (σ : Equiv.Perm (Fin n))
    (B : ℕ) (hn : n + 1 ≤ B) : GrowthCert B 2 2 (weightedMatrix e σ) := by
  have hr (j : Fin n) : GrowthCert B 1 1 (literal (((σ j).val + 1 : ℕ) : ℤ)) :=
    GrowthCert.literal _ (by
      simp only [Int.natAbs_natCast]
      exact (by have := (σ j).isLt; omega : (σ j).val + 1 ≤ n + 1).trans hn)
  have hlast : GrowthCert B 1 1 (literal ((n + 1 : ℕ) : ℤ)) :=
    GrowthCert.literal _ (by simpa only [Int.natAbs_natCast] using hn)
  apply table_cert _ (by decide)
  intro ij
  unfold weightedEntry
  split_ifs
  all_goals first
    | exact (GrowthCert.slot _ _ B).mono (by decide) (by decide)
    | exact (GrowthCert.literal 0 (by simp)).mono (by decide) (by decide)
    | simpa using (hr _).mul (GrowthCert.slot 0 0 B)
    | simpa using ((hr _).mul (GrowthCert.slot 0 0 B)).neg
    | simpa using hlast.mul (GrowthCert.slot 0 0 B)

private theorem caches_cert (e : Fin m → Fin n) (matrix : Code) (B : ℕ)
    (hB : 2 ≤ B) (hm : GrowthCert B 2 2 matrix) :
    ∀ c ∈ preparationCaches e matrix,
      c.factor ≤ 4 * m + 4 ∧ c.offset ≤ 4 * m + 4 ∧ c.literalsBounded B := by
  have hp : ∀ c ∈ preparationCaches e matrix, GrowthCert B 4 (4 * m + 4) c := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (canonicalA_cert m n B).mono (by decide) (by omega)
      · exact (canonicalB_cert m B hB).mono le_rfl (by omega)
      · exact (canonicalC_cert e B).mono (by decide) (by omega)
      · exact (coefficient_cert e B).mono (by decide) (by omega)
      · exact (weight_cert e B).mono (by decide) (by omega)
      · exact hm.mono (by decide) (by omega)
    · simp only [finishCaches, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact ((GrowthCert.readAt _ _ B).par (GrowthCert.literal 1 (by omega))).mono
          (by decide) (by omega)
      · exact ((GrowthCert.readAt _ _ B).par (GrowthCert.literal 0 (by simp))).mono
          (by decide) (by omega)
      all_goals exact (GrowthCert.readAt _ _ B).mono (by decide) (by omega)
  intro c hc
  have hs := hp c hc
  exact ⟨hs.factor.trans (by omega), hs.offset, hs.literals⟩

private theorem finish_frames (M : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    (b : Fin m → ℤ) (c : Fin n → ℤ) (w a : List ℤ) (env : Env) :
    let Q : IntLP (m + 1) (n + 1) := ⟨M, Fin.snoc b 1, Fin.snoc c 0⟩
    frames (finishCaches m n) (pack M :: w :: a :: List.ofFn c :: List.ofFn b :: env) =
      lpInput Q ++ (List.ofFn Q.c :: List.ofFn Q.b ::
        pack M :: w :: a :: List.ofFn c :: List.ofFn b :: env) := by
  intro Q
  have hb : (par (readAt 4 (List.range m)) (literal 1)).eval
      (pack M :: w :: a :: List.ofFn c :: List.ofFn b :: env) = List.ofFn Q.b := by
    rw [eval_par, readAt_range 4 m (List.ofFn b) _ (by rfl) (by simp), eval_literal]
    simp only [Q, List.ofFn_succ_last, Fin.snoc_castSucc, Fin.snoc_last]
  have hc : (par (readAt 4 (List.range n)) (literal 0)).eval
      (List.ofFn Q.b :: pack M :: w :: a :: List.ofFn c :: List.ofFn b :: env) =
      List.ofFn Q.c := by
    rw [eval_par, readAt_range 4 n (List.ofFn c) _ (by rfl) (by simp), eval_literal]
    simp only [Q, List.ofFn_succ_last, Fin.snoc_castSucc, Fin.snoc_last]
  simp only [finishCaches, frames, hb, hc]
  rw [readAt_range 0 (n + 1) (List.ofFn Q.c) _ (by rfl) (by simp)]
  rw [readAt_range 2 (m + 1) (List.ofFn Q.b) _ (by rfl) (by simp)]
  rw [readAt_range 4 ((m + 1) * (n + 1)) (pack M) _ (by rfl) (by simp)]
  rfl

private theorem preparation_frames (P : IntLP m n) (e : Fin m → Fin n) (matrix : Code)
    (Q : IntLP (m + 1) (n + 1)) (env : Env)
    (hm : matrix.eval ([P.shieldW e] :: [P.shieldCoeff e] :: canonEnv P e env) = pack Q.A)
    (hb : Q.b = (P.shieldLP e).b) (hc : Q.c = (P.shieldLP e).c) :
    frames (preparationCaches e matrix)
      (pack (P.canonG e) :: [(P.basisMat e).det] :: pack (P.basisMat e) :: (lpInput P ++ env)) =
      lpInput Q ++ (List.ofFn Q.c :: List.ofFn Q.b ::
        pack Q.A :: [P.shieldW e] :: [P.shieldCoeff e] :: canonEnv P e env) := by
  have hm' := hm
  simp only [canonEnv] at hm'
  have ha := coefficient_eval P e env
  have hw := weight_eval P e env
  simp only [canonEnv] at ha hw
  simp only [preparationCaches, List.cons_append, List.nil_append, frames,
    canonicalA_eval P, canonicalB_eval P, canonicalC_eval P, ha, hw, hm']
  have hf := finish_frames Q.A (P.canonical e).b (P.canonical e).c
    [P.shieldW e] [P.shieldCoeff e]
    (pack (P.canonical e).A :: pack (P.canonG e) :: [(P.basisMat e).det] ::
      pack (P.basisMat e) :: (lpInput P ++ env))
  have hQ : (⟨Q.A, Fin.snoc (P.canonical e).b 1, Fin.snoc (P.canonical e).c 0⟩ :
      IntLP (m + 1) (n + 1)) = Q := by
    cases Q
    simp_all only [IntLP.shieldLP, IntLP.mk.injEq, and_self]
  rw [hQ] at hf
  exact hf

/-- A polynomial exponent bounding all preparation intermediates. The first
term covers eleven cache stages; the second covers the final atom program. -/
def preparationExponent (m : ℕ) : ℕ :=
  (4 * m + 5) ^ 11 * (m + 2) + (2 * m + 4) * 36 * (m + 2) ^ 2

private theorem prepared_peak (P : IntLP m n) (e : Fin m → Fin n) (matrix : Code)
    (Q : IntLP (m + 1) (n + 1))
    (hm : matrix.eval ([P.shieldW e] :: [P.shieldCoeff e] :: canonEnv P e []) = pack Q.A)
    (hb : Q.b = (P.shieldLP e).b) (hc : Q.c = (P.shieldLP e).c)
    (hcert : GrowthCert (preparationBase P) 2 2 matrix)
    (hQ : Q.maxEntry ≤ preparationBase P ^ (2 * m + 3)) :
    ((cacheChain [basisCode e, determinant m, gCode m]
      (cacheChain (preparationCaches e matrix) (atomCode (m + 1) (n + 1)))).run (lpInput P)).peak ≤
      preparationBase P ^ preparationExponent m := by
  let B := preparationBase P
  let q := 4 * m + 4
  let E := (q + 1) ^ 11 * (m + 2)
  let F := (2 * m + 4) * 36 * (m + 2) ^ 2
  let I := frames [basisCode e, determinant m, gCode m] (lpInput P)
  have hB : 2 ≤ B := (base_facts P).1
  have hB1 : 1 ≤ B := by omega
  have hi := initial_bounds P e
  have hs := frames_growth (preparationCaches e matrix) I B (m + 1) q hB
    (caches_cert e matrix B hB hcert) hi.2
  change prefixPeak (preparationCaches e matrix) I ≤ B ^ E ∧
    envBounded (frames (preparationCaches e matrix) I) (B ^ E) at hs
  have hbe : (basisCode e).eval (lpInput P) = pack (P.basisMat e) := by
    simpa only [List.append_nil] using basisCode_eval P e []
  have hI : I = pack (P.canonG e) :: [(P.basisMat e).det] ::
      pack (P.basisMat e) :: lpInput P := by
    simp only [I, frames, hbe, determinant_correct, gCode_eval P]
  let tail := List.ofFn Q.c :: List.ofFn Q.b :: pack Q.A ::
    [P.shieldW e] :: [P.shieldCoeff e] :: canonEnv P e []
  have hframes : frames (preparationCaches e matrix) I = lpInput Q ++ tail := by
    rw [hI]
    simpa only [List.append_nil] using preparation_frames P e matrix Q [] hm hb hc
  have hmB : m + 2 ≤ B := by
    have hu := P.two_le_maxEntry
    dsimp [B, preparationBase]
    have hmul := Nat.mul_le_mul_left (2 * (m + n + 2)) hu
    nlinarith
  have hbaseQ : (m + 2) * Q.maxEntry ≤ B ^ (2 * m + 4) := by
    calc _ ≤ B * B ^ (2 * m + 3) := Nat.mul_le_mul hmB hQ
         _ = _ := by rw [pow_succ]; ring
  have hatom : ((atomCode (m + 1) (n + 1)).run (frames (preparationCaches e matrix) I)).peak ≤
      B ^ F := by
    rw [hframes]
    apply (atomCode_peak Q (by omega) tail).trans
    apply (Q.N_sq_mul_K_le (by omega)).trans
    calc ((m + 1 + 1) * Q.maxEntry) ^ (36 * (m + 1 + 1) ^ 2) ≤
        (B ^ (2 * m + 4)) ^ (36 * (m + 2) ^ 2) := Nat.pow_le_pow_left hbaseQ _
         _ = _ := by rw [← pow_mul]; congr 1; dsimp [F]; ring
  have hE : m + 1 ≤ E := by
    have hpow : 1 ≤ (q + 1) ^ 11 := Nat.one_le_pow _ _ (by omega)
    exact (by omega : m + 1 ≤ m + 2).trans (Nat.le_mul_of_pos_left _ hpow)
  change _ ≤ B ^ (E + F)
  rw [prefix_peak, prefix_peak]
  exact max_le (hi.1.trans (Nat.pow_le_pow_right hB1 (by omega)))
    (max_le (hs.1.trans (Nat.pow_le_pow_right hB1 (by omega)))
      (hatom.trans (Nat.pow_le_pow_right hB1 (by omega))))

/-- All operands and results of unweighted shortest-start preparation. -/
theorem shieldCode_peak (P : IntLP m n) (e : Fin m → Fin n) (hm : 1 ≤ m) :
    ((shieldCode e).run (lpInput P)).peak ≤ preparationBase P ^ preparationExponent m := by
  rw [shieldCode_prefix]
  apply prepared_peak P e (shieldMatrix e) (P.shieldLP e)
  · exact table_matrix _ _ _ (fun i j ↦ shieldEntry_eval P e i j [])
  · rfl
  · rfl
  · exact shieldMatrix_cert e _
  · have hbase : (m + 1) * P.maxEntry ≤ preparationBase P := by
      dsimp [preparationBase]
      gcongr <;> omega
    exact (P.shieldLP_maxEntry_le e hm).trans ((Nat.pow_le_pow_left hbase _).trans
      (Nat.pow_le_pow_right (by have := (base_facts P).1; omega) (by omega)))

/-- All operands and results of weighted shortest-start preparation. -/
theorem weightedCode_peak (P : IntLP m n) (e : Fin m → Fin n)
    (σ : Equiv.Perm (Fin n)) (hm : 1 ≤ m) :
    ((weightedCode e σ).run (lpInput P)).peak ≤ preparationBase P ^ preparationExponent m := by
  rw [weightedCode_prefix]
  apply prepared_peak P e (weightedMatrix e σ) (P.weightedLP e σ)
  · exact table_matrix _ _ _ (fun i j ↦ weightedEntry_eval P e σ i j [])
  · rfl
  · rfl
  · exact weightedMatrix_cert e _ _ (base_facts P).2.2
  · have hbase : (m + 1) * P.maxEntry ≤ preparationBase P := by
      dsimp [preparationBase]
      gcongr <;> omega
    calc _ ≤ (n + 1) * ((m + 1) * P.maxEntry) ^ (2 * m + 2) :=
            P.weightedLP_maxEntry_le e σ hm
         _ ≤ preparationBase P * preparationBase P ^ (2 * m + 2) :=
            Nat.mul_le_mul (base_facts P).2.2 (Nat.pow_le_pow_left hbase _)
         _ = _ := by rw [pow_succ]; ring

/-- Signed width of every numeric operand/result, for either preparation path. -/
theorem preparation_width (P : IntLP m n) (c : Code)
    (h : (c.run (lpInput P)).peak ≤ preparationBase P ^ preparationExponent m) :
    1 + Nat.size (c.run (lpInput P)).peak ≤
      1 + preparationExponent m * Nat.size (preparationBase P) := by
  apply Nat.add_le_add_left
  exact IntLP.magnitude_bits_le (z := ((c.run (lpInput P)).peak : ℤ))
    (by unfold preparationExponent; positivity) (by simpa only [Int.natAbs_natCast] using h)

end WolfeSimplex.Execution

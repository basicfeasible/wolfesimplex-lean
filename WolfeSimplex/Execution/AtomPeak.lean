import WolfeSimplex.Execution.Atoms
import WolfeSimplex.Execution.ScalarBound
import WolfeSimplex.Construction.Peak

namespace WolfeSimplex.Execution
open Code Finset
variable {m n : ℕ}

private theorem scan_peak (block : ℕ) (f : Fin n → ℤ) (env : Env) (R : ℕ)
    (hblock : env[block]?.getD [] = List.ofFn f) (hv : ∀ i, (f i).natAbs ≤ R) :
    ((absoluteScan block n).run env).peak ≤ R := by
  have he (i : Fin n) : (slot block i.val).eval env = [f i] := by
    simp only [eval_slot, hblock, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]
  have hc (i : Fin n) : ScalarBound R env (abs (slot block i.val)) |f i| :=
    (ScalarBound.slot block i.val (f i) (hv i) (he i)).abs
  exact (maxList_peak (List.finRange n) (fun i ↦ abs (slot block i.val))
    (fun i ↦ |f i|) env R (fun i _ ↦ (hc i).value)
    (fun i _ ↦ (hc i).peak) (fun i _ ↦ (hc i).magnitude)).1

/-- Numeric inequalities used to bound the executed construction. These are
proved below from the paper's scale bounds, rather than supplied by a caller. -/
private structure AtomBound (P : IntLP m n) (R : ℕ) : Prop where
  two : 2 ≤ R
  dim : m ≤ R
  dimSucc : m + 1 ≤ R
  u : P.U ≤ R
  c : P.C.natAbs ≤ R
  cost : ∀ j, (P.c j).natAbs ≤ R
  a : ∀ i j, (P.A i j).natAbs ≤ R
  b : ∀ i, (P.b i).natAbs ≤ R
  gamma : ∀ j, (P.gamma j).natAbs ≤ R
  alpha : ∀ j i, (P.scaledAlpha j i).natAbs ≤ R
  t : P.T ≤ R
  k : P.K ≤ R
  h : P.H ≤ R
  n : P.N ≤ R
  twom : 2 * m ≤ R
  mu : m * P.U ≤ R
  powerT : (m * P.U) ^ (m + 1) ≤ R
  productT : 2 * m * (m * P.U) ^ m ≤ R
  productA : ∀ i j, ((P.T : ℤ) * P.A i j).natAbs ≤ R
  ksq : P.K * P.K ≤ R
  baseH : (m + 1) * (P.K * P.K) ≤ R
  powerH : ((m + 1) * (P.K * P.K)) ^ (m + 2) ≤ R
  hcube : P.H ^ 3 ≤ R
  hfour : P.H ^ 4 ≤ R
  q : 2 * m * P.H ^ 3 ≤ R
  factor : P.N * (2 * m * P.H ^ 3) ≤ R
  ngamma : ∀ j, ((P.N : ℤ) * P.gamma j).natAbs ≤ R
  falpha : ∀ j i, (((P.N * (2 * m * P.H ^ 3) : ℕ) : ℤ) * P.scaledAlpha j i).natAbs ≤ R

private theorem scale_bounds (P : IntLP m n) (hm : 1 ≤ m) :
    AtomBound P (P.N ^ 2 * P.K) := by
  let R := P.N ^ 2 * P.K
  rcases Construction.scalar_bounds P hm with
    ⟨hUT, hmT, h2mT, hmuT, hpowT, hTN, hK2H, hbaseH, hHN, hH3N, hqN, hNR, hTUR, h2R⟩
  have hTR : P.T ≤ R := hTN.trans hNR
  have hUR := hUT.trans hTR
  have hNpos : 1 ≤ P.N := Nat.one_le_iff_ne_zero.mpr (P.N_pos hm).ne'
  have hNN : P.N ≤ P.N ^ 2 := by nlinarith
  have hN2R : P.N ^ 2 ≤ R := by dsimp [R]; have := P.one_le_K; nlinarith
  have hT2R : P.T ^ 2 ≤ R := (Nat.pow_le_pow_left hTN 2).trans hN2R
  have hKR : P.K ≤ R := by dsimp [R]; nlinarith
  have hHR := hHN.trans hNR
  have hC : P.C.natAbs ≤ P.K := by
    simpa only [IntLP.gamma, Fin.snoc_last] using P.natAbs_gamma_le (Fin.last n)
  have hmaxc : (univ.sup fun j ↦ (P.c j).natAbs) ≤ P.K := by
    have he : P.C.natAbs = 1 + (univ.sup fun j ↦ (P.c j).natAbs) := by
      unfold IntLP.C
      change (((1 : ℕ) : ℤ) + ((univ.sup fun j ↦ (P.c j).natAbs : ℕ) : ℤ)).natAbs = _
      rw [← Nat.cast_add, Int.natAbs_natCast]
    rw [he] at hC
    omega
  have hcost : ∀ j, (P.c j).natAbs ≤ R := fun j ↦
    (Finset.le_sup (mem_univ j)).trans (hmaxc.trans hKR)
  have hpowExtra : (m * P.U) ^ (m + 1) ≤ R := by
    rw [pow_succ]
    exact (Nat.mul_le_mul hpowT hmuT).trans (by simpa only [pow_two] using hT2R)
  have hH2R : P.H ^ 2 ≤ R := (Nat.pow_le_pow_left hHN 2).trans hN2R
  have hHExtra : ((m + 1) * (P.K * P.K)) ^ (m + 2) ≤ R := by
    have he : ((m + 1) * (P.K * P.K)) ^ (m + 1) = P.H := by
      simp only [IntLP.H, pow_two]
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ, he]
    exact (Nat.mul_le_mul_left P.H (by simpa only [pow_two] using hbaseH)).trans
      (by simpa only [pow_two] using hH2R)
  have hH4 : P.H ^ 4 ≤ R := by
    calc P.H ^ 4 = P.H ^ 3 * P.H := by ring
         _ ≤ P.N * P.N := Nat.mul_le_mul hH3N hHN
         _ ≤ R := by simpa only [pow_two] using hN2R
  refine
    { two := h2R
      dim := hmT.trans hTR
      dimSucc := (by omega : m + 1 ≤ 2 * m).trans (h2mT.trans hTR)
      u := hUR
      c := hC.trans hKR
      cost := hcost
      a := fun i j ↦ (P.natAbs_A_le i j).trans hUR
      b := fun i ↦ (P.natAbs_b_le i).trans hUR
      gamma := fun j ↦ (P.natAbs_gamma_le j).trans hKR
      alpha := fun j i ↦ (P.natAbs_scaledAlpha_le j i).trans hKR
      t := hTR
      k := hKR
      h := hHR
      n := hNR
      twom := h2mT.trans hTR
      mu := hmuT.trans hTR
      powerT := hpowExtra
      productT := (by simp [IntLP.T] : 2 * m * (m * P.U) ^ m ≤ P.T).trans hTR
      productA := ?_
      ksq := by simpa only [pow_two] using hK2H.trans hHR
      baseH := by simpa only [pow_two] using hbaseH.trans hHR
      powerH := hHExtra
      hcube := hH3N.trans hNR
      hfour := hH4
      q := hqN.trans hNR
      factor := (Nat.mul_le_mul_left P.N hqN).trans (by simpa only [pow_two, R] using hN2R)
      ngamma := ?_
      falpha := ?_ }
  · intro i j
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    exact (Nat.mul_le_mul_left P.T (P.natAbs_A_le i j)).trans hTUR
  · intro j
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    exact (Nat.mul_le_mul_left P.N (P.natAbs_gamma_le j)).trans (Nat.mul_le_mul_right P.K hNN)
  · intro j i
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    calc P.N * (2 * m * P.H ^ 3) * (P.scaledAlpha j i).natAbs ≤ P.N * P.N * P.K :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hqN) (P.natAbs_scaledAlpha_le j i)
         _ = _ := by ring

private theorem u_peak (P : IntLP m n) (env : Env) (R : ℕ) (h : AtomBound P R) :
    ((uCode m n).run (lpInput P ++ env)).peak ≤ R := by
  let E := lpInput P ++ env
  have ha := scan_peak 0 (fun k : Fin (m * n) ↦ P.A k.divNat k.modNat) E R
    (by simp [E, lpInput, pack, Matrix.toArray]) (fun k ↦ h.a _ _)
  have hb := scan_peak 1 P.b E R (by simp [E, lpInput]) h.b
  have hea := absoluteScan_eval 0 (fun k : Fin (m * n) ↦ P.A k.divNat k.modNat) E
    (by simp [E, lpInput, pack, Matrix.toArray])
  have heb := absoluteScan_eval 1 P.b E (by simp [E, lpInput])
  have hva : (((Finset.univ.sup fun k : Fin (m * n) ↦ (P.A k.divNat k.modNat).natAbs : ℕ) : ℤ)).natAbs ≤ R := by
    simp only [Int.natAbs_natCast]
    exact Finset.sup_le (fun k _ ↦ h.a _ _)
  have hvb : (((Finset.univ.sup fun i : Fin m ↦ (P.b i).natAbs : ℕ) : ℤ)).natAbs ≤ R := by
    simp only [Int.natAbs_natCast]
    exact Finset.sup_le (fun i _ ↦ h.b i)
  exact ((ScalarBound.literal 1 (by simpa using (le_trans (by decide : 1 ≤ 2) h.two))).max
    ((ScalarBound.mk hea ha hva).max (ScalarBound.mk heb hb hvb))).peak

private theorem c_peak (P : IntLP m n) (u : ℤ) (env : Env) (R : ℕ) (h : AtomBound P R) :
    ((cCode n).run ([u] :: (lpInput P ++ env))).peak ≤ R := by
  let E := [u] :: (lpInput P ++ env)
  have hs := scan_peak 3 P.c E R (by simp [E, lpInput]) h.cost
  have he := absoluteScan_eval 3 P.c E (by simp [E, lpInput])
  have hv : (((Finset.univ.sup fun j : Fin n ↦ (P.c j).natAbs : ℕ) : ℤ)).natAbs ≤ R := by
    simp only [Int.natAbs_natCast]
    exact Finset.sup_le (fun j _ ↦ h.cost j)
  have hc : ((1 : ℤ) + (Finset.univ.sup fun j : Fin n ↦ (P.c j).natAbs : ℕ)).natAbs ≤ R := h.c
  exact ((ScalarBound.literal 1 (by simpa using (le_trans (by decide : 1 ≤ 2) h.two))).add
    (ScalarBound.mk he hs hv) hc).peak

private theorem t_peak (P : IntLP m n) (c : ℤ) (env : Env) (hm : 1 ≤ m)
    (R : ℕ) (h : AtomBound P R) :
    ((tCode m).run ([c] :: [(P.U : ℤ)] :: env)).peak ≤ R := by
  let E := [c] :: [(P.U : ℤ)] :: env
  have h2 : ScalarBound R E (literal 2) 2 := ScalarBound.literal 2 h.two
  have hM : ScalarBound R E (literal (m : ℤ)) (m : ℤ) :=
    ScalarBound.literal _ (by simpa using h.dim)
  have hU : ScalarBound R E (slot 1 0) (P.U : ℤ) :=
    ScalarBound.slot _ _ _ (by simpa using h.u) (by rfl)
  have hmu := hM.mul hU (by simpa only [Int.natAbs_mul, Int.natAbs_natCast] using h.mu)
  have hp := hmu.power 0 m (by
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    have := P.one_le_U; nlinarith) (by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using h.powerT)
  have hprod := (h2.mul hM (by simpa only [Int.natAbs_mul, Int.natAbs_natCast, show (2 : ℤ).natAbs = 2 from rfl] using h.twom)).mul hp (by
    simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, show (2 : ℤ).natAbs = 2 from rfl] using h.productT)
  have hz : ((2 : ℤ) * m * ((m : ℤ) * P.U) ^ m + 1).natAbs ≤ R := by
    have he : (2 : ℤ) * m * ((m : ℤ) * P.U) ^ m + 1 = P.T := by simp [IntLP.T]
    rw [he, Int.natAbs_natCast]
    exact h.t
  exact (hprod.add (ScalarBound.literal 1 (by simpa using (le_trans (by decide : 1 ≤ 2) h.two))) hz).peak

private theorem h_peak (P : IntLP m n) (env : Env) (R : ℕ) (h : AtomBound P R) :
    ((hCode m).run ([(P.K : ℤ)] :: env)).peak ≤ R := by
  let E := [(P.K : ℤ)] :: env
  have hK : ScalarBound R E (slot 0 0) (P.K : ℤ) :=
    ScalarBound.slot _ _ _ (by simpa using h.k) (by rfl)
  have hM : ScalarBound R E (literal ((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) :=
    ScalarBound.literal _ (by simpa only [Int.natAbs_natCast] using h.dimSucc)
  have hb := hM.mul (hK.mul hK (by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using h.ksq)) (by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using h.baseH)
  have hp := hb.power 0 (m + 1) (by
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    have := P.one_le_K
    nlinarith) (by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast, Nat.add_assoc] using h.powerH)
  exact hp.peak

private theorem n_peak (P : IntLP m n) (k a g : List ℤ) (env : Env) (R : ℕ)
    (h : AtomBound P R) :
    ((nCode m).run ([(P.H : ℤ)] :: k :: a :: g :: [(P.T : ℤ)] :: env)).peak ≤ R := by
  let E := [(P.H : ℤ)] :: k :: a :: g :: [(P.T : ℤ)] :: env
  have hH : ScalarBound R E (slot 0 0) (P.H : ℤ) :=
    ScalarBound.slot _ _ _ (by simpa using h.h) (by rfl)
  have hT : ScalarBound R E (slot 4 0) (P.T : ℤ) :=
    ScalarBound.slot _ _ _ (by simpa using h.t) (by rfl)
  have hM : ScalarBound R E (literal (m : ℤ)) (m : ℤ) :=
    ScalarBound.literal _ (by simpa using h.dim)
  have h2 : ScalarBound R E (literal 2) 2 := ScalarBound.literal 2 h.two
  have h2m := h2.mul hM (by simpa only [Int.natAbs_mul, Int.natAbs_natCast, show (2 : ℤ).natAbs = 2 from rfl] using h.twom)
  have htprod : ((2 : ℤ) * m * P.T).natAbs ≤ R := by
    -- It is no larger than N, since H is at least one.
    have hh : 1 ≤ P.H ^ 3 := Nat.one_le_pow _ _ P.one_le_H
    have hn : 2 * m * P.T ≤ P.N := by
      calc _ = (2 * m * P.T) * 1 := by ring
           _ ≤ (2 * m * P.T) * P.H ^ 3 := Nat.mul_le_mul_left _ hh
           _ = P.N := rfl
    simpa only [Int.natAbs_mul, Int.natAbs_natCast, show (2 : ℤ).natAbs = 2 from rfl] using hn.trans h.n
  have hc := hH.power 0 3 (by simpa using P.one_le_H) (by simpa using h.hfour)
  have hz : ((2 : ℤ) * m * P.T * (P.H : ℤ) ^ 3).natAbs ≤ R := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, show (2 : ℤ).natAbs = 2 from rfl, IntLP.N] using h.n
  exact ((h2m.mul hT htprod).mul hc hz).peak

private theorem factor_peak (P : IntLP m n) (env : Env) (R : ℕ) (h : AtomBound P R) :
    ((factorCode m).run ([(P.N : ℤ)] :: [(P.H : ℤ)] :: env)).peak ≤ R := by
  let E := [(P.N : ℤ)] :: [(P.H : ℤ)] :: env
  have hH : ScalarBound R E (slot 1 0) (P.H : ℤ) :=
    ScalarBound.slot _ _ _ (by simpa using h.h) (by rfl)
  have hN : ScalarBound R E (slot 0 0) (P.N : ℤ) :=
    ScalarBound.slot _ _ _ (by simpa using h.n) (by rfl)
  have hM : ScalarBound R E (literal (m : ℤ)) (m : ℤ) :=
    ScalarBound.literal _ (by simpa using h.dim)
  have h2 : ScalarBound R E (literal 2) 2 := ScalarBound.literal 2 h.two
  have h2m := h2.mul hM (by simpa only [Int.natAbs_mul, Int.natAbs_natCast, show (2 : ℤ).natAbs = 2 from rfl] using h.twom)
  have hc := hH.power 0 3 (by simpa using P.one_le_H) (by simpa using h.hfour)
  have hq := h2m.mul hc (by
    simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, show (2 : ℤ).natAbs = 2 from rfl] using h.q)
  exact (hN.mul hq (by
    simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, show (2 : ℤ).natAbs = 2 from rfl] using h.factor)).peak

private theorem gamma_peak (P : IntLP m n) (t u : ℤ) (env : Env) (R : ℕ)
    (h : AtomBound P R) :
    ((gammaCode n).run ([t] :: [P.C] :: [u] :: (lpInput P ++ env))).peak ≤ R := by
  apply peak_table
  intro c hc
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
  let E := [t] :: [P.C] :: [u] :: (lpInput P ++ env)
  have hC : ScalarBound R E (slot 1 0) P.C := ScalarBound.slot _ _ _ h.c (by rfl)
  induction j using Fin.lastCases with
  | last =>
    have hs := hC.add (ScalarBound.literal 0 (by simp)) (by simpa using h.c)
    simpa only [Fin.val_last, lt_self_iff_false, ite_false] using hs.peak
  | cast j =>
    have hcj : ScalarBound R E (slot 5 j.val) (P.c j) :=
      ScalarBound.slot _ _ _ (h.cost j) (by
        simp only [eval_slot, E, lpInput, List.getElem?_cons_succ, List.cons_append,
          List.getElem?_cons_zero, Option.getD_some, List.getElem?_ofFn, dite_eq_left j.isLt])
    have hz : (P.C + P.c j).natAbs ≤ R := by
      simpa only [IntLP.gamma, Fin.snoc_castSucc] using h.gamma j.castSucc
    simpa only [Fin.val_castSucc, ite_eq_left j.isLt] using (hC.add hcj hz).peak

private theorem alpha_peak (P : IntLP m n) (g : List ℤ) (c u : ℤ) (env : Env) (R : ℕ)
    (h : AtomBound P R) :
    ((alphaCode m n).run (g :: [(P.T : ℤ)] :: [c] :: [u] :: (lpInput P ++ env))).peak ≤ R := by
  apply peak_table
  intro code hc
  obtain ⟨ji, rfl⟩ := List.mem_ofFn.mp hc
  let E := g :: [(P.T : ℤ)] :: [c] :: [u] :: (lpInput P ++ env)
  let j := ji.divNat
  let i := ji.modNat
  have ht : ScalarBound R E (slot 1 0) (P.T : ℤ) :=
    ScalarBound.slot _ _ _ (by simpa using h.t) (by rfl)
  have hb : ScalarBound R E (slot 5 i.val) (P.b i) :=
    ScalarBound.slot _ _ _ (h.b i) (by
      simp only [eval_slot, E, lpInput, List.getElem?_cons_succ, List.cons_append,
        List.getElem?_cons_zero, Option.getD_some, List.getElem?_ofFn, dite_eq_left i.isLt])
  change ((sub (mul (slot 1 0) (if j.val < n then
    slot 4 (n * i.val + j.val) else literal 0)) (slot 5 i.val)).run E).peak ≤ R
  induction j using Fin.lastCases with
  | last =>
    have hp := ht.mul (ScalarBound.literal 0 (by simp)) (by simp)
    have hz : ((P.T : ℤ) * 0 - P.b i).natAbs ≤ R := by simpa using h.b i
    simpa only [Fin.val_last, lt_self_iff_false, ite_false] using (hp.sub hb hz).peak
  | cast j =>
    have ha : ScalarBound R E (slot 4 (n * i.val + j.val)) (P.A i j) :=
      ScalarBound.slot _ _ _ (h.a i j) (by
        simp only [eval_slot, E, lpInput, List.getElem?_cons_succ, List.cons_append,
          List.getElem?_cons_zero, Option.getD_some]
        exact congrArg (fun z : ℤ ↦ [z]) (pack_get _ i j))
    have hz : ((P.T : ℤ) * P.A i j - P.b i).natAbs ≤ R := by
      simpa only [IntLP.scaledAlpha, Fin.snoc_castSucc] using h.alpha j.castSucc i
    simpa only [Fin.val_castSucc, ite_eq_left j.isLt] using ((ht.mul ha (h.productA i j)).sub hb hz).peak

private theorem k_peak (P : IntLP m n) (env : Env) (R : ℕ) (h : AtomBound P R) :
    ((kCode m n).run (pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) ::
      List.ofFn P.gamma :: env)).peak ≤ R := by
  let E := pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) :: List.ofFn P.gamma :: env
  have ha := scan_peak 0 (fun k : Fin ((n + 1) * m) ↦ P.scaledAlpha k.divNat k.modNat) E R
    (by simp [E, pack, Matrix.toArray]) (fun _ ↦ h.alpha _ _)
  have hg := scan_peak 1 P.gamma E R (by rfl) h.gamma
  have hea := absoluteScan_eval 0
    (fun k : Fin ((n + 1) * m) ↦ P.scaledAlpha k.divNat k.modNat) E
    (by simp [E, pack, Matrix.toArray])
  have heg := absoluteScan_eval 1 P.gamma E (by rfl)
  have hva : (((univ.sup fun k : Fin ((n + 1) * m) ↦
      (P.scaledAlpha k.divNat k.modNat).natAbs : ℕ) : ℤ)).natAbs ≤ R := by
    simp only [Int.natAbs_natCast]
    exact Finset.sup_le (fun k _ ↦ h.alpha _ _)
  have hvg : (((univ.sup fun j : Fin (n + 1) ↦ (P.gamma j).natAbs : ℕ) : ℤ)).natAbs ≤ R := by
    simp only [Int.natAbs_natCast]
    exact Finset.sup_le (fun j _ ↦ h.gamma j)
  exact ((ScalarBound.literal 1 (by simpa using (le_trans (by decide : 1 ≤ 2) h.two))).max
    ((ScalarBound.mk hea ha hva).max (ScalarBound.mk heg hg hvg))).peak

private theorem output_peak (P : IntLP m n) (hh kk : List ℤ) (env : Env) (R : ℕ)
    (h : AtomBound P R) :
    ((outputCode m n).run
      ([((P.N * (2 * m * P.H ^ 3) : ℕ) : ℤ)] :: [(P.N : ℤ)] :: hh :: kk ::
        pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) :: List.ofFn P.gamma :: env)).peak ≤ R := by
  apply peak_table
  intro code hc
  obtain ⟨ji, rfl⟩ := List.mem_ofFn.mp hc
  let E := [((P.N * (2 * m * P.H ^ 3) : ℕ) : ℤ)] :: [(P.N : ℤ)] :: hh :: kk ::
    pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) :: List.ofFn P.gamma :: env
  let j := ji.divNat
  let i := ji.modNat
  change ((if i.val = 0 then mul (slot 1 0) (slot 5 j.val)
    else mul (slot 0 0) (slot 4 (m * j.val + (i.val - 1)))).run E).peak ≤ R
  induction i using Fin.cases with
  | zero =>
    have hn : ScalarBound R E (slot 1 0) (P.N : ℤ) :=
      ScalarBound.slot _ _ _ (by simpa using h.n) (by rfl)
    have hg : ScalarBound R E (slot 5 j.val) (P.gamma j) :=
      ScalarBound.slot _ _ _ (h.gamma j) (by
        simp only [eval_slot, E, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.getD_some, List.getElem?_ofFn, dite_eq_left j.isLt])
    simpa only [Fin.val_zero, eq_self_iff_true, ite_true] using (hn.mul hg (h.ngamma j)).peak
  | succ i =>
    have hf : ScalarBound R E (slot 0 0) ((P.N * (2 * m * P.H ^ 3) : ℕ) : ℤ) :=
      ScalarBound.slot _ _ _ (by simpa only [Int.natAbs_natCast] using h.factor) (by rfl)
    have ha : ScalarBound R E (slot 4 (m * j.val + i.val)) (P.scaledAlpha j i) :=
      ScalarBound.slot _ _ _ (h.alpha j i) (by
        simp only [eval_slot, E, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.getD_some]
        exact congrArg (fun z : ℤ ↦ [z]) (pack_get _ j i))
    simpa only [Fin.val_succ, Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, ite_false] using (hf.mul ha (h.falpha j i)).peak

set_option maxHeartbeats 2000000 in
-- Normalize the nested cache environments in the complete interpreter schedule.
/-- Every numeric operand/result of the interpreted atom program satisfies the
same magnitude bound as the construction certificate. -/
theorem atomCode_peak (P : IntLP m n) (hm : 1 ≤ m) (env : Env) :
    ((atomCode m n).run (lpInput P ++ env)).peak ≤ P.N ^ 2 * P.K := by
  have h := scale_bounds P hm
  unfold atomCode
  rw [peak_extend, uCode_eval P]
  apply max_le (u_peak P _ _ h)
  rw [peak_extend, cCode_eval P]
  apply max_le (c_peak P _ _ _ h)
  rw [peak_extend, tCode_eval P]
  apply max_le (t_peak P _ _ hm _ h)
  rw [peak_extend, gammaCode_eval P]
  apply max_le (gamma_peak P _ _ _ _ h)
  rw [peak_extend, alphaCode_eval P]
  apply max_le (alpha_peak P _ _ _ _ _ h)
  rw [peak_extend, kCode_eval P]
  apply max_le (k_peak P _ _ h)
  rw [peak_extend, hCode_eval P]
  apply max_le (h_peak P _ _ h)
  rw [peak_extend, nCode_eval P]
  apply max_le (n_peak P _ _ _ _ _ h)
  rw [peak_extend, factorCode_eval P]
  exact max_le (factor_peak P _ _ h) (output_peak P _ _ _ _ h)

end WolfeSimplex.Execution

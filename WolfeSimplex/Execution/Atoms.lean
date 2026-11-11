import WolfeSimplex.Execution.Bird
import WolfeSimplex.Construction.Correctness

/-!
# The atom construction as executable first-order code

Only dimensions control program generation. Coefficients are input array cells,
not Lean expressions evaluated while constructing the program. Each cached scalar
or table is materialized once, in a new immutable environment frame.
-/

namespace WolfeSimplex.Execution

open Code
variable {m n : ℕ}

/-- Dense input arrays for the integer LP. -/
def lpInput (P : IntLP m n) : Env := [pack P.A, List.ofFn P.b, List.ofFn P.c]

def absoluteScan (block count : ℕ) : Code :=
  maxList ((List.finRange count).map fun k ↦ abs (slot block k.val))

def uCode (m n : ℕ) : Code :=
  max (literal 1) (max (absoluteScan 0 (m * n)) (absoluteScan 1 m))

def cCode (n : ℕ) : Code := add (literal 1) (absoluteScan 3 n)

def tCode (m : ℕ) : Code :=
  add (mul (mul (literal 2) (literal m))
    (power 0 (mul (literal m) (slot 1 0)) m)) (literal 1)

def gammaCode (n : ℕ) : Code :=
  table (List.ofFn fun j : Fin (n + 1) ↦
    add (slot 1 0) (if j.val < n then slot 5 j.val else literal 0))

def alphaCode (m n : ℕ) : Code :=
  table (List.ofFn fun ji : Fin ((n + 1) * m) ↦
    sub (mul (slot 1 0) (if ji.divNat.val < n then
      slot 4 (n * ji.modNat.val + ji.divNat.val) else literal 0)) (slot 5 ji.modNat.val))

def kCode (m n : ℕ) : Code :=
  max (literal 1) (max (absoluteScan 0 ((n + 1) * m)) (absoluteScan 1 (n + 1)))

def hCode (m : ℕ) : Code :=
  power 0 (mul (literal (m + 1 : ℕ)) (mul (slot 0 0) (slot 0 0))) (m + 1)

def nCode (m : ℕ) : Code :=
  mul (mul (mul (literal 2) (literal m)) (slot 4 0)) (power 0 (slot 0 0) 3)

def factorCode (m : ℕ) : Code :=
  mul (slot 0 0) (mul (mul (literal 2) (literal m)) (power 0 (slot 1 0) 3))

def outputCode (m n : ℕ) : Code :=
  table (List.ofFn fun ji : Fin ((n + 1) * (m + 1)) ↦
    if ji.modNat.val = 0 then mul (slot 1 0) (slot 5 ji.divNat.val)
    else mul (slot 0 0) (slot 4 (m * ji.divNat.val + (ji.modNat.val - 1))))

/-- All computation—including the powers—is represented by first-order syntax. -/
def atomCode (m n : ℕ) : Code :=
  extend (uCode m n) (extend (cCode n) (extend (tCode m)
    (extend (gammaCode n) (extend (alphaCode m n) (extend (kCode m n)
      (extend (hCode m) (extend (nCode m) (extend (factorCode m) (outputCode m n)))))))))

theorem table_ofFn_eval {r : ℕ} (f : Fin r → Code) (v : Fin r → ℤ) (env : Env)
    (h : ∀ i, (f i).eval env = [v i]) :
    (table (List.ofFn f)).eval env = List.ofFn v := by
  have ht := table_eval_values (List.finRange r) f (fun i ↦ [v i]) env
    (fun i _ ↦ h i)
  simpa only [List.finRange, List.map_ofFn, Function.comp_def, ← List.map_eq_flatMap] using ht

theorem fold_max_le (xs : List ℕ) (b : ℕ) :
    xs.foldr Max.max 0 ≤ b ↔ ∀ z ∈ xs, z ≤ b := by
  induction xs <;> simp_all [max_le_iff]

theorem mem_le_fold_max {xs : List ℕ} {z : ℕ} (hz : z ∈ xs) :
    z ≤ xs.foldr Max.max 0 := by
  induction xs with
  | nil => simp at hz
  | cons a xs ih =>
    rcases List.mem_cons.mp hz with rfl | hz
    · exact le_max_left _ _
    · exact (ih hz).trans (le_max_right _ _)

theorem fold_max_ofFn (v : Fin n → ℕ) :
    (List.ofFn v).foldr Max.max 0 = Finset.univ.sup v := by
  apply Nat.le_antisymm
  · apply (fold_max_le _ _).mpr
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact Finset.le_sup (Finset.mem_univ i)
  · exact Finset.sup_le (fun i _ ↦ mem_le_fold_max (List.mem_ofFn.mpr ⟨i, rfl⟩))

theorem fold_max_cast (xs : List ℕ) :
    (xs.map (fun z : ℕ ↦ (z : ℤ))).foldr Max.max 0 = (xs.foldr Max.max 0 : ℕ) := by
  induction xs with
  | nil => rfl
  | cons z xs ih => simp only [List.map_cons, List.foldr_cons, ih, Nat.cast_max]

theorem scan_ofFn (f : Fin n → ℤ) :
    ((List.ofFn fun i ↦ |f i|).foldr Max.max 0) =
      ((Finset.univ.sup fun i ↦ (f i).natAbs : ℕ) : ℤ) := by
  have heq : List.ofFn (fun i ↦ |f i|) =
      (List.ofFn (fun i ↦ (f i).natAbs)).map (fun z : ℕ ↦ (z : ℤ)) := by
    simp only [List.map_ofFn]
    congr 1
    funext i
    exact Int.abs_eq_natAbs (f i)
  rw [heq, fold_max_cast, fold_max_ofFn]

theorem absoluteScan_eval (block : ℕ) (f : Fin n → ℤ) (env : Env)
    (hblock : env[block]?.getD [] = List.ofFn f) :
    (absoluteScan block n).eval env =
      [((Finset.univ.sup fun i ↦ (f i).natAbs : ℕ) : ℤ)] := by
  have h := maxList_eval (List.finRange n) (fun k ↦ abs (slot block k.val))
    (fun k : Fin n ↦ |f k|) env (by
      intro k _
      apply abs_eval
      simp only [eval_slot, hblock]
      simp [List.getElem?_ofFn, k.isLt])
  simpa only [absoluteScan, List.finRange, List.map_ofFn, Function.comp_def,
    scan_ofFn] using h

theorem sup_flat (A : Matrix (Fin m) (Fin n) ℤ) :
    (Finset.univ.sup fun k : Fin (m * n) ↦ (A k.divNat k.modNat).natAbs) =
      Finset.univ.sup (fun ij : Fin m × Fin n ↦ (A ij.1 ij.2).natAbs) := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro k _
    exact Finset.le_sup (f := fun ij : Fin m × Fin n ↦ (A ij.1 ij.2).natAbs)
      (Finset.mem_univ (k.divNat, k.modNat))
  · apply Finset.sup_le
    rintro ⟨i, j⟩ _
    have h := Finset.le_sup
      (f := fun k : Fin (m * n) ↦ (A k.divNat k.modNat).natAbs)
      (Finset.mem_univ (Fin.mkDivMod i j))
    simpa using h

theorem uCode_eval (P : IntLP m n) (env : Env) :
    (uCode m n).eval (lpInput P ++ env) = [(P.U : ℤ)] := by
  have ha := absoluteScan_eval 0 (fun k : Fin (m * n) ↦ P.A k.divNat k.modNat)
    (lpInput P ++ env) (by simp [lpInput, pack, Matrix.toArray])
  have hb := absoluteScan_eval 1 P.b (lpInput P ++ env) (by simp [lpInput])
  have h := max_eval (eval_literal 1 _)
    (max_eval ha hb)
  simpa only [uCode, Code.max, binaryValue, sup_flat, IntLP.U, Nat.cast_max,
    Nat.cast_one] using h

theorem cCode_eval (P : IntLP m n) (u : ℤ) (env : Env) :
    (cCode n).eval ([u] :: (lpInput P ++ env)) = [P.C] := by
  have hc := absoluteScan_eval 3 P.c ([u] :: (lpInput P ++ env)) (by simp [lpInput])
  simpa only [cCode, Code.add, binaryValue, IntLP.C] using
    add_eval (eval_literal 1 _) hc

theorem tCode_eval (P : IntLP m n) (c : ℤ) (env : Env) :
    (tCode m).eval ([c] :: [P.U] :: env) = [(P.T : ℤ)] := by
  have hu : (slot 1 0).eval ([c] :: [P.U] :: env) = [(P.U : ℤ)] := rfl
  have hbase := mul_eval (eval_literal (m : ℤ) _) hu
  have hp := power_eval 0 m _ _ _ hbase
  have h := add_eval
    (mul_eval
      (mul_eval (eval_literal 2 _) (eval_literal (m : ℤ) _)) hp)
    (eval_literal 1 _)
  simpa only [tCode, Code.add, Code.mul, binaryValue, IntLP.T, Nat.cast_add,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] using h

theorem gammaCode_eval (P : IntLP m n) (t u : ℤ) (env : Env) :
    (gammaCode n).eval ([t] :: [P.C] :: [u] :: (lpInput P ++ env)) = List.ofFn P.gamma := by
  apply table_ofFn_eval
  intro j
  have hc : (slot 1 0).eval ([t] :: [P.C] :: [u] :: (lpInput P ++ env)) = [P.C] := rfl
  induction j using Fin.lastCases with
  | last =>
    simpa [gammaCode, IntLP.gamma] using
      add_eval hc (eval_literal 0 _)
  | cast j =>
    have hj : (slot 5 j.val).eval ([t] :: [P.C] :: [u] :: (lpInput P ++ env)) = [P.c j] := by
      simp [eval_slot, lpInput, j.isLt]
    simpa [gammaCode, IntLP.gamma, j.isLt] using add_eval hc hj

theorem alphaCode_eval (P : IntLP m n) (g : List ℤ) (c u : ℤ) (env : Env) :
    (alphaCode m n).eval (g :: [P.T] :: [c] :: [u] :: (lpInput P ++ env)) =
      pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) := by
  unfold alphaCode
  have ht := table_ofFn_eval
    (fun ji : Fin ((n + 1) * m) ↦
      sub (mul (slot 1 0) (if ji.divNat.val < n then
        slot 4 (n * ji.modNat.val + ji.divNat.val) else literal 0)) (slot 5 ji.modNat.val))
    (fun ji : Fin ((n + 1) * m) ↦ P.scaledAlpha ji.divNat ji.modNat)
    (g :: [P.T] :: [c] :: [u] :: (lpInput P ++ env)) ?_
  · simpa [pack, Matrix.toArray] using ht
  · intro ji
    let j := ji.divNat
    let i := ji.modNat
    have hT : (slot 1 0).eval (g :: [P.T] :: [c] :: [u] :: (lpInput P ++ env)) = [(P.T : ℤ)] := rfl
    have hb : (slot 5 i.val).eval (g :: [P.T] :: [c] :: [u] :: (lpInput P ++ env)) = [P.b i] := by
      simp [eval_slot, lpInput, i.isLt]
    change (sub (mul (slot 1 0) (if j.val < n then slot 4 (n * i.val + j.val)
      else literal 0)) (slot 5 i.val)).eval _ = [P.scaledAlpha j i]
    induction j using Fin.lastCases with
    | last =>
      simpa [IntLP.scaledAlpha] using
        sub_eval (mul_eval hT (eval_literal 0 _)) hb
    | cast j =>
      have ha : (slot 4 (n * i.val + j.val)).eval
          (g :: [P.T] :: [c] :: [u] :: (lpInput P ++ env)) = [P.A i j] := by
        simp only [eval_slot, lpInput, List.cons_append, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.getD_some]
        rw [pack_get]
      simpa [IntLP.scaledAlpha, j.isLt] using
        sub_eval (mul_eval hT ha) hb

theorem kCode_eval (P : IntLP m n) (env : Env) :
    (kCode m n).eval (pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) ::
      List.ofFn P.gamma :: env) = [(P.K : ℤ)] := by
  let a : ℕ := Finset.univ.sup fun k : Fin ((n + 1) * m) ↦
    (P.scaledAlpha k.divNat k.modNat).natAbs
  let g : ℕ := Finset.univ.sup fun j : Fin (n + 1) ↦ (P.gamma j).natAbs
  have hk : Max.max 1 (Max.max a g) = P.K := by
    apply Nat.le_antisymm
    · refine max_le P.one_le_K (max_le ?_ ?_)
      · exact Finset.sup_le (fun k _ ↦ P.natAbs_scaledAlpha_le _ _)
      · exact Finset.sup_le (fun j _ ↦ P.natAbs_gamma_le j)
    · unfold IntLP.K
      apply Finset.sup_le
      intro j _
      refine max_le ?_ (max_le ?_ (le_max_left _ _))
      · exact (Finset.le_sup (Finset.mem_univ j)).trans
          ((le_max_right a g).trans (le_max_right 1 (Max.max a g)))
      · apply Finset.sup_le
        intro i _
        have h := Finset.le_sup
          (f := fun k : Fin ((n + 1) * m) ↦ (P.scaledAlpha k.divNat k.modNat).natAbs)
          (Finset.mem_univ (Fin.mkDivMod j i))
        have hh : (P.scaledAlpha j i).natAbs ≤ a := by simpa using h
        exact hh.trans ((le_max_left a g).trans (le_max_right 1 (Max.max a g)))
  have ha := absoluteScan_eval 0
    (fun k : Fin ((n + 1) * m) ↦ P.scaledAlpha k.divNat k.modNat)
    (pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) :: List.ofFn P.gamma :: env)
    (by simp [pack, Matrix.toArray])
  have hg := absoluteScan_eval 1 P.gamma
    (pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) :: List.ofFn P.gamma :: env) (by simp)
  have h : (kCode m n).eval (pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) ::
      List.ofFn P.gamma :: env) = [Max.max (1 : ℤ) (Max.max (a : ℤ) (g : ℤ))] :=
    max_eval (eval_literal 1 _) (max_eval ha hg)
  apply h.trans
  simpa only [Nat.cast_max, Nat.cast_one] using congrArg (fun z : ℕ ↦ [(z : ℤ)]) hk

theorem hCode_eval (P : IntLP m n) (env : Env) :
    (hCode m).eval ([(P.K : ℤ)] :: env) = [(P.H : ℤ)] := by
  have hk : (slot 0 0).eval ([(P.K : ℤ)] :: env) = [(P.K : ℤ)] := rfl
  have hb := mul_eval (eval_literal ((m + 1 : ℕ) : ℤ) _) (mul_eval hk hk)
  simpa only [hCode, IntLP.H, Nat.cast_pow, Nat.cast_mul, pow_two] using
    power_eval 0 (m + 1) _ _ _ hb

theorem nCode_eval (P : IntLP m n) (k : List ℤ) (env : Env) :
    (nCode m).eval ([(P.H : ℤ)] :: k ::
      pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) :: List.ofFn P.gamma ::
      [(P.T : ℤ)] :: env) = [(P.N : ℤ)] := by
  have hh : (slot 0 0).eval ([(P.H : ℤ)] :: k ::
      pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) :: List.ofFn P.gamma ::
      [(P.T : ℤ)] :: env) = [(P.H : ℤ)] := rfl
  have ht : (slot 4 0).eval ([(P.H : ℤ)] :: k ::
      pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) :: List.ofFn P.gamma ::
      [(P.T : ℤ)] :: env) = [(P.T : ℤ)] := rfl
  simpa only [nCode, IntLP.N, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    mul_eval (mul_eval (mul_eval (eval_literal 2 _) (eval_literal (m : ℤ) _)) ht)
      (power_eval 0 3 _ _ _ hh)

theorem factorCode_eval (P : IntLP m n) (env : Env) :
    (factorCode m).eval ([(P.N : ℤ)] :: [(P.H : ℤ)] :: env) =
      [((P.N * (2 * m * P.H ^ 3) : ℕ) : ℤ)] := by
  have hn : (slot 0 0).eval ([(P.N : ℤ)] :: [(P.H : ℤ)] :: env) = [(P.N : ℤ)] := rfl
  have hh : (slot 1 0).eval ([(P.N : ℤ)] :: [(P.H : ℤ)] :: env) = [(P.H : ℤ)] := rfl
  simpa only [factorCode, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    mul_eval hn (mul_eval (mul_eval (eval_literal 2 _) (eval_literal (m : ℤ) _))
      (power_eval 0 3 _ _ _ hh))

/-- Integer form of the paper's atom coordinates. -/
def integerAtoms (P : IntLP m n) : Matrix (Fin (n + 1)) (Fin (m + 1)) ℤ :=
  fun j ↦ Fin.cons ((P.N : ℤ) * P.gamma j)
    (fun i ↦ ((P.N * (2 * m * P.H ^ 3) : ℕ) : ℤ) * P.scaledAlpha j i)

theorem outputCode_eval (P : IntLP m n) (h k : List ℤ) (env : Env) :
    (outputCode m n).eval
      ([((P.N * (2 * m * P.H ^ 3) : ℕ) : ℤ)] :: [(P.N : ℤ)] :: h :: k ::
        pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) :: List.ofFn P.gamma :: env) =
      pack (integerAtoms P) := by
  unfold outputCode
  rw [show pack (integerAtoms P) = List.ofFn
    (fun ji : Fin ((n + 1) * (m + 1)) ↦ integerAtoms P ji.divNat ji.modNat) by simp [pack, Matrix.toArray]]
  apply table_ofFn_eval
  intro ji
  let j := ji.divNat
  let i := ji.modNat
  change (if i.val = 0 then mul (slot 1 0) (slot 5 j.val)
    else mul (slot 0 0) (slot 4 (m * j.val + (i.val - 1)))).eval _ =
      [integerAtoms P j i]
  induction i using Fin.cases with
  | zero =>
    have hg : (slot 5 j.val).eval
      ([((P.N * (2 * m * P.H ^ 3) : ℕ) : ℤ)] :: [(P.N : ℤ)] :: h :: k ::
        pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) :: List.ofFn P.gamma :: env) =
        [P.gamma j] := by
      simp only [eval_slot, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
      rw [List.getElem?_ofFn]
      simp only [dite_eq_left j.isLt, Option.getD_some]
    simpa [integerAtoms] using mul_eval (by rfl) hg
  | succ i =>
    have ha : (slot 4 (m * j.val + i.val)).eval
      ([((P.N * (2 * m * P.H ^ 3) : ℕ) : ℤ)] :: [(P.N : ℤ)] :: h :: k ::
        pack (fun j : Fin (n + 1) ↦ P.scaledAlpha j) :: List.ofFn P.gamma :: env) =
        [P.scaledAlpha j i] := by
      simp only [eval_slot, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
      exact congrArg List.singleton (pack_get _ j i)
    simpa [integerAtoms] using mul_eval (by rfl) ha

/-- Interpreter correctness, including every cached scalar and output cell. -/
theorem atomCode_correct (P : IntLP m n) (env : Env) :
    (atomCode m n).eval (lpInput P ++ env) = pack (integerAtoms P) := by
  simp only [atomCode, eval_extend, uCode_eval, cCode_eval, tCode_eval,
    gammaCode_eval, alphaCode_eval, kCode_eval, hCode_eval, nCode_eval, factorCode_eval]
  exact outputCode_eval P _ _ _

/-- The first-order program computes the actual real point set in the paper. -/
theorem integerAtoms_correct (P : IntLP m n) (j : Fin (n + 1)) (i : Fin (m + 1)) :
    (integerAtoms P j i : ℝ) = P.atom j i := by
  induction i using Fin.cases with
  | zero => simp [integerAtoms, IntLP.atom_zero]
  | succ i =>
    rw [IntLP.atom_succ, IntLP.N_sq_mul_alpha]
    simp only [integerAtoms, Fin.cons_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]

theorem absoluteScan_size (block count : ℕ) :
    (absoluteScan block count).size ≤ 7 * count + 1 := by
  have h := maxList_size_le (List.finRange count) (fun k ↦ abs (slot block k.val))
    4 (by simp)
  simpa [absoluteScan, mul_comm] using h

/-- The generated straight-line program has polynomial size in the dimensions.
All coefficient-dependent arithmetic happens during interpretation. -/
theorem atomCode_size (m n : ℕ) : (atomCode m n).size ≤ 400 * (m + n + 1) ^ 2 := by
  have hu : (uCode m n).size ≤ 7 * (m * n) + 7 * m + 9 := by
    have ha := absoluteScan_size 0 (m * n)
    have hb := absoluteScan_size 1 m
    simp only [uCode, size_max, size] at *
    omega
  have hc : (cCode n).size ≤ 7 * n + 5 := by
    have h := absoluteScan_size 3 n
    simp only [cCode, size_add, size]
    omega
  have ht : (tCode m).size = 11 * m + 30 := by
    simp [tCode, size]; ring
  have hg : (gammaCode n).size ≤ 8 * (n + 1) + 1 := by
    have h := table_size_le (List.finRange (n + 1))
      (fun j ↦ add (slot 1 0) (if j.val < n then slot 5 j.val else literal 0)) 7
      (by intro j _; split <;> simp [size])
    simpa only [gammaCode, List.finRange, List.map_ofFn, Function.comp_def, List.length_finRange, List.length_ofFn, Nat.mul_comm] using h
  have ha : (alphaCode m n).size ≤ 13 * ((n + 1) * m) + 1 := by
    have h := table_size_le (List.finRange ((n + 1) * m))
      (fun ji ↦ sub (mul (slot 1 0) (if ji.divNat.val < n then
        slot 4 (n * ji.modNat.val + ji.divNat.val) else literal 0)) (slot 5 ji.modNat.val)) 12
      (by intro ji _; split <;> simp [size])
    simpa only [alphaCode, List.finRange, List.map_ofFn, Function.comp_def, List.length_finRange, List.length_ofFn, Nat.mul_comm] using h
  have hk : (kCode m n).size ≤ 7 * ((n + 1) * m) + 7 * (n + 1) + 9 := by
    have ha := absoluteScan_size 0 ((n + 1) * m)
    have hg := absoluteScan_size 1 (n + 1)
    simp only [kCode, size_max, size]
    omega
  have hh : (hCode m).size = 11 * m + 34 := by simp [hCode, size]; ring
  have hn : (nCode m).size = 60 := by simp [nCode, size]
  have hf : (factorCode m).size = 60 := by simp [factorCode, size]
  have ho : (outputCode m n).size ≤ 8 * ((n + 1) * (m + 1)) + 1 := by
    have h := table_size_le (List.finRange ((n + 1) * (m + 1)))
      (fun ji ↦ if ji.modNat.val = 0 then mul (slot 1 0) (slot 5 ji.divNat.val)
        else mul (slot 0 0) (slot 4 (m * ji.divNat.val + (ji.modNat.val - 1)))) 7
      (by intro ji _; split <;> simp [size])
    simpa only [outputCode, List.finRange, List.map_ofFn, Function.comp_def, List.length_finRange, List.length_ofFn, Nat.mul_comm] using h
  simp only [atomCode, size]
  nlinarith [Nat.zero_le (m * m), Nat.zero_le (n * n)]

/-- Actual interpreter work, including input reads and cache/output allocation. -/
theorem atomCode_work (P : IntLP m n) :
    ((atomCode m n).run (lpInput P)).work ≤
      2000000 * (m + n + 1) ^ 4 := by
  have hw := work_bound (atomCode m n) (lpInput P)
  have hs := atomCode_size m n
  have hd : 1 ≤ m + n + 1 := by omega
  have hp : 1 ≤ (m + n + 1) ^ 2 := Nat.one_le_pow _ _ hd
  have hlen : (lpInput P).length = 3 := rfl
  rw [hlen] at hw
  calc _ ≤ 10 * (400 * (m + n + 1) ^ 2) * (3 + 400 * (m + n + 1) ^ 2 + 1) := by
          exact hw.trans (by gcongr)
       _ ≤ _ := by nlinarith [sq_nonneg ((m + n + 1) ^ 2)]

end WolfeSimplex.Execution

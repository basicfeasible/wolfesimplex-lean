import WolfeSimplex.Proofs.NetworkEncoding
import WolfeSimplex.Execution.Budget

/-! First-order preprocessing of native rational network data. Inputs are
arrays of endpoints, rational numerators/denominators and retained row indices.
The output contains exactly the six dense rational-LP arrays read by the
denominator-clearing program. All input-dependent selection is executed. -/
namespace WolfeSimplex.Execution.Network
open Code Finset Matrix
variable {v n m c : ℕ}

/-- Integer equality implemented using existing arithmetic instructions. -/
def equal (a b : Code) : Code := sub (literal 1) (abs (sign (sub a b)))

theorem equal_eval {a b : Code} {env : Env} {x y : ℤ}
    (ha : a.eval env = [x]) (hb : b.eval env = [y]) :
    (equal a b).eval env = [if x = y then 1 else 0] := by
  have hs := eval_unary Unary.sign (sub_eval ha hb)
  have he := sub_eval (eval_literal 1 env) (abs_eval hs)
  change (equal a b).eval env = [1 - |(x - y).sign|] at he
  rw [he]
  congr 1
  rcases lt_trichotomy x y with h | rfl | h
  · simp [Int.sign_eq_neg_one_of_neg (sub_neg.mpr h), ne_of_lt h]
  · simp
  · simp [Int.sign_eq_one_of_pos (sub_pos.mpr h), ne_of_gt h]

def input (Q : RationalNetwork v n) (D : Q.toNetwork.RowDeletion m c) : Env :=
  [List.ofFn fun e ↦ (Q.tail e).val,
   List.ofFn fun e ↦ (Q.head e).val,
   List.ofFn fun w ↦ (Q.supply w).num,
   List.ofFn fun w ↦ ((Q.supply w).den : ℤ),
   List.ofFn fun e ↦ (Q.cost e).num,
   List.ofFn fun e ↦ ((Q.cost e).den : ℤ),
   List.ofFn fun e ↦ (Q.capacity e).num,
   List.ofFn fun e ↦ ((Q.capacity e).den : ℤ),
   List.ofFn fun i ↦ (D.rows i).val.val]

def select (v block row : ℕ) : Code :=
  Code.sum (List.ofFn fun w : Fin v ↦
    mul (equal (slot 8 row) (literal w.val)) (slot block w.val))

def aNum (v m n : ℕ) (r : Fin (m + n)) (j : Fin (n + n)) : Code :=
  Fin.addCases
    (fun i ↦ Fin.addCases
      (fun e ↦ sub (equal (slot 1 e.val) (slot 8 i.val))
        (equal (slot 0 e.val) (slot 8 i.val))) (fun _ ↦ literal 0) j)
    (fun e ↦ Fin.addCases (fun k ↦ equal (literal e.val) (literal k.val))
      (fun k ↦ equal (literal e.val) (literal k.val)) j) r

def bNum (v m n : ℕ) (r : Fin (m + n)) : Code :=
  Fin.addCases (fun i ↦ select v 2 i.val) (fun e ↦ slot 6 e.val) r

def bDen (v m n : ℕ) (r : Fin (m + n)) : Code :=
  Fin.addCases (fun i ↦ select v 3 i.val) (fun e ↦ slot 7 e.val) r

def cNum (n : ℕ) (j : Fin (n + n)) : Code :=
  Fin.addCases (fun e ↦ slot 4 e.val) (fun _ ↦ literal 0) j

def cDen (n : ℕ) (j : Fin (n + n)) : Code :=
  Fin.addCases (fun e ↦ slot 5 e.val) (fun _ ↦ literal 1) j

def code (v m n : ℕ) : Code :=
  par (table (List.ofFn fun ij : Fin ((m + n) * (n + n)) ↦ aNum v m n ij.divNat ij.modNat))
    (par (table (List.ofFn fun _ : Fin ((m + n) * (n + n)) ↦ literal 1))
      (par (table (List.ofFn (bNum v m n)))
        (par (table (List.ofFn (bDen v m n)))
          (par (table (List.ofFn (cNum n))) (table (List.ofFn (cDen n)))))))

def raw {r s : ℕ} (R : RatLP r s) : List ℤ :=
  pack (fun i j ↦ (R.A i j).num) ++
    (pack (fun i j ↦ ((R.A i j).den : ℤ)) ++
      (List.ofFn (fun i ↦ (R.b i).num) ++
        (List.ofFn (fun i ↦ ((R.b i).den : ℤ)) ++
          (List.ofFn (fun j ↦ (R.c j).num) ++ List.ofFn (fun j ↦ ((R.c j).den : ℤ))))))

variable (Q : RationalNetwork v n) (D : Q.toNetwork.RowDeletion m c)

private theorem tail_slot (e : Fin n) :
    (slot 0 e.val).eval (input Q D) = [((Q.tail e).val : ℤ)] := by
  simp [input]
private theorem head_slot (e : Fin n) :
    (slot 1 e.val).eval (input Q D) = [((Q.head e).val : ℤ)] := by
  simp [input]
private theorem row_slot (i : Fin m) :
    (slot 8 i.val).eval (input Q D) = [((D.rows i).val.val : ℤ)] := by
  simp [input]

theorem select_eval (i : Fin m) (block : ℕ) (f : Fin v → ℤ)
    (hf : ∀ w, (slot block w.val).eval (input Q D) = [f w]) :
    (select v block i.val).eval (input Q D) = [f (D.rows i).val] := by
  have he (w : Fin v) :
      (equal (slot 8 i.val) (literal w.val)).eval (input Q D) =
        [if (D.rows i).val = w then 1 else 0] := by
    simpa only [Int.natCast_inj, Fin.val_inj] using
      equal_eval (row_slot Q D i) (eval_literal (w.val : ℤ) (input Q D))
  have h := sum_eval (List.finRange v)
    (fun w ↦ mul (equal (slot 8 i.val) (literal w.val)) (slot block w.val))
    (fun w ↦ (if (D.rows i).val = w then 1 else 0) * f w) (input Q D)
    (fun w _ ↦ mul_eval (he w) (hf w))
  simpa [select, List.finRange, List.map_ofFn, Function.comp_def, List.sum_ofFn,
    ite_mul] using h

theorem aNum_eval (r : Fin (m + n)) (j : Fin (n + n)) :
    (aNum v m n r j).eval (input Q D) = [((Q.standard D).A r j).num] := by
  refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r
  · refine Fin.addCases (fun e ↦ ?_) (fun e ↦ ?_) j
    · have hh := equal_eval (head_slot Q D e) (row_slot Q D i)
      have ht := equal_eval (tail_slot Q D e) (row_slot Q D i)
      have he := sub_eval hh ht
      simp only [aNum, Fin.addCases_left]
      simp only [Int.natCast_inj, Fin.val_inj] at he
      rw [he]
      simp only [RationalNetwork.standard, Fin.addCases_left]
      split_ifs <;> norm_num
    · simp [aNum, RationalNetwork.standard, -Fin.natAdd_eq_addNat]
  · refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp only [aNum, Fin.addCases_left, Fin.addCases_right] <;>
      rw [equal_eval (eval_literal _ _) (eval_literal _ _)] <;>
      simp only [RationalNetwork.standard, Fin.addCases_left, Fin.addCases_right,
        Int.natCast_inj, Fin.val_inj] <;> split_ifs <;> norm_num

theorem aDen_eq_one (r : Fin (m + n)) (j : Fin (n + n)) :
    ((Q.standard D).A r j).den = 1 := by
  refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r <;>
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
    simp only [RationalNetwork.standard, Fin.addCases_left, Fin.addCases_right] <;>
    (try split_ifs) <;> norm_num

theorem bNum_eval (r : Fin (m + n)) :
    (bNum v m n r).eval (input Q D) = [((Q.standard D).b r).num] := by
  refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r
  · simp only [bNum, Fin.addCases_left, RationalNetwork.standard, Fin.append_left]
    exact select_eval Q D i 2 (fun w ↦ (Q.supply w).num) (by intro w; simp [input])
  · simp [bNum, RationalNetwork.standard, input, -Fin.natAdd_eq_addNat]

theorem bDen_eval (r : Fin (m + n)) :
    (bDen v m n r).eval (input Q D) = [(((Q.standard D).b r).den : ℤ)] := by
  refine Fin.addCases (fun i ↦ ?_) (fun e ↦ ?_) r
  · simp only [bDen, Fin.addCases_left, RationalNetwork.standard, Fin.append_left]
    exact select_eval Q D i 3 (fun w ↦ ((Q.supply w).den : ℤ)) (by intro w; simp [input])
  · simp [bDen, RationalNetwork.standard, input, -Fin.natAdd_eq_addNat]

theorem cNum_eval (j : Fin (n + n)) :
    (cNum n j).eval (input Q D) = [((Q.standard D).c j).num] := by
  refine Fin.addCases (fun e ↦ ?_) (fun e ↦ ?_) j <;>
    simp [cNum, RationalNetwork.standard, input, -Fin.natAdd_eq_addNat]

theorem cDen_eval (j : Fin (n + n)) :
    (cDen n j).eval (input Q D) = [(((Q.standard D).c j).den : ℤ)] := by
  refine Fin.addCases (fun e ↦ ?_) (fun e ↦ ?_) j <;>
    simp [cDen, RationalNetwork.standard, input, -Fin.natAdd_eq_addNat]

theorem correct : (code v m n).eval (input Q D) = raw (Q.standard D) := by
  unfold code raw
  simp only [eval_par]
  rw [table_matrix _ _ _ (aNum_eval Q D)]
  rw [table_matrix (fun _ _ ↦ literal 1) (fun i j ↦ (((Q.standard D).A i j).den : ℤ))
    _ (by intro i j; rw [aDen_eq_one Q D i j]; rfl)]
  rw [table_ofFn_eval _ _ _ (bNum_eval Q D), table_ofFn_eval _ _ _ (bDen_eval Q D),
    table_ofFn_eval _ _ _ (cNum_eval Q D), table_ofFn_eval _ _ _ (cDen_eval Q D)]

end WolfeSimplex.Execution.Network

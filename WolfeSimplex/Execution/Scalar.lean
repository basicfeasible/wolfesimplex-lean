import WolfeSimplex.Execution.Code

namespace WolfeSimplex.Execution.Code

@[simp] theorem eval_copy (i : ℕ) (xs : Env) : (copy i).eval xs = [(current xs)[i]?.getD 0] := rfl
@[simp] theorem eval_literal (z : ℤ) (xs : Env) : (literal z).eval xs = [z] := rfl
@[simp] theorem eval_seq (a b : Code) (xs : Env) :
    (seq a b).eval xs = b.eval (a.eval xs :: xs) := rfl
@[simp] theorem eval_par (a b : Code) (xs : Env) :
    (par a b).eval xs = a.eval xs ++ b.eval xs := rfl
@[simp] theorem eval_extend (a b : Code) (xs : Env) :
    (extend a b).eval xs = b.eval (a.eval xs :: xs) := rfl

theorem eval_binary {a b : Code} {xs : Env} {x y : ℤ}
    (op : Binary) (ha : a.eval xs = [x]) (hb : b.eval xs = [y]) :
    (seq (par a b) (binary op 0 1)).eval xs = [binaryValue op x y] := by
  unfold eval at ha hb ⊢
  simp [run, current, ha, hb]

theorem eval_unary {a : Code} {xs : Env} {x : ℤ}
    (op : Unary) (ha : a.eval xs = [x]) :
    (seq a (unary op 0)).eval xs = [unaryValue op x] := by
  unfold eval at ha ⊢
  simp [run, current, ha]

theorem add_eval {a b : Code} {env : Env} {x y : ℤ}
    (ha : a.eval env = [x]) (hb : b.eval env = [y]) : (add a b).eval env = [x + y] :=
  eval_binary Binary.add ha hb

theorem sub_eval {a b : Code} {env : Env} {x y : ℤ}
    (ha : a.eval env = [x]) (hb : b.eval env = [y]) : (sub a b).eval env = [x - y] :=
  eval_binary Binary.sub ha hb

theorem mul_eval {a b : Code} {env : Env} {x y : ℤ}
    (ha : a.eval env = [x]) (hb : b.eval env = [y]) : (mul a b).eval env = [x * y] :=
  eval_binary Binary.mul ha hb

theorem max_eval {a b : Code} {env : Env} {x y : ℤ}
    (ha : a.eval env = [x]) (hb : b.eval env = [y]) :
    (max a b).eval env = [Max.max x y] := eval_binary Binary.max ha hb

theorem neg_eval {a : Code} {env : Env} {x : ℤ}
    (ha : a.eval env = [x]) : (neg a).eval env = [-x] := eval_unary Unary.neg ha

theorem abs_eval {a : Code} {env : Env} {x : ℤ}
    (ha : a.eval env = [x]) : (abs a).eval env = [|x|] := eval_unary Unary.abs ha

@[simp] theorem size_copy (i : ℕ) : (copy i).size = 2 := rfl
@[simp] theorem size_add (a b : Code) : (add a b).size = a.size + b.size + 3 := rfl
@[simp] theorem size_sub (a b : Code) : (sub a b).size = a.size + b.size + 3 := rfl
@[simp] theorem size_mul (a b : Code) : (mul a b).size = a.size + b.size + 3 := rfl
@[simp] theorem size_max (a b : Code) : (max a b).size = a.size + b.size + 3 := rfl
@[simp] theorem size_neg (a : Code) : (neg a).size = a.size + 2 := rfl
@[simp] theorem size_abs (a : Code) : (abs a).size = a.size + 2 := rfl
@[simp] theorem size_sign (a : Code) : (sign a).size = a.size + 2 := rfl

def sum : List Code → Code
  | [] => literal 0
  | c :: cs => add c (sum cs)

def maxList : List Code → Code
  | [] => literal 0
  | c :: cs => max c (maxList cs)

theorem sum_eval {α : Type} (as : List α) (f : α → Code) (v : α → ℤ) (xs : Env)
    (h : ∀ a ∈ as, (f a).eval xs = [v a]) :
    (sum (as.map f)).eval xs = [(as.map v).sum] := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb ↦ h b (by simp [hb]))
    simpa only [List.map_cons, sum, add, binaryValue, List.sum_cons] using
      eval_binary Binary.add ha ht

theorem maxList_eval {α : Type} (as : List α) (f : α → Code) (v : α → ℤ) (xs : Env)
    (h : ∀ a ∈ as, (f a).eval xs = [v a]) :
    (maxList (as.map f)).eval xs = [(as.map v).foldr Max.max 0] := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb ↦ h b (by simp [hb]))
    simpa only [List.map_cons, maxList, max, binaryValue, List.foldr_cons] using
      eval_binary Binary.max ha ht

theorem sum_size (cs : List Code) :
    (sum cs).size = (cs.map fun c ↦ c.size + 3).sum + 1 := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [sum, size_add, ih, List.map_cons, List.sum_cons]; omega

theorem maxList_size (cs : List Code) :
    (maxList cs).size = (cs.map fun c ↦ c.size + 3).sum + 1 := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [maxList, size_max, ih, List.map_cons, List.sum_cons]; omega

theorem table_eval_values {α : Type} (as : List α) (f : α → Code)
    (v : α → List ℤ) (xs : Env) (h : ∀ a ∈ as, (f a).eval xs = v a) :
    (table (as.map f)).eval xs = as.flatMap v := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb ↦ h b (by simp [hb]))
    simp only [List.map_cons, table, List.foldr_cons, eval_par, List.flatMap_cons]
    rw [ha]
    exact congrArg (fun tail ↦ v a ++ tail) ht

@[simp] theorem read_range (xs : List ℤ) (env : Env) :
    (read (List.range xs.length)).eval (xs :: env) = xs := by
  apply List.ext_getElem
  · simp [eval, run]
  · intro i hi hi'
    simp only [eval, run, current, List.getElem?_cons_zero, Option.getD_some,
      List.getElem_map, List.getElem_range]
    simp [List.getElem?_eq_getElem hi']

@[simp] theorem eval_slot (block i : ℕ) (env : Env) :
    (slot block i).eval env = [(env[block]?.getD [])[i]?.getD 0] := rfl

/-- Repeated execution with state arrays cached between iterations. -/
def iterateCode (c : Code) : ℕ → Code
  | 0 => read (List.range c.outputs)
  | n + 1 => seq c (iterateCode c n)

/-- Cached exponentiation. Only the base and accumulator are passed around. -/
def power (_arity : ℕ) (base : Code) (n : ℕ) : Code :=
  let step := par (copy 0) (mul (copy 0) (copy 1))
  extend base (seq (par (copy 0) (literal 1))
    (seq (iterateCode step n) (copy 1)))

theorem repeat_power (b a : ℤ) (n : ℕ) (env : Env) :
    (iterateCode (par (copy 0) (mul (copy 0) (copy 1))) n).eval ([b, a] :: env) =
      [b, b ^ n * a] := by
  induction n generalizing a env with
  | zero => simp [iterateCode, eval, run, outputs, copy, mul, current, List.range_succ]
  | succ n ih =>
    simp only [iterateCode, eval_seq, eval_par, eval_copy]
    have hm : (mul (copy 0) (copy 1)).eval ([b, a] :: env) = [b * a] := by
      exact eval_binary Binary.mul (by rfl) (by rfl)
    simp only [current, List.getElem?_cons_zero, Option.getD_some, hm, List.singleton_append]
    rw [ih]
    congr 2
    rw [pow_succ]
    ring

theorem power_eval (arity n : ℕ) (base : Code) (xs : Env) (b : ℤ)
    (hb : base.eval xs = [b]) :
    (power arity base n).eval xs = [b ^ n] := by
  simp only [power, eval_extend, hb, eval_seq, eval_par, eval_copy, eval_literal]
  simp only [current, List.getElem?_cons_zero, Option.getD_some, List.singleton_append,
    repeat_power, mul_one]
  rfl

theorem sum_map_le {α : Type} (as : List α) (f : α → ℕ) (b : ℕ)
    (h : ∀ a ∈ as, f a ≤ b) : (as.map f).sum ≤ as.length * b := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have ht := ih (fun a ha ↦ h a (by simp [ha]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem table_size_le {α : Type} (as : List α) (f : α → Code) (b : ℕ)
    (h : ∀ a ∈ as, (f a).size ≤ b) :
    (table (as.map f)).size ≤ as.length * (b + 1) + 1 := by
  rw [table_size, List.map_map]
  exact Nat.add_le_add_right (sum_map_le _ _ _ (fun a ha ↦ by
    have := h a ha; dsimp; omega)) 1

theorem maxList_size_le {α : Type} (as : List α) (f : α → Code) (b : ℕ)
    (h : ∀ a ∈ as, (f a).size ≤ b) :
    (maxList (as.map f)).size ≤ as.length * (b + 3) + 1 := by
  rw [maxList_size, List.map_map]
  exact Nat.add_le_add_right (sum_map_le _ _ _ (fun a ha ↦ by
    have := h a ha; dsimp; omega)) 1

theorem sum_size_le {α : Type} (as : List α) (f : α → Code) (b : ℕ)
    (h : ∀ a ∈ as, (f a).size ≤ b) :
    (sum (as.map f)).size ≤ as.length * (b + 3) + 1 := by
  rw [sum_size, List.map_map]
  exact Nat.add_le_add_right (sum_map_le _ _ _ (fun a ha ↦ by
    have := h a ha; dsimp; omega)) 1

@[simp] theorem size_slot (block i : ℕ) : (slot block i).size = 2 := rfl

@[simp] theorem iterateCode_size (c : Code) (n : ℕ) :
    (iterateCode c n).size = n * (c.size + 1) + c.outputs + 1 := by
  induction n with
  | zero => simp [iterateCode, size]
  | succ n ih => simp only [iterateCode, size, ih]; ring

@[simp] theorem power_size (arity : ℕ) (base : Code) (n : ℕ) :
    (power arity base n).size = base.size + 11 * n + 12 := by
  simp [power, size, outputs, copy, mul]
  ring

theorem readAt_range (block count : ℕ) (xs : List ℤ) (env : Env)
    (hf : env[block]?.getD [] = xs) (hl : xs.length = count) :
    (readAt block (List.range count)).eval env = xs := by
  have h := read_range xs ([] : Env)
  simpa only [eval, run, current, List.getElem?_cons_zero, Option.getD_some, hf, hl] using h

end WolfeSimplex.Execution.Code

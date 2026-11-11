import WolfeSimplex.Proofs.PaperPath
import WolfeSimplex.Construction.Cost

/-!
# Executable trace projection

A support is stored as a Boolean vector. The source procedure shadows a complete
Wolfe execution, retaining its choices and history, and removes the added label.
Only Boolean copies are needed; it does not solve a second linear system.
-/

namespace WolfeSimplex.Efficiency

abbrev Mask (n : ℕ) := Vector Bool n
abbrev Points (N D : ℕ) := Vector (Vector ℤ D) N

/-- Mathematical interpretation; not used to compute the projected trace. -/
def support {n : ℕ} (b : Mask n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ b[j] = true

def mask {n : ℕ} (B : Finset (Fin n)) : Mask n :=
  Vector.ofFn fun j ↦ decide (j ∈ B)

@[simp] theorem support_mask {n : ℕ} (B : Finset (Fin n)) : support (mask B) = B := by
  ext j
  simp [support, mask]

/-- Append the added label. Three cell/control charges per stored bit suffice
for copying and initialization in the array model. -/
def start {n : ℕ} (b : Mask n) : Mask (n + 1) :=
  b.push true

@[simp] theorem start_get {n : ℕ} (b : Mask n) (j : Fin n) :
    (start b)[j.castSucc] = b[j] := by simp [start, Fin.getElem_fin]

@[simp] theorem start_last {n : ℕ} (b : Mask n) :
    (start b)[Fin.last n] = true := by simp [start, Fin.getElem_fin]

@[simp] theorem mask_get {n : ℕ} (B : Finset (Fin n)) (j : Fin n) :
    (mask B)[j] = decide (j ∈ B) := by simp [mask, Fin.getElem_fin]

@[simp] theorem start_mask {n : ℕ} (B : Finset (Fin n)) :
    start (mask B) = mask (hat B) := by
  apply Vector.ext
  intro j hj
  by_cases h : j < n
  · let k : Fin n := ⟨j, h⟩
    change (start (mask B))[k.castSucc] = (mask (hat B))[k.castSucc]
    rw [start_get, mask_get, mask_get]
    simp
  · have heq : j = n := by omega
    subst j
    change (start (mask B))[Fin.last n] = (mask (hat B))[Fin.last n]
    rw [start_last, mask_get]
    simp

@[simp] theorem mask_support {n : ℕ} (b : Mask n) : mask (support b) = b := by
  apply Vector.ext
  intro j hj
  simp [mask, support]

@[simp] theorem support_start {n : ℕ} (b : Mask n) :
    support (start b) = hat (support b) := by
  calc support (start b) = support (start (mask (support b))) := by rw [mask_support]
       _ = hat (support b) := by rw [start_mask, support_mask]

/-- Drop the added label by reading the first `n` stored bits. -/
def project {n : ℕ} (b : Mask (n + 1)) : Mask n := Vector.ofFn fun j ↦ b[j.castSucc]

@[simp] theorem project_get {n : ℕ} (b : Mask (n + 1)) (j : Fin n) :
    (project b)[j] = b[j.castSucc] := by simp [project, Fin.getElem_fin]

@[simp] theorem project_mask_hat {n : ℕ} (B : Finset (Fin n)) :
    project (mask (hat B)) = mask B := by
  have h (j : Fin n) : (project (mask (hat B)))[j] = (mask B)[j] := by
    simp only [project_get, mask_get]
    simp
  apply Vector.ext
  intro j hj
  exact h ⟨j, hj⟩

/-- Measured cell reads/writes and list traversal. Resource-monitor evaluation
is outside the cost model, as in `Construction.Computation`. -/
def projectTrace {n : ℕ} : List (Mask (n + 1)) →
    Construction.Computation (List (Mask n))
  | [] => ⟨[], 0, 0, 1⟩
  | b :: bs =>
    let rest := projectTrace bs
    ⟨project b :: rest.value, 0, 0, rest.bookkeeping + 2 * n + 2⟩

@[simp] theorem projectTrace_value {n : ℕ} (xs : List (Mask (n + 1))) :
    (projectTrace xs).value = xs.map project := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [projectTrace, ih]

@[simp] theorem projectTrace_operations {n : ℕ} (xs : List (Mask (n + 1))) :
    (projectTrace xs).operations = 0 := by cases xs <;> rfl

@[simp] theorem projectTrace_work {n : ℕ} (xs : List (Mask (n + 1))) :
    (projectTrace xs).work = (2 * n + 2) * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    have hi : (projectTrace bs).bookkeeping = (2 * n + 2) * bs.length + 1 := by
      simpa [Construction.Computation.work] using ih
    simp only [Construction.Computation.work, projectTrace, Nat.zero_add, List.length_cons]
    rw [hi]
    ring

def realPoints {N D : ℕ} (v : Points N D) : Fin N → Fin D → ℝ :=
  fun j i ↦ (v[j][i] : ℝ)

/-- A complete mathematical Wolfe run, encoded as its list of support masks. -/
def WolfeTrace {N D : ℕ} (p : Fin N → Fin D → ℝ) (b : Mask N)
    (xs : List (Mask N)) : Prop :=
  ∃ f S, Wolfe.IsWolfeRun p f S ∧ S 0 = support b ∧
    xs = List.ofFn (fun k : Fin (f + 1) ↦ mask (S k))

/-- A complete mathematical simplex run, in the same concrete trace format. -/
def SimplexTrace {m n : ℕ} (P : IntLP m n) (b : Mask n)
    (xs : List (Mask n)) : Prop :=
  ∃ f B, P.toLP.IsSimplexRun f B ∧ B 0 = support b ∧
    xs = List.ofFn (fun k : Fin (f + 1) ↦ mask (B k))

/-- The trace projection implements every pivot of the induced simplex run. -/
theorem project_correct {m n : ℕ} (P : IntLP m n) (hP : P.IsAdmissible)
    (b : Mask n) (hb : P.toLP.IsFeasibleBasis (support b))
    (xs : List (Mask (n + 1))) (hx : WolfeTrace P.atom (start b) xs) :
    SimplexTrace P b (projectTrace xs).value := by
  obtain ⟨f, S, hS, h0, rfl⟩ := hx
  rw [support_start] at h0
  obtain ⟨B, hB, hB0, hSB⟩ := (PaperPath.part_c P hP (support b) hb f S).mp ⟨hS, h0⟩
  refine ⟨f, B, hB, hB0, ?_⟩
  rw [projectTrace_value, List.map_ofFn]
  congr 1
  funext k
  change project (mask (S k)) = mask (B k)
  rw [hSB k (by omega), project_mask_hat]

end WolfeSimplex.Efficiency

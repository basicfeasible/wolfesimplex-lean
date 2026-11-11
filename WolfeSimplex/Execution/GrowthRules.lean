import WolfeSimplex.Execution.Frames

namespace WolfeSimplex.Execution.Code

/-- A small static certificate for a straight-line fragment. -/
structure GrowthCert (B f o : ℕ) (c : Code) : Prop where
  factor : c.factor ≤ f
  offset : c.offset ≤ o
  literals : c.literalsBounded B

namespace GrowthCert
variable {B f g o p : ℕ} {a b : Code}

theorem mono (h : GrowthCert B f o a) (hf : f ≤ g) (ho : o ≤ p) :
    GrowthCert B g p a := ⟨h.factor.trans hf, h.offset.trans ho, h.literals⟩

theorem slot (block i B : ℕ) : GrowthCert B 1 0 (Code.slot block i) := ⟨le_rfl, le_rfl, trivial⟩
theorem readAt (block : ℕ) (is : List ℕ) (B : ℕ) :
    GrowthCert B 1 0 (Code.readAt block is) := ⟨le_rfl, le_rfl, trivial⟩
theorem literal (z : ℤ) (h : z.natAbs ≤ B) : GrowthCert B 1 1 (.literal z) := ⟨le_rfl, le_rfl, h⟩

theorem par (ha : GrowthCert B f o a) (hb : GrowthCert B g p b) :
    GrowthCert B (Max.max f g) (Max.max o p) (Code.par a b) :=
  ⟨max_le_max ha.factor hb.factor, max_le_max ha.offset hb.offset, ha.literals, hb.literals⟩

theorem add (ha : GrowthCert B f o a) (hb : GrowthCert B g p b) :
    GrowthCert B (Max.max f g) (Max.max o p + 1) (Code.add a b) := by
  exact ⟨by simpa [Code.add, Code.factor] using max_le_max ha.factor hb.factor,
    by simpa [Code.add, Code.offset, Code.factor] using
      Nat.add_le_add_right (max_le_max ha.offset hb.offset) 1,
    by simpa [Code.add, literalsBounded] using And.intro ha.literals hb.literals⟩

theorem sub (ha : GrowthCert B f o a) (hb : GrowthCert B g p b) :
    GrowthCert B (Max.max f g) (Max.max o p + 1) (Code.sub a b) := by
  exact ⟨by simpa [Code.sub, Code.factor] using max_le_max ha.factor hb.factor,
    by simpa [Code.sub, Code.offset, Code.factor] using
      Nat.add_le_add_right (max_le_max ha.offset hb.offset) 1,
    by simpa [Code.sub, literalsBounded] using And.intro ha.literals hb.literals⟩

theorem mul (ha : GrowthCert B f o a) (hb : GrowthCert B g p b) :
    GrowthCert B (2 * Max.max f g) (2 * Max.max o p) (Code.mul a b) := by
  exact ⟨by simpa [Code.mul, Code.factor, mul_comm] using
      Nat.mul_le_mul_left 2 (max_le_max ha.factor hb.factor),
    by simpa [Code.mul, Code.offset, Code.factor, mul_comm] using
      Nat.mul_le_mul_left 2 (max_le_max ha.offset hb.offset),
    by simpa [Code.mul, literalsBounded] using And.intro ha.literals hb.literals⟩

theorem max (ha : GrowthCert B f o a) (hb : GrowthCert B g p b) :
    GrowthCert B (Max.max f g) (Max.max o p) (Code.max a b) := by
  exact ⟨by simpa [Code.max, Code.factor] using max_le_max ha.factor hb.factor,
    by simpa [Code.max, Code.offset, Code.factor] using max_le_max ha.offset hb.offset,
    by simpa [Code.max, literalsBounded] using And.intro ha.literals hb.literals⟩

theorem neg (h : GrowthCert B f o a) : GrowthCert B f o (Code.neg a) := by
  exact ⟨by simpa [Code.neg, Code.factor] using h.factor,
    by simpa [Code.neg, Code.factor, Code.offset] using h.offset,
    by simpa [Code.neg, literalsBounded] using h.literals⟩

theorem abs (h : GrowthCert B f o a) : GrowthCert B f o (Code.abs a) := by
  exact ⟨by simpa [Code.abs, Code.factor] using h.factor,
    by simpa [Code.abs, Code.factor, Code.offset] using h.offset,
    by simpa [Code.abs, literalsBounded] using h.literals⟩

theorem table {α : Type} (as : List α) (f : α → Code) (q r : ℕ) (hq : 1 ≤ q)
    (h : ∀ a ∈ as, GrowthCert B q r (f a)) :
    GrowthCert B q r (Code.table (as.map f)) := by
  induction as with
  | nil => exact ⟨hq, Nat.zero_le _, trivial⟩
  | cons a as ih =>
    have ht := ih (fun a ha ↦ h a (by simp [ha]))
    have hp := (h a (by simp)).par ht
    simpa only [List.map_cons, Code.table, List.foldr_cons, max_self] using hp

theorem sum {α : Type} (as : List α) (f : α → Code) (q r : ℕ) (hq : 1 ≤ q)
    (h : ∀ a ∈ as, GrowthCert B q r (f a)) :
    GrowthCert B q ((r + 1) * as.length + 1) (Code.sum (as.map f)) := by
  induction as with
  | nil => simpa [Code.sum] using (GrowthCert.literal (B := B) 0 (by simp)).mono hq le_rfl
  | cons a as ih =>
    have ht := ih (fun a ha ↦ h a (by simp [ha]))
    have hp := (h a (by simp)).add ht
    simp only [max_self, List.length_cons] at hp ⊢
    apply hp.mono le_rfl
    simp only [Nat.mul_succ]
    omega

theorem maxList {α : Type} (as : List α) (f : α → Code) (q r : ℕ) (hq : 1 ≤ q)
    (h : ∀ a ∈ as, GrowthCert B q r (f a)) :
    GrowthCert B q (r + 1) (Code.maxList (as.map f)) := by
  induction as with
  | nil =>
    exact (GrowthCert.literal 0 (by simp)).mono hq (by omega)
  | cons a as ih =>
    have ht := ih (fun a ha ↦ h a (by simp [ha]))
    have hp := (h a (by simp)).max ht
    apply hp.mono (by simp)
    omega

end GrowthCert
end WolfeSimplex.Execution.Code

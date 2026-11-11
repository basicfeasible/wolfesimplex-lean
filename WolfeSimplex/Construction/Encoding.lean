import WolfeSimplex.Construction.Resources

/-!
# Dense binary input encoding

Dimensions and all entries are included. A natural is encoded by a unary prefix
for its binary digit count, a separator, and its binary digits; an integer adds
a sign bit. We use the length of this concrete bit list, not a unit-cost size
parameter that hides large input coefficients.
-/

namespace WolfeSimplex.Construction

variable {m n : ℕ}

def encodeNat (a : ℕ) : List Bool :=
  List.replicate (Nat.size a) true ++ false :: a.bits

def encodeInt (a : ℤ) : List Bool := decide (a < 0) :: encodeNat a.natAbs

def inputData (P : IntLP m n) : List ℤ := constraintData P ++ List.ofFn P.c

def payloadBits (P : IntLP m n) : ℕ :=
  ((inputData P).map fun a ↦ 1 + Nat.size a.natAbs).sum

def inputEncoding (P : IntLP m n) : List Bool :=
  encodeNat m ++ encodeNat n ++ (inputData P).flatMap encodeInt

def inputSize (P : IntLP m n) : ℕ := (inputEncoding P).length

@[simp] theorem encodeNat_length (a : ℕ) : (encodeNat a).length = 2 * Nat.size a + 1 := by
  simp [encodeNat, Nat.size_eq_bits_len]; omega

@[simp] theorem encodeInt_length (a : ℤ) :
    (encodeInt a).length = 2 * (1 + Nat.size a.natAbs) := by
  simp [encodeInt]; omega

private theorem encoded_list_length (xs : List ℤ) :
    (xs.flatMap encodeInt).length = 2 * (xs.map fun a ↦ 1 + Nat.size a.natAbs).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]; omega

theorem inputSize_eq (P : IntLP m n) :
    inputSize P = 2 * (Nat.size m + Nat.size n + payloadBits P + 1) := by
  simp only [inputSize, inputEncoding, List.length_append, encodeNat_length,
    encoded_list_length, payloadBits]
  omega

private theorem length_le_payload (xs : List ℤ) :
    xs.length ≤ (xs.map fun a ↦ 1 + Nat.size a.natAbs).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

private theorem member_size_le_payload {xs : List ℤ} {a : ℤ} (ha : a ∈ xs) :
    Nat.size a.natAbs ≤ (xs.map fun b ↦ 1 + Nat.size b.natAbs).sum := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    simp only [List.mem_cons] at ha
    simp only [List.map_cons, List.sum_cons]
    rcases ha with rfl | ha
    · omega
    · have := ih ha; omega

theorem dimensions_le_payload (P : IntLP m n) : m + n ≤ payloadBits P := by
  have h := length_le_payload (inputData P)
  have hl : (inputData P).length = m * n + m + n := by
    simp [inputData, constraintData, List.length_flatten, Function.comp_def]
    omega
  rw [hl] at h
  exact (by omega : m + n ≤ m * n + m + n).trans h

/-- The largest input magnitude has at most the payload length plus two bits. -/
theorem maxEntry_size_le (P : IntLP m n) : Nat.size P.maxEntry ≤ payloadBits P + 2 := by
  have hentry : ∀ a ∈ inputData P, a.natAbs ≤ 2 ^ (payloadBits P + 1) := by
    intro a ha
    have hs := member_size_le_payload ha
    have hlt := Nat.lt_size_self a.natAbs
    exact (Nat.le_of_lt hlt).trans
      (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by simpa [payloadBits] using Nat.le_succ_of_le hs))
  have hu : P.U ≤ 2 ^ (payloadBits P + 1) := by
    rw [← uScan_value P]
    apply (Computation.maxAbs_le_iff _ _).mpr
    refine ⟨Nat.one_le_pow _ _ (by omega), ?_⟩
    intro a ha
    exact hentry a (List.mem_append_left _ ha)
  have hc : (cScan P).value ≤ 2 ^ (payloadBits P + 1) := by
    apply (Computation.scanMax_le_iff _ _).mpr
    intro a ha
    exact hentry a (List.mem_append_right _ ha)
  have hw : P.maxEntry ≤ 2 ^ (payloadBits P + 1) := by
    have h2 : 2 ≤ 2 ^ (payloadBits P + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
           _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    have heq : P.maxEntry = max 2 (max P.U (cScan P).value) := by
      simp only [IntLP.maxEntry, IntLP.U, cScan_value]
      omega
    rw [heq]
    exact max_le h2 (max_le hu hc)
  apply Nat.size_le.mpr
  exact hw.trans_lt (by
    rw [show payloadBits P + 2 = payloadBits P + 1 + 1 by omega, pow_succ]
    have : 0 < 2 ^ (payloadBits P + 1) := by positivity
    omega)

/-- A convenient parameter controlling dimensions and coefficient widths. -/
def sizeParameter (P : IntLP m n) : ℕ := m + n + 1 + Nat.size P.maxEntry

theorem sizeParameter_le (P : IntLP m n) : sizeParameter P ≤ 3 * inputSize P := by
  have := dimensions_le_payload P
  have := maxEntry_size_le P
  rw [inputSize_eq]
  dsimp [sizeParameter]
  omega

private theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  calc a * b ≤ a * 2 ^ Nat.size b := Nat.mul_le_mul_left _ (Nat.lt_size_self b).le
       _ < 2 ^ Nat.size a * 2 ^ Nat.size b :=
         Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity)
       _ = _ := by rw [pow_add]

theorem base_size_le (P : IntLP m n) :
    Nat.size ((m + 1) * P.maxEntry) ≤ sizeParameter P := by
  have hm : Nat.size (m + 1) ≤ m + 1 := Nat.size_le.mpr (Nat.lt_two_pow_self)
  exact (size_mul_le _ _).trans (by dsimp [sizeParameter]; omega)

end WolfeSimplex.Construction

import SMSFormula.Applications.Unimodular.DyadicE8

/-!
# E8 correction-fiber count

This file proves the uniform
`2^28` cardinality of the explicit `0/1 + 2A` correction fibers and then
uses the existing E8 dyadic bridge to evaluate the native Schulze--Pillot
local factor at `2` for the E8 seed.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice
open scoped BigOperators

namespace E8CorrectionFiber

abbrev Upper (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Mat (n : ℕ) (K : Type*) := Matrix (Fin n) (Fin n) K
abbrev std (n : ℕ) {R : Type*} [CommRing R] (i : Fin n) : Fin n → R := Pi.single i 1

section Coefficients
variable {n : ℕ} {K : Type*} [AddCommGroup K]

/-- Prescribed diagonal and off-diagonal quadratic coefficients. -/
def HasCoefficients (r : Fin n → K) (s : Upper n → K) (M : Mat n K) : Prop :=
  (∀ i, M i i = r i) ∧
  (∀ p : Upper n, M p.1.1 p.1.2 + M p.1.2 p.1.1 = s p)

abbrev CoefficientFiber (r : Fin n → K) (s : Upper n → K) :=
  {M : Mat n K // HasCoefficients r s M}

/-- Lower-triangular entries are free; upper-triangular entries are solved. -/
def fill (r : Fin n → K) (s t : Upper n → K) : Mat n K := fun i j =>
  if h : i < j then s ⟨(i, j), h⟩ - t ⟨(i, j), h⟩
  else if h' : j < i then t ⟨(j, i), h'⟩
  else r i

@[simp] theorem fill_diag (r : Fin n → K) (s t : Upper n → K) (i : Fin n) :
    fill r s t i i = r i := by
  simp [fill]

@[simp] theorem fill_upper (r : Fin n → K) (s t : Upper n → K) (p : Upper n) :
    fill r s t p.1.1 p.1.2 = s p - t p := by
  simp [fill, p.2]

@[simp] theorem fill_lower (r : Fin n → K) (s t : Upper n → K) (p : Upper n) :
    fill r s t p.1.2 p.1.1 = t p := by
  simp [fill, p.2, not_lt_of_gt p.2]

theorem fill_hasCoefficients (r : Fin n → K) (s t : Upper n → K) :
    HasCoefficients r s (fill r s t) := by
  constructor
  · intro i; exact fill_diag r s t i
  · intro p; simp

def readLower {r : Fin n → K} {s : Upper n → K}
    (M : CoefficientFiber r s) : Upper n → K := fun p => M.1 p.1.2 p.1.1

theorem fill_readLower {r : Fin n → K} {s : Upper n → K}
    (M : CoefficientFiber r s) : fill r s (readLower M) = M.1 := by
  funext i j
  by_cases hij : i < j
  · have h := M.2.2 (⟨(i, j), hij⟩ : Upper n)
    change M.1 i j + M.1 j i = s ⟨(i, j), hij⟩ at h
    simp only [fill, dif_pos hij, readLower]
    exact (eq_sub_iff_add_eq.mpr h).symm
  · by_cases hji : j < i
    · simp [fill, hij, hji, readLower]
    · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      exact (fill_diag r s (readLower M) i).trans (M.2.1 i).symm

/-- An explicit equivalence, not just a cardinality assertion. -/
def coefficientFiberEquiv (r : Fin n → K) (s : Upper n → K) :
    CoefficientFiber r s ≃ (Upper n → K) where
  toFun := readLower
  invFun t := ⟨fill r s t, fill_hasCoefficients r s t⟩
  left_inv M := by
    apply Subtype.ext
    exact fill_readLower M
  right_inv t := by
    funext p
    exact fill_lower r s t p

/-- The proof is uniform over all right-hand sides, including nonzero defects. -/
theorem coefficientFiber_card [Fintype K] (r : Fin n → K) (s : Upper n → K) :
    Nat.card (CoefficientFiber r s) =
      (Fintype.card K) ^ Fintype.card (Upper n) := by
  classical
  calc
    Nat.card (CoefficientFiber r s) = Nat.card (Upper n → K) :=
      Nat.card_congr (coefficientFiberEquiv r s)
    _ = (Fintype.card K) ^ Fintype.card (Upper n) := by
      simp [Nat.card_eq_fintype_card]

/-- Only 64 ordered index pairs are inspected in this computation. -/
theorem upper_eight_card : Fintype.card (Upper 8) = 28 := by decide

theorem coefficientFiber_eight_card
    (r : Fin 8 → ZMod 2) (s : Upper 8 → ZMod 2) :
    Nat.card (CoefficientFiber r s) = 2 ^ 28 := by
  rw [coefficientFiber_card, upper_eight_card]
  norm_num

end Coefficients

section Pullback
variable {n : ℕ} {K : Type*} [AddCommGroup K]

/-- Transport the coefficient problem along any invertible change of variables. -/
def pullbackCoefficientEquiv
    (e : Mat n K ≃ Mat n K) (r : Fin n → K) (s : Upper n → K) :
    {A : Mat n K // HasCoefficients r s (e A)} ≃ CoefficientFiber r s where
  toFun A := ⟨e A.1, A.2⟩
  invFun M := ⟨e.symm M.1, by simpa using M.2⟩
  left_inv A := by apply Subtype.ext; exact e.symm_apply_apply A.1
  right_inv M := by apply Subtype.ext; exact e.apply_symm_apply M.1

/-- The native predicate is related to scalar coefficients, not assumed counted. -/
def predicateFiberEquiv
    (P : Mat n K → Prop) (e : Mat n K ≃ Mat n K)
    (r : Fin n → K) (s : Upper n → K)
    (h : ∀ A, P A ↔ HasCoefficients r s (e A)) :
    {A : Mat n K // P A} ≃ (Upper n → K) :=
  (show {A : Mat n K // P A} ≃ {A : Mat n K // HasCoefficients r s (e A)} from
    { toFun := fun A => ⟨A.1, (h A.1).mp A.2⟩
      invFun := fun A => ⟨A.1, (h A.1).mpr A.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
      ((pullbackCoefficientEquiv e r s).trans (coefficientFiberEquiv r s))

/-- Rank-uniform affine predicate-fiber count after reducing the native predicate
by an invertible matrix change to fixed diagonal and upper-triangular scalar
coefficient equations. -/
theorem predicateFiber_card [Fintype K]
    (P : Mat n K → Prop) (e : Mat n K ≃ Mat n K)
    (r : Fin n → K) (s : Upper n → K)
    (h : ∀ A, P A ↔ HasCoefficients r s (e A)) :
    Nat.card {A : Mat n K // P A} =
      (Fintype.card K) ^ Fintype.card (Upper n) := by
  classical
  calc
    Nat.card {A : Mat n K // P A} = Nat.card (Upper n → K) :=
      Nat.card_congr (predicateFiberEquiv P e r s h)
    _ = (Fintype.card K) ^ Fintype.card (Upper n) := by
      simp [Nat.card_eq_fintype_card]

theorem predicateFiber_eight_card
    (P : Mat 8 (ZMod 2) → Prop) (e : Mat 8 (ZMod 2) ≃ Mat 8 (ZMod 2))
    (r : Fin 8 → ZMod 2) (s : Upper 8 → ZMod 2)
    (h : ∀ A, P A ↔ HasCoefficients r s (e A)) :
    Nat.card {A : Mat 8 (ZMod 2) // P A} = 2 ^ 28 := by
  rw [predicateFiber_card P e r s h, upper_eight_card]
  norm_num

end Pullback

section Decomposition
variable {n : ℕ} {K : Type*}

/-- A finite target decomposed into a base finite type and free upper-pair
parameters has the expected product cardinality. -/
theorem cardinality_of_decomposition [Fintype K] {S B : Type*} [Fintype B]
    (e : S ≃ B × (Upper n → K)) :
    Nat.card S = Fintype.card B * (Fintype.card K) ^ Fintype.card (Upper n) := by
  classical
  calc
    Nat.card S = Nat.card (B × (Upper n → K)) := Nat.card_congr e
    _ = Fintype.card B * (Fintype.card K) ^ Fintype.card (Upper n) := by
      simp [Nat.card_eq_fintype_card]

end Decomposition

section MatrixChange
variable {n : ℕ} {R : Type*} [CommRing R]

/-- Supply a right inverse only; square matrices over a commutative ring are
Dedekind finite. No inversion of a potentially singular matrix is used. -/
def leftMatrixEquiv (U V : Mat n R) (hUV : U * V = 1) : Mat n R ≃ Mat n R where
  toFun A := U * A
  invFun M := V * M
  left_inv A := by
    change V * (U * A) = A
    have hVU : V * U = 1 := mul_eq_one_comm.mp hUV
    rw [← Matrix.mul_assoc, hVU, Matrix.one_mul]
  right_inv M := by
    change U * (V * M) = M
    rw [← Matrix.mul_assoc, hUV, Matrix.one_mul]

end MatrixChange

section QuadraticBasis
variable {n : ℕ} {R : Type*} [CommRing R]

theorem std_decomposition (v : Fin n → R) :
    (∑ i : Fin n, v i • std n i) = v := by
  classical
  funext j
  simp [std, Pi.smul_apply, Finset.sum_apply, Pi.single_apply]

theorem polar_finset_sum_left (Q : QuadraticForm R (Fin n → R))
    {ι : Type*} (s : Finset ι) (f : ι → (Fin n → R)) (y : Fin n → R) :
    QuadraticMap.polar Q (∑ i ∈ s, f i) y =
      ∑ i ∈ s, QuadraticMap.polar Q (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, QuadraticMap.polar_add_left, ih]

theorem polar_finset_sum_right (Q : QuadraticForm R (Fin n → R))
    {ι : Type*} (s : Finset ι) (f : ι → (Fin n → R)) (x : Fin n → R) :
    QuadraticMap.polar Q x (∑ i ∈ s, f i) =
      ∑ i ∈ s, QuadraticMap.polar Q x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, QuadraticMap.polar_add_right, ih]

/-- All pairs follow from upper-triangular pairs and the diagonal values. -/
theorem polar_std_eq_of_upper
    (Q T : QuadraticForm R (Fin n → R))
    (hd : ∀ i, Q (std n i) = T (std n i))
    (hb : ∀ p : Upper n,
      QuadraticMap.polar Q (std n p.1.1) (std n p.1.2) =
      QuadraticMap.polar T (std n p.1.1) (std n p.1.2)) :
    ∀ i j, QuadraticMap.polar Q (std n i) (std n j) =
      QuadraticMap.polar T (std n i) (std n j) := by
  intro i j
  rcases lt_trichotomy i j with hij | hij | hji
  · exact hb ⟨(i, j), hij⟩
  · subst j
    rw [QuadraticMap.polar_self, QuadraticMap.polar_self, hd]
  · rw [QuadraticMap.polar_comm Q, QuadraticMap.polar_comm T]
    exact hb ⟨(j, i), hji⟩

/-- This is the small coefficient-test lemma needed by the E8 lifting proof. -/
theorem quadratic_eq_of_diag_polar
    (Q T : QuadraticForm R (Fin n → R))
    (hd : ∀ i, Q (std n i) = T (std n i))
    (hb : ∀ p : Upper n,
      QuadraticMap.polar Q (std n p.1.1) (std n p.1.2) =
      QuadraticMap.polar T (std n p.1.1) (std n p.1.2)) : Q = T := by
  classical
  have hbb := polar_std_eq_of_upper Q T hd hb
  have hpolar (x y : Fin n → R) :
      QuadraticMap.polar Q x y = QuadraticMap.polar T x y := by
    calc
      QuadraticMap.polar Q x y =
          QuadraticMap.polar Q (∑ i, x i • std n i) (∑ i, y i • std n i) := by
            rw [std_decomposition, std_decomposition]
      _ = QuadraticMap.polar T (∑ i, x i • std n i) (∑ i, y i • std n i) := by
            simp only [polar_finset_sum_left, polar_finset_sum_right,
              QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hbb]
      _ = QuadraticMap.polar T x y := by rw [std_decomposition, std_decomposition]
  apply QuadraticMap.ext
  intro x
  have hsum (s : Finset (Fin n)) :
      Q (∑ i ∈ s, x i • std n i) = T (∑ i ∈ s, x i • std n i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha, QuadraticMap.map_add,
          Q.map_smul, T.map_smul, hd, ih, hpolar]
  simpa only [std_decomposition] using hsum Finset.univ

/-- Matrix-vector multiplication as a linear map; no coordinate expansion. -/
def matrixLinear (X : Mat n R) : (Fin n → R) →ₗ[R] (Fin n → R) where
  toFun := X.mulVec
  map_add' x y := Matrix.mulVec_add X x y
  map_smul' c x := by
    funext i
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_left_comm]

@[simp] theorem mulVec_std (X : Mat n R) (i : Fin n) :
    X.mulVec (std n i) = fun j => X j i := by
  funext j
  simp [Matrix.mulVec, dotProduct, std, Pi.single_apply]

/-- Exactly n diagonal tests and binomial(n,2) polar tests suffice. -/
theorem matrix_preserves_iff_diag_polar
    (Q : QuadraticForm R (Fin n → R)) (X : Mat n R) :
    (∀ v, Q (X.mulVec v) = Q v) ↔
      (∀ i, Q (X.mulVec (std n i)) = Q (std n i)) ∧
      (∀ p : Upper n,
        QuadraticMap.polar Q (X.mulVec (std n p.1.1)) (X.mulVec (std n p.1.2)) =
        QuadraticMap.polar Q (std n p.1.1) (std n p.1.2)) := by
  constructor
  · intro h
    refine ⟨fun i => h (std n i), ?_⟩
    intro p
    simp only [QuadraticMap.polar, ← Matrix.mulVec_add, h]
  · rintro ⟨hd, hb⟩
    have heq : Q.comp (matrixLinear X) = Q := by
      apply quadratic_eq_of_diag_polar
      · exact hd
      · intro p
        simpa [QuadraticMap.polar, matrixLinear, Matrix.mulVec_add] using hb p
    intro v
    exact congrArg (fun q : QuadraticForm R (Fin n → R) => q v) heq

/-- The only first-order quadratic identity used at the dyadic lifting step. -/
theorem quadratic_first_order_mod_four
    (Q : QuadraticForm (ZMod 4) (Fin n → ZMod 4))
    (u v : Fin n → ZMod 4) :
    Q (u + (2 : ZMod 4) • v) =
      Q u + (2 : ZMod 4) * QuadraticMap.polar Q u v := by
  rw [QuadraticMap.map_add (Q : (Fin n → ZMod 4) → ZMod 4) u ((2 : ZMod 4) • v),
    Q.map_smul, QuadraticMap.polar_smul_right]
  norm_num [smul_eq_mul]
  rw [show (4 : ZMod 4) = 0 by decide, zero_mul]

theorem polar_first_order_mod_four
    (Q : QuadraticForm (ZMod 4) (Fin n → ZMod 4))
    (u v w z : Fin n → ZMod 4) :
    QuadraticMap.polar Q (u + (2 : ZMod 4) • v) (w + (2 : ZMod 4) • z) =
      QuadraticMap.polar Q u w + (2 : ZMod 4) *
        (QuadraticMap.polar Q u z + QuadraticMap.polar Q w v) := by
  simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_eq_mul]
  rw [QuadraticMap.polar_comm Q v w]
  ring_nf
  have h4 : (4 : ZMod 4) = 0 := by decide
  simp [h4]

/-- A matrix product entry, expressed as a bilinear pairing of columns. -/
theorem transpose_bilinear_entry (X B A : Mat n R) (i j : Fin n) :
    (X.transpose * B * A) i j =
      dotProduct (fun k => X k i) (B.mulVec (fun k => A k j)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end QuadraticBasis

abbrev F := ZMod 2
abbrev R4 := ZMod 4
abbrev V (R : Type*) := Fin 8 → R
abbrev col {R : Type*} (M : Mat 8 R) (j : Fin 8) : V R := fun i => M i j

/-- Wrap the existing polynomial, without changing its normalization. -/
def Q (R : Type*) [CommRing R] : QuadraticForm R (V R) :=
  QuadraticMap.ofPolar e8QuadraticPolynomial
    (by
      intro a x
      simp only [e8QuadraticPolynomial, Pi.smul_apply, smul_eq_mul]
      ring)
    (by
      intro x y z
      simp only [QuadraticMap.polar, e8QuadraticPolynomial, Pi.add_apply]
      ring)
    (by
      intro a x y
      simp only [QuadraticMap.polar, e8QuadraticPolynomial,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring)

@[simp] theorem Q_apply {R : Type*} [CommRing R] (x : V R) :
    Q R x = e8QuadraticPolynomial x := rfl

abbrev b {R : Type*} [CommRing R] (x y : V R) : R :=
  QuadraticMap.polar (Q R) x y

def red : R4 →+* F := ZMod.castHom (by norm_num : 2 ∣ 4) F
abbrev liftV (v : V F) : V R4 := fun i => zmodTwoLiftToFour (v i)
abbrev redV (v : V R4) : V F := fun i => red (v i)
def embed (a : F) : R4 := 2 * zmodTwoLiftToFour a
/-- This is only used on even residues, as proved at each use. -/
def halfEven (a : R4) : F := ((a.val / 2 : ℕ) : F)

theorem two_mul_eq_embed (a : R4) : 2 * a = embed (red a) := by
  exact (by decide : ∀ a : R4, 2 * a = embed (red a)) a

theorem add_embed_eq_iff (a c : R4) (t : F) (h : red a = red c) :
    a + embed t = c ↔ t = halfEven (c - a) := by
  exact (by decide : ∀ (a c : R4) (t : F), red a = red c →
    (a + embed t = c ↔ t = halfEven (c - a))) a c t h

@[simp] theorem redV_liftV (v : V F) : redV (liftV v) = v := by
  funext i
  exact zmodTwoLiftToFour_to_modTwo (v i)

@[simp] theorem redV_std (i : Fin 8) :
    redV (std 8 i : V R4) = (std 8 i : V F) := by
  funext j
  simp [redV, std, Pi.single_apply]

@[simp] theorem redV_add (x y : V R4) : redV (x + y) = redV x + redV y := by
  funext i
  exact map_add red (x i) (y i)

@[simp] theorem red_Q (v : V R4) : red (Q R4 v) = Q F (redV v) := by
  exact map_e8QuadraticPolynomial red v

@[simp] theorem red_b (x y : V R4) : red (b x y) = b (redV x) (redV y) := by
  simp only [b, QuadraticMap.polar, map_sub, red_Q, redV_add]

def B : Mat 8 F :=
  !![0, 1, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 1;
    0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0]

def Binv : Mat 8 F :=
  !![0, 1, 0, 0, 0, 0, 0, 1;
    1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 1, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 1, 0, 1;
    1, 0, 1, 0, 1, 0, 1, 0]

/-- Fixed, small arithmetic certificate. -/
theorem B_mul_Binv : B * Binv = 1 := by decide

/-- Multiplication by the fixed E8 polar matrix, expanded row-by-row. -/
theorem B_mulVec_eq (y : V F) :
    B.mulVec y = fun i =>
      match i with
      | 0 => y 1
      | 1 => y 0 + y 2
      | 2 => y 1 + y 3 + y 7
      | 3 => y 2 + y 4
      | 4 => y 3 + y 5
      | 5 => y 4 + y 6
      | 6 => y 5
      | 7 => y 2 := by
  funext i
  fin_cases i <;> simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]

/-- The fixed E8 polar matrix represents the original polar form over `𝔽₂`. -/
theorem dot_B_mulVec_eq_e8PolarBilinear (x y : V F) :
    dotProduct x (B.mulVec y) = e8PolarBilinear x y := by
  rw [B_mulVec_eq]
  simp only [dotProduct, Fin.sum_univ_eight, e8PolarBilinear]
  ring

/-- The polar form is represented by the fixed matrix `B`. -/
theorem b_eq_matrix (x y : V F) : b x y = dotProduct x (B.mulVec y) := by
  have hneg : ∀ a : F, -a = a := by decide
  change e8QuadraticPolynomial (x + y) - e8QuadraticPolynomial x -
    e8QuadraticPolynomial y = _
  simp only [sub_eq_add_neg, hneg]
  rw [← e8PolarBilinear_eq_quadratic_add]
  exact (dot_B_mulVec_eq_e8PolarBilinear x y).symm

theorem b_cols (Y A : Mat 8 F) (i j : Fin 8) :
    b (col Y i) (col A j) = (Y.transpose * B * A) i j := by
  rw [b_eq_matrix]
  exact (transpose_bilinear_entry Y B A i j).symm

theorem isometry_b_cols (Y : e8QuadraticIsometryModTwo) (i j : Fin 8) :
    b (col Y.1 i) (col Y.1 j) = b (std 8 i : V F) (std 8 j) := by
  rw [show col Y.1 i = Y.1.mulVec (std 8 i) by exact (mulVec_std Y.1 i).symm,
    show col Y.1 j = Y.1.mulVec (std 8 j) by exact (mulVec_std Y.1 j).symm]
  simp only [b, QuadraticMap.polar, ← Matrix.mulVec_add, Q_apply, Y.2]

theorem isometry_matrix (Y : e8QuadraticIsometryModTwo) :
    Y.1.transpose * B * Y.1 = B := by
  funext i j
  rw [← b_cols, isometry_b_cols, b_eq_matrix]
  simp [std, Matrix.mulVec, dotProduct, Pi.single_apply]

def U (Y : e8QuadraticIsometryModTwo) : Mat 8 F := Y.1.transpose * B

def Uinv (Y : e8QuadraticIsometryModTwo) : Mat 8 F := Y.1 * Binv

theorem U_mul_Uinv (Y : e8QuadraticIsometryModTwo) : U Y * Uinv Y = 1 := by
  rw [U, Uinv, ← Matrix.mul_assoc, isometry_matrix, B_mul_Binv]

def changeEquiv (Y : e8QuadraticIsometryModTwo) : Mat 8 F ≃ Mat 8 F :=
  leftMatrixEquiv (U Y) (Uinv Y) (U_mul_Uinv Y)

/-- Defects of the canonical `0/1` lift; no assumption that this lift is an isometry. -/
def diagTarget (Y : e8QuadraticIsometryModTwo) (i : Fin 8) : F :=
  halfEven (Q R4 (std 8 i) - Q R4 (liftV (col Y.1 i)))

def crossTarget (Y : e8QuadraticIsometryModTwo) (p : Upper 8) : F :=
  halfEven (b (std 8 p.1.1 : V R4) (std 8 p.1.2) -
    b (liftV (col Y.1 p.1.1)) (liftV (col Y.1 p.1.2)))

theorem diag_same_reduction (Y : e8QuadraticIsometryModTwo) (i : Fin 8) :
    red (Q R4 (liftV (col Y.1 i))) = red (Q R4 (std 8 i)) := by
  rw [red_Q, red_Q, redV_liftV, redV_std]
  simpa only [Q_apply, mulVec_std] using Y.2 (std 8 i)

theorem cross_same_reduction (Y : e8QuadraticIsometryModTwo) (i j : Fin 8) :
    red (b (liftV (col Y.1 i)) (liftV (col Y.1 j))) =
      red (b (std 8 i : V R4) (std 8 j)) := by
  rw [red_b, red_b, redV_liftV, redV_liftV, redV_std, redV_std]
  exact isometry_b_cols Y i j

/-- Corrected columns; never unfold the entire eight-variable matrix action. -/
theorem corrected_column (Y A : Mat 8 F) (i : Fin 8) :
    (e8MatrixModFourCorrectedLift Y A).mulVec (std 8 i) =
      liftV (col Y i) + (2 : R4) • liftV (col A i) := by
  rw [mulVec_std]
  funext j
  rfl

theorem corrected_diag (Y : e8QuadraticIsometryModTwo) (A : Mat 8 F) (i : Fin 8) :
    Q R4 ((e8MatrixModFourCorrectedLift Y.1 A).mulVec (std 8 i)) =
      Q R4 (liftV (col Y.1 i)) + embed ((changeEquiv Y A) i i) := by
  rw [corrected_column, quadratic_first_order_mod_four, two_mul_eq_embed,
    red_b, redV_liftV, redV_liftV, b_cols]
  rfl

theorem corrected_cross (Y : e8QuadraticIsometryModTwo) (A : Mat 8 F)
    (i j : Fin 8) :
    b ((e8MatrixModFourCorrectedLift Y.1 A).mulVec (std 8 i))
      ((e8MatrixModFourCorrectedLift Y.1 A).mulVec (std 8 j)) =
      b (liftV (col Y.1 i)) (liftV (col Y.1 j)) +
        embed ((changeEquiv Y A) i j + (changeEquiv Y A) j i) := by
  rw [corrected_column, corrected_column]
  change QuadraticMap.polar (Q R4)
      (liftV (col Y.1 i) + (2 : R4) • liftV (col A i))
      (liftV (col Y.1 j) + (2 : R4) • liftV (col A j)) =
    b (liftV (col Y.1 i)) (liftV (col Y.1 j)) +
      embed ((changeEquiv Y A) i j + (changeEquiv Y A) j i)
  rw [polar_first_order_mod_four, two_mul_eq_embed, map_add,
    red_b, red_b, redV_liftV, redV_liftV, redV_liftV, redV_liftV,
    b_cols, b_cols]
  rfl

/-- This is the substantive bridge from the native correction predicate to
36 scalar equations. It is not a cardinality hypothesis. -/
theorem correction_iff_coefficients (Y : e8QuadraticIsometryModTwo) (A : Mat 8 F) :
    (∀ v : V R4,
      e8QuadraticPolynomial ((e8MatrixModFourCorrectedLift Y.1 A).mulVec v) =
        e8QuadraticPolynomial v) ↔
      HasCoefficients (diagTarget Y) (crossTarget Y) (changeEquiv Y A) := by
  change (∀ v, Q R4 ((e8MatrixModFourCorrectedLift Y.1 A).mulVec v) = Q R4 v) ↔ _
  rw [matrix_preserves_iff_diag_polar]
  constructor
  · rintro ⟨hd, hb⟩
    constructor
    · intro i
      have h := hd i
      rw [corrected_diag] at h
      exact (add_embed_eq_iff _ _ _ (diag_same_reduction Y i)).mp h
    · intro p
      have h := hb p
      change b ((e8MatrixModFourCorrectedLift Y.1 A).mulVec (std 8 p.1.1))
          ((e8MatrixModFourCorrectedLift Y.1 A).mulVec (std 8 p.1.2)) =
        b (std 8 p.1.1 : V R4) (std 8 p.1.2) at h
      rw [corrected_cross] at h
      exact (add_embed_eq_iff _ _ _
        (cross_same_reduction Y p.1.1 p.1.2)).mp h
  · rintro ⟨hd, hb⟩
    constructor
    · intro i
      rw [corrected_diag]
      exact (add_embed_eq_iff _ _ _ (diag_same_reduction Y i)).mpr (hd i)
    · intro p
      change b ((e8MatrixModFourCorrectedLift Y.1 A).mulVec (std 8 p.1.1))
          ((e8MatrixModFourCorrectedLift Y.1 A).mulVec (std 8 p.1.2)) =
        b (std 8 p.1.1 : V R4) (std 8 p.1.2)
      rw [corrected_cross]
      exact (add_embed_eq_iff _ _ _
        (cross_same_reduction Y p.1.1 p.1.2)).mpr (hb p)

/-- The parameters are the 28 strictly lower-triangular entries of `U(Y)A`. -/
def correctionFiberEquiv (Y : e8QuadraticIsometryModTwo) :
    e8QuadraticIsometryModFourCorrectionFiber Y ≃ (Upper 8 → F) :=
  predicateFiberEquiv _ (changeEquiv Y) (diagTarget Y) (crossTarget Y)
    (correction_iff_coefficients Y)

/-- The uniform mod-`4` lift count for every E8 mod-`2` quadratic isometry. -/
theorem correctionFiber_card (Y : e8QuadraticIsometryModTwo) :
    Nat.card (e8QuadraticIsometryModFourCorrectionFiber Y) = 2 ^ 28 := by
  calc
    Nat.card (e8QuadraticIsometryModFourCorrectionFiber Y) = Nat.card (Upper 8 → F) :=
      Nat.card_congr (correctionFiberEquiv Y)
    _ = 2 ^ 28 := by simp [F, Nat.card_eq_fintype_card, upper_eight_card]

end E8CorrectionFiber

/-- Production name for the uniform `2^28` E8 correction-fiber count. -/
theorem e8QuadraticIsometryModFourCorrectionFiber_card
    (Y : e8QuadraticIsometryModTwo) :
    Nat.card (e8QuadraticIsometryModFourCorrectionFiber Y) = 2 ^ 28 :=
  E8CorrectionFiber.correctionFiber_card Y

/-- The fiber of the native mod-`4` to mod-`2` E8 quadratic-isometry map over
a fixed mod-`2` isometry is the explicit correction fiber over that isometry. -/
theorem e8QuadraticIsometryModFourToModTwo_fiber_natCard_eq_correctionFiber
    (Y : e8QuadraticIsometryModTwo) :
    Nat.card {X : e8QuadraticIsometryModFour // e8QuadraticIsometryModFourToModTwo X = Y} =
      Nat.card (e8QuadraticIsometryModFourCorrectionFiber Y) := by
  rw [← e8QuadraticIsometryModFour_rawReductionFiber_natCard_eq_correctionFiber Y]
  refine Nat.card_congr ?_
  exact
    { toFun := fun X =>
        ⟨X.1, by
          exact congrArg Subtype.val X.2⟩
      invFun := fun X =>
        ⟨X.1, by
          apply Subtype.ext
          exact X.2⟩
      left_inv := fun X => by
        apply Subtype.ext
        rfl
      right_inv := fun X => by
        apply Subtype.ext
        rfl }

/-- The full E8 `ZMod 4` quadratic-isometry target factors into the counted
mod-`2` base and a uniform `2^28` correction fiber. -/
theorem e8QuadraticIsometryModFour_natCard_eq_modTwo_mul_pow :
    Nat.card e8QuadraticIsometryModFour = Nat.card e8QuadraticIsometryModTwo * 2 ^ 28 := by
  exact nat_card_eq_mul_of_fiber_card e8QuadraticIsometryModFourToModTwo (2 ^ 28)
    (fun Y => by
      rw [e8QuadraticIsometryModFourToModTwo_fiber_natCard_eq_correctionFiber]
      exact e8QuadraticIsometryModFourCorrectionFiber_card Y)

/-- Fully evaluated cardinality of the E8 `ZMod 4` quadratic-isometry target,
kept in factored form matching the mod-`2` base and correction fiber. -/
theorem e8QuadraticIsometryModFour_natCard_eq_348364800_mul_pow :
    Nat.card e8QuadraticIsometryModFour = 348364800 * 2 ^ 28 := by
  rw [e8QuadraticIsometryModFour_natCard_eq_modTwo_mul_pow,
    e8QuadraticIsometryModTwo_natCard_eq_348364800]

/-- Fully evaluated cardinality of the E8 `ZMod 4` quadratic-isometry target
in the normalization used by the depth-three local-factor bridge. -/
theorem e8QuadraticIsometryModFour_natCard_eq_42525_mul_pow :
    Nat.card e8QuadraticIsometryModFour = 42525 * 2 ^ 41 := by
  rw [e8QuadraticIsometryModFour_natCard_eq_348364800_mul_pow]
  norm_num

/-- Fully evaluated cardinality of the E8 depth-three `ZMod 4` matrix target. -/
theorem e8Lattice_depthThreeCoordinateSolutionMatrix_natCard_eq_42525_mul_pow :
    Nat.card e8LatticeDepthThreeCoordinateSolutionMatrix = 42525 * 2 ^ 41 := by
  rw [e8LatticeDepthThreeCoordinateSolutionMatrix_natCard_eq_quadraticIsometryModFour,
    e8QuadraticIsometryModFour_natCard_eq_42525_mul_pow]

/-- Fully evaluated cardinality of the E8 depth-three filtered finite-set target. -/
theorem e8Lattice_depthThreeCoordinateSolutionMatrices_card_eq_42525_mul_pow :
    e8LatticeDepthThreeCoordinateSolutionMatrices.card = 42525 * 2 ^ 41 := by
  rw [e8Lattice_depthThreeCoordinateSolutionMatrices_card,
    e8Lattice_depthThreeCoordinateSolutionMatrix_natCard_eq_42525_mul_pow]

/-- Fully evaluated cardinality of the E8 depth-three quotient-family target. -/
theorem e8Lattice_depthThreeCoordinateSolutionFamily_natCard_eq_42525_mul_pow :
    Nat.card e8LatticeDepthThreeCoordinateSolutionFamily = 42525 * 2 ^ 41 := by
  rw [← e8Lattice_depthThreeCoordinateSolutionMatrix_natCard,
    e8Lattice_depthThreeCoordinateSolutionMatrix_natCard_eq_42525_mul_pow]

/-- Fully evaluated E8 depth-three coordinate quotient count. -/
theorem e8Lattice_primePowCoordinateSubmodule_count_eq_42525_mul_pow :
    coordinateLocalDualQuotientCount e8Lattice 2 3
      (primePowCoordinateSubmodule (n := 8) 2 2)
      (primePowCoordinateSubmodule_rank (n := 8) 2 2) = 42525 * 2 ^ 41 := by
  rw [← e8Lattice_depthThreeCoordinateSolutionFamily_natCard,
    e8Lattice_depthThreeCoordinateSolutionFamily_natCard_eq_42525_mul_pow]

/-- The native dyadic Schulze--Pillot local factor for the E8 seed at `2`,
proved through the evaluated depth-three coordinate quotient count. -/
theorem e8Lattice_massLocalFactor_two_eq :
    e8Lattice.massLocalFactor 2 = (42525 / 256 : ℝ) :=
  e8Lattice_massLocalFactor_two_eq_of_primePowCoordinateSubmoduleCount
    e8Lattice_primePowCoordinateSubmodule_count_eq_42525_mul_pow

end PositiveDefiniteIntegralLattice

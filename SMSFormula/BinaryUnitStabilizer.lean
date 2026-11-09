import SMSFormula.BinaryDiscriminantOrder
import SMSFormula.BinaryProperNormalization

/-!
# The full proper stabilizer of a primitive binary norm ideal

Primitivity makes every determinant-one polynomial isometry multiplication
by an integral norm-one order unit. The same matrix acts on the original
lattice. No classification of imaginary quadratic units is assumed.
-/

open Matrix

namespace BinaryNormIdeal

open scoped QuadraticAlgebra

private lemma proper_polynomial_matrix_relations (a b c : ℤ)
    (U : Matrix (Fin 2) (Fin 2) ℤ) (hd : U.det = 1)
    (hp : ∀ x : Fin 2 → ℤ,
      a * (U.mulVec x) 0 ^ 2 + b * (U.mulVec x) 0 * (U.mulVec x) 1 +
        c * (U.mulVec x) 1 ^ 2 = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) :
    a * (U 1 1 - U 0 0) = b * U 1 0 ∧ a * U 0 1 = -c * U 1 0 := by
  have hA := hp ![1, 0]
  have hC := hp ![0, 1]
  have hS := hp ![1, 1]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at hA hC hS
  norm_num at hA hC hS
  let H : Matrix (Fin 2) (Fin 2) ℤ := !![2*a, b; b, 2*c]
  have hcong : U.transpose * H * U = H := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [H, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    · nlinarith [hA]
    · nlinarith [hS, hA, hC]
    · nlinarith [hS, hA, hC]
    · nlinarith [hC]
  have hlin : H * U = U.adjugate.transpose * H := by
    have h := congrArg (fun M => M * U.adjugate) hcong
    simp only [Matrix.mul_assoc, Matrix.mul_adjugate, hd, one_smul, Matrix.mul_one] at h
    have ht := congrArg Matrix.transpose h
    have hH : H.transpose = H := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hH] using ht
  have h00 := congrArg (fun M => M 0 0) hlin
  have h01 := congrArg (fun M => M 0 1) hlin
  simp only [H, Matrix.mul_apply, Matrix.adjugate_fin_two, Matrix.transpose_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h00 h01
  constructor <;> nlinarith

/-- Every proper isometry of a primitive binary polynomial is the integral
multiplication matrix of a norm-one element of its coefficient order. -/
theorem exists_norm_one_of_proper_polynomial_matrix (a b c : ℤ) (ha : a ≠ 0)
    (hprim : Int.gcd a (Int.gcd b c : ℤ) = 1)
    (U : Matrix (Fin 2) (Fin 2) ℤ) (hd : U.det = 1)
    (hp : ∀ x : Fin 2 → ℤ,
      a * (U.mulVec x) 0 ^ 2 + b * (U.mulVec x) 0 * (U.mulVec x) 1 +
        c * (U.mulVec x) 1 ^ 2 = a * x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2) :
    ∃ z : CoefficientOrder a b c, z.norm = 1 ∧ multiplicationMatrix a b c z = U := by
  obtain ⟨hs, hq⟩ := proper_polynomial_matrix_relations a b c U hd hp
  have hbr : a ∣ b * U 1 0 := ⟨U 1 1 - U 0 0, hs.symm⟩
  have hcr : a ∣ c * U 1 0 := ⟨-U 0 1, by linear_combination hq⟩
  have hg : a ∣ (Int.gcd b c : ℤ) * U 1 0 := by
    have h := dvd_add (dvd_mul_of_dvd_left hbr (Int.gcdA b c))
      (dvd_mul_of_dvd_left hcr (Int.gcdB b c))
    have heq : b * U 1 0 * Int.gcdA b c + c * U 1 0 * Int.gcdB b c =
        (Int.gcd b c : ℤ) * U 1 0 := by rw [Int.gcd_eq_gcd_ab]; ring
    rwa [heq] at h
  have hr : a ∣ U 1 0 := (Int.isCoprime_iff_gcd_eq_one.mpr hprim).dvd_of_dvd_mul_left hg
  obtain ⟨v, hv⟩ := hr
  have hq' : U 0 1 = -c * v := by
    apply mul_left_cancel₀ ha
    linear_combination hq - c * hv
  have hs' : U 1 1 = U 0 0 + b * v := by
    apply mul_left_cancel₀ ha
    linear_combination hs + b * hv
  let z : CoefficientOrder a b c := ⟨U 0 0, v⟩
  have hM : multiplicationMatrix a b c z = U := by
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact hq'.symm
    · exact hv.symm
    · exact hs'.symm
  refine ⟨z, ?_, hM⟩
  rw [← det_multiplicationMatrix, hM, hd]

/-- An integral element of norm one is a unit with its exact conjugate as inverse. -/
def unitOfNormOne (a b c : ℤ) (z : CoefficientOrder a b c) (hz : z.norm = 1) :
    (CoefficientOrder a b c)ˣ where
  val := z
  inv := star z
  val_inv := by rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hz]; simp
  inv_val := by rw [mul_comm, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hz]; simp

/-- Norm-one units in the common ring fixed only by D. -/
abbrev DiscriminantNormOneUnits (D : ℤ) :=
  {u : (DiscriminantOrder D)ˣ // (u.val : DiscriminantOrder D).norm = 1}

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

/-- The norm-one-unit action exhausts the actual proper lattice stabilizer. -/
theorem binaryNormOneUnitToProperIsometry_surjective (K : PositiveDefiniteIntegralLattice 2) :
    Function.Surjective K.binaryNormOneUnitToProperIsometry := by
  intro U
  let a := K.pairingMatrix 0 0 / (K.binaryContent : ℤ)
  let b := (2 * K.pairingMatrix 0 1) / (K.binaryContent : ℤ)
  let c := K.pairingMatrix 1 1 / (K.binaryContent : ℤ)
  have hmat : U.val.transpose * K.pairingMatrix.map (Int.cast : ℤ → ℤ) * U.val =
      K.pairingMatrix.map (Int.cast : ℤ → ℤ) := by
    simpa only [Int.cast_id, Matrix.map_id] using U.prop.1.2
  have hp := (binaryPrimitivePolynomialOver_matrix_congruence_iff K K rfl U.val).mp hmat
  simp only [binaryPrimitivePolynomialOver_int, binaryPrimitivePolynomial_apply] at hp
  obtain ⟨z, hz, hM⟩ := BinaryNormIdeal.exists_norm_one_of_proper_polynomial_matrix a b c
    (ne_of_gt K.binaryPrimitivePolynomial_leading_pos)
    K.binaryPrimitivePolynomial_coefficients_gcd_eq_one U.val U.prop.2 hp
  let u := BinaryNormIdeal.unitOfNormOne a b c z hz
  refine ⟨⟨u, hz⟩, ?_⟩
  apply Subtype.ext
  exact hM

/-- Exact order-unit/proper-stabilizer correspondence on the original carrier. -/
noncomputable def binaryNormOneUnitsEquivProperIsometryGroup (K : PositiveDefiniteIntegralLattice 2) :
    {u : K.binaryCoefficientOrderˣ // (u.val : K.binaryCoefficientOrder).norm = 1} ≃
      K.ProperIsometryGroup :=
  Equiv.ofBijective K.binaryNormOneUnitToProperIsometry
    ⟨K.binaryNormOneUnitToProperIsometry_injective, K.binaryNormOneUnitToProperIsometry_surjective⟩

/-- Norm-preserving generator translation identifies the two unit carriers. -/
noncomputable def binaryNormOneUnitsEquivDiscriminantNormOneUnits (K : PositiveDefiniteIntegralLattice 2) :
    {u : K.binaryCoefficientOrderˣ // (u.val : K.binaryCoefficientOrder).norm = 1} ≃
      BinaryNormIdeal.DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant :=
  (Units.mapEquiv K.binaryCoefficientOrderEquivDiscriminantOrder.toMulEquiv).toEquiv.subtypeEquiv
    (by
      intro u
      change (u : K.binaryCoefficientOrder).norm = 1 ↔
        (K.binaryCoefficientOrderEquivDiscriminantOrder (u : K.binaryCoefficientOrder)).norm = 1
      rw [norm_binaryCoefficientOrderEquivDiscriminantOrder])

/-- The actual proper stabilizer is exactly the common discriminant-order
norm-one-unit carrier. This is a carrier bijection, with no pointwise O/SO doubling. -/
noncomputable def properIsometryGroupEquivDiscriminantNormOneUnits (K : PositiveDefiniteIntegralLattice 2) :
    K.ProperIsometryGroup ≃ BinaryNormIdeal.DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant :=
  K.binaryNormOneUnitsEquivProperIsometryGroup.symm.trans
    K.binaryNormOneUnitsEquivDiscriminantNormOneUnits

theorem finite_discriminantNormOneUnits (K : PositiveDefiniteIntegralLattice 2) :
    Finite (BinaryNormIdeal.DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant) :=
  Finite.of_equiv K.ProperIsometryGroup K.properIsometryGroupEquivDiscriminantNormOneUnits

/-- Exact proper stabilizer order, expressed without a caller unit-cardinality premise. -/
theorem card_properIsometryGroup_eq_discriminantNormOneUnits (K : PositiveDefiniteIntegralLattice 2) :
    Fintype.card K.ProperIsometryGroup =
      Nat.card (BinaryNormIdeal.DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant) := by
  simpa only [Nat.card_eq_fintype_card] using
    Nat.card_congr K.properIsometryGroupEquivDiscriminantNormOneUnits

/-- All actual binary lattices with the same primitive discriminant have the
same proper stabilizer order. No equality of ordinary stabilizer orders is used. -/
theorem card_properIsometryGroup_eq_of_binaryPrimitiveDiscriminant_eq
    (K L : PositiveDefiniteIntegralLattice 2) (hD : K.binaryPrimitiveDiscriminant = L.binaryPrimitiveDiscriminant) :
    Fintype.card K.ProperIsometryGroup = Fintype.card L.ProperIsometryGroup := by
  rw [card_properIsometryGroup_eq_discriminantNormOneUnits,
    card_properIsometryGroup_eq_discriminantNormOneUnits, hD]

/-- The actual proper-class mass is its original finite proper-genus count
divided by the common order-unit count. The proper classes have not been
replaced by ideal classes or by a total class number. -/
theorem properClassGenusMass_eq_card_div_discriminantNormOneUnits (K : PositiveDefiniteIntegralLattice 2) :
    K.properClassGenusMass = (Fintype.card K.properGenus : ℚ) /
      Nat.card (BinaryNormIdeal.DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant) := by
  classical
  unfold properClassGenusMass
  have hcard (C : K.properGenus) :
      Fintype.card (properGenusClassRepresentative K C).ProperIsometryGroup =
        Nat.card (BinaryNormIdeal.DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant) := by
    rw [card_properIsometryGroup_eq_discriminantNormOneUnits]
    rw [← (properGenusClassRepresentative_isSameGenus K C).binaryPrimitiveDiscriminant_eq]
  simp_rw [hcard]
  simp [div_eq_mul_inv]

/-- Reuse the existing aggregate proper/full mass theorem to reduce ordinary
binary mass to the actual proper-genus count and the common norm-one units. -/
theorem ordinaryGenusMass_eq_card_properGenus_div_two_discriminantNormOneUnits
    (K : PositiveDefiniteIntegralLattice 2) :
    K.ordinaryGenusMass = (Fintype.card K.properGenus : ℚ) /
      (2 * (Nat.card (BinaryNormIdeal.DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant) : ℚ)) := by
  have htwo : K.properClassGenusMass = 2 * K.ordinaryGenusMass := by
    exact_mod_cast K.properClassGenusMass_eq_two_ordinaryGenusMass
  calc
    K.ordinaryGenusMass = (2 * K.ordinaryGenusMass) / 2 := by ring
    _ = K.properClassGenusMass / 2 := by rw [htwo]
    _ = ((Fintype.card K.properGenus : ℚ) /
        Nat.card (BinaryNormIdeal.DiscriminantNormOneUnits K.binaryPrimitiveDiscriminant)) / 2 := by
      rw [properClassGenusMass_eq_card_div_discriminantNormOneUnits]
    _ = _ := by rw [div_div]; congr 1; ring

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.exists_norm_one_of_proper_polynomial_matrix
#assert_standard_axioms BinaryNormIdeal.unitOfNormOne
#assert_standard_axioms BinaryNormIdeal.DiscriminantNormOneUnits
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormOneUnitToProperIsometry_surjective
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormOneUnitsEquivProperIsometryGroup
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryNormOneUnitsEquivDiscriminantNormOneUnits
#assert_standard_axioms PositiveDefiniteIntegralLattice.properIsometryGroupEquivDiscriminantNormOneUnits
#assert_standard_axioms PositiveDefiniteIntegralLattice.finite_discriminantNormOneUnits
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_properIsometryGroup_eq_discriminantNormOneUnits
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_properIsometryGroup_eq_of_binaryPrimitiveDiscriminant_eq
#assert_standard_axioms PositiveDefiniteIntegralLattice.properClassGenusMass_eq_card_div_discriminantNormOneUnits
#assert_standard_axioms PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_card_properGenus_div_two_discriminantNormOneUnits

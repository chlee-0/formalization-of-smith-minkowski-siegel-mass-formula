import SMSFormula.FiniteOrthogonalGroupGeneralRepresentation
import SMSFormula.PadicSpecialOrthogonalDifferentialCongruence
import SMSFormula.RationalCliffordSpinCandidateAlmostEverywhereIntegralLifting
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorRangeGoodPlace
import SMSFormula.RationalPadicUnitSquareClass

/-!
# The constructive lower bound for the good-place integral spinor range

This file records the constructive half of the good-place spinor-
range calculation.  In rank `r + 2`, an odd unimodular residue form represents
both `1` and a nonsquare.  Lifting the representing vectors gives two integral
reflections.  Their product is integral special orthogonal, and its spinor norm
is the nontrivial unit square class.

The upper inclusion, saying that every integral special-orthogonal spinor norm
is represented by a p-adic unit, is deliberately isolated below as a separate
certificate.  It requires integral Cartan--Dieudonne or equivalent arithmetic
input and is not inferred from the field-level Spin kernel theorem.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Matrix
open QuadraticMap.ReflectionWord
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- An odd unimodular form of rank `r + 2` has an integral reflection whose
norm has any prescribed nonzero residue. -/
theorem exists_localPadicIntegralReflectionData_residue_norm_of_rank_add_two
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    (hdet : IsUnit (L.pairingMatrix_padic p).det)
    (c : ZMod p) (hc : c ≠ 0) :
    ∃ d : LocalPadicIntegralReflectionData L p,
      PadicInt.toZMod
          (d.vector ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) d.vector) = c := by
  let A : Matrix (Fin (r + 2)) (Fin (r + 2)) (ZMod p) :=
    (L.pairingMatrix_padic p).map PadicInt.toZMod
  have hA_symm : A.IsSymm := by
    simpa [A, pairingMatrix_padic] using
      ((L.form_symm.map (Int.castRingHom ℤ_[p])).map PadicInt.toZMod)
  have hA_det : A.det ≠ 0 := by
    have hunit : IsUnit (PadicInt.toZMod (L.pairingMatrix_padic p).det) :=
      hdet.map PadicInt.toZMod
    have hmapdet :
        A.det = PadicInt.toZMod (L.pairingMatrix_padic p).det := by
      simpa [A] using
        (RingHom.map_det PadicInt.toZMod (L.pairingMatrix_padic p)).symm
    rw [hmapdet]
    exact hunit.ne_zero
  have hchar : ringChar (ZMod p) ≠ 2 := by
    simpa [ZMod.ringChar_zmod_n] using hpodd
  obtain ⟨x, hx⟩ :=
    exists_vector_gramQuadraticValue_eq_of_rank_add_two
      A hA_symm hA_det hchar c hc
  let w : Fin (r + 2) → ℤ_[p] := fun i ↦ (x i).val
  have hw_res (i : Fin (r + 2)) : PadicInt.toZMod (w i) = x i := by
    apply ZMod.val_injective
    simp [w]
  let q : ℤ_[p] := w ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) w
  have hq_res : PadicInt.toZMod q = c := by
    calc
      PadicInt.toZMod q = gramQuadraticValue A x := by
        simp only [q, gramQuadraticValue, dotProduct, Matrix.mulVec, A,
          Matrix.map_apply]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [map_mul, hw_res]
        congr 1
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [map_mul, hw_res]
      _ = c := hx
  have hq_unit : IsUnit q := by
    by_contra hnot
    have hmem :
        q ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
      exact hnot
    exact hc (hq_res ▸ hmem)
  refine ⟨LocalPadicIntegralReflectionData.ofNormIsUnit L p w hq_unit, ?_⟩
  exact hq_res

/-- At an odd unimodular place there are integral reflections with square and
nonsquare unit residues. -/
theorem exists_integralReflectionData_square_and_nonsquare_residue
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    (hdet : IsUnit (L.pairingMatrix_padic p).det) :
    ∃ (c : ZMod p)
        (dOne dNonsquare : LocalPadicIntegralReflectionData L p),
      ¬ IsSquare c ∧
      PadicInt.toZMod
          (dOne.vector ⬝ᵥ
            Matrix.mulVec (L.pairingMatrix_padic p) dOne.vector) = 1 ∧
      PadicInt.toZMod
          (dNonsquare.vector ⬝ᵥ
            Matrix.mulVec (L.pairingMatrix_padic p) dNonsquare.vector) = c := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    simpa [ZMod.ringChar_zmod_n] using hpodd
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hchar
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hc
    subst c
    exact IsSquare.zero
  obtain ⟨dOne, hdOne⟩ :=
    exists_localPadicIntegralReflectionData_residue_norm_of_rank_add_two
      L p hpodd hdet 1 one_ne_zero
  obtain ⟨dNonsquare, hdNonsquare⟩ :=
    exists_localPadicIntegralReflectionData_residue_norm_of_rank_add_two
      L p hpodd hdet c hc0
  exact ⟨c, dOne, dNonsquare, hc, hdOne, hdNonsquare⟩

/-- A p-adic integral element with nonzero residue is a unit. -/
theorem isUnit_of_toZMod_ne_zero
    {p : ℕ} [Fact p.Prime] {q : ℤ_[p]}
    (hq : PadicInt.toZMod q ≠ 0) : IsUnit q := by
  by_contra hnot
  have hmem :
      q ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
    exact hnot
  exact hq hmem

/-- For an integral p-adic unit, squarehood in the field is detected by its
residue. -/
theorem isSquare_padic_coe_iff_isSquare_toZMod_of_isUnit
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {u : ℤ_[p]} (hu : IsUnit u) :
    IsSquare (u : ℚ_[p]) ↔ IsSquare (PadicInt.toZMod u) := by
  have hu0 : (u : ℚ_[p]) ≠ 0 :=
    PadicInt.coe_ne_zero.mpr hu.ne_zero
  have huval : (u : ℚ_[p]).valuation = 0 := by
    norm_cast
    exact PadicInt.valuation_eq_zero_of_isUnit hu
  have hfieldInt : IsSquare (u : ℚ_[p]) ↔ IsSquare u := by
    constructor
    · rintro ⟨x, hx⟩
      have hx0 : x ≠ 0 := by
        intro hxzero
        apply hu0
        simpa [hxzero] using hx
      have hxval : x.valuation = 0 := by
        have h := congrArg Padic.valuation hx
        rw [huval, Padic.valuation_mul hx0 hx0] at h
        omega
      have hxnorm : ‖x‖ = 1 := by
        rw [Padic.norm_eq_zpow_neg_valuation hx0, hxval]
        simp
      refine ⟨⟨x, hxnorm.le⟩, ?_⟩
      exact Subtype.ext hx
    · rintro ⟨x, hx⟩
      refine ⟨(x : ℚ_[p]), ?_⟩
      exact congrArg Subtype.val hx
  rw [hfieldInt]
  exact PadicInt.isSquare_iff_isSquare_toZMod_of_isUnit hpodd hu

/-- A nonsquare unit residue gives a nontrivial p-adic field square class. -/
theorem not_isSquare_padic_coe_of_not_isSquare_toZMod
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {u : ℤ_[p]} (hu : IsUnit u)
    (hres : ¬ IsSquare (PadicInt.toZMod u)) :
    ¬ IsSquare (u : ℚ_[p]) := by
  rwa [isSquare_padic_coe_iff_isSquare_toZMod_of_isUnit hpodd hu]

/-- The matrix underlying the original integral reflection is the cast of
its integral reflection matrix, hence the standard Gram reflection. -/
theorem LocalPadicIntegralReflectionData.stabilizer_matrix_eq_gramReflectionMatrix
    {n p : ℕ} [Fact p.Prime] {L : PositiveDefiniteIntegralLattice n}
    (d : LocalPadicIntegralReflectionData L p) :
    d.stabilizer.1.1.1 =
      gramReflectionMatrix (L.pairingMatrix_padicField p)
        (fun i ↦ (d.vector i : ℚ_[p])) := by
  change d.integralGL.1.map PadicInt.Coe.ringHom = _
  rw [d.integralGL_val]
  exact d.coe_matrix_eq_gramReflectionMatrix

/-- Two integral reflections, multiplied in this order, give an original
determinant-one integral stabilizer element. -/
noncomputable def LocalPadicIntegralReflectionData.specialPairHistorical
    {n p : ℕ} [Fact p.Prime] {L : PositiveDefiniteIntegralLattice n}
    (dFirst dSecond : LocalPadicIntegralReflectionData L p) :
    L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p := by
  refine ⟨dSecond.stabilizer * dFirst.stabilizer, ?_⟩
  change L.localPadicLatticeStabilizerDeterminant p
      (dSecond.stabilizer * dFirst.stabilizer) = 1
  rw [map_mul, dSecond.stabilizer_determinant,
    dFirst.stabilizer_determinant]
  simp

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance integralSpinorRangeUpperPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-! ## The exact missing upper inclusion -/

/-- Every restricted integral spinor norm at `v` is represented by a p-adic
unit.  This is the exact arithmetic upper inclusion still requiring an
integral Cartan--Dieudonne theorem or an equivalent congruence-kernel
argument.  It is deliberately independent of integral Spin lifting and the
two-sheet Haar calculation. -/
def CliffordSpinCandidateIntegralSpinorNormUnitValuedAt
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) : Prop :=
  (V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v).range ≤
    Rat.padicUnitSquareClassSubgroup
      (Rat.HeightOneSpectrum.primesEquiv v).1

/-- At an odd place, the missing unit-valuedness theorem bounds the actual
restricted spinor range by the two integral-unit square classes. -/
theorem heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_le_two_of_unitValued
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hpodd : (Rat.HeightOneSpectrum.primesEquiv v).1 ≠ 2)
    (hunit : V.CliffordSpinCandidateIntegralSpinorNormUnitValuedAt v) :
    V.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree v ≤ 2 := by
  let R := (V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v).range
  let U := Rat.padicUnitSquareClassSubgroup
    (Rat.HeightOneSpectrum.primesEquiv v).1
  have hcardU : Nat.card U = 2 :=
    Rat.natCard_padicUnitSquareClassSubgroup_eq_two
      (Rat.HeightOneSpectrum.primesEquiv v).1 hpodd
  letI : Finite U :=
    (Nat.card_pos_iff.mp (hcardU.symm ▸ (by norm_num : 0 < 2))).2
  have hcard := Nat.card_le_card_of_injective
    (Subgroup.inclusion hunit) (Subgroup.inclusion_injective hunit)
  rw [hcardU] at hcard
  exact hcard

end RationalQuadraticSpaceMatrix

namespace Rat

/-- A nonsquare field unit represents a nontrivial square class. -/
theorem squareClass_unit_ne_one_of_not_isSquare
    {K : Type*} [Field K] (u : Kˣ) (hu : ¬ IsSquare (u : K)) :
    (u : SquareClass K) ≠ 1 := by
  intro h
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_square] at h
  obtain ⟨y, hy⟩ := h
  apply hu
  refine ⟨(y : K), ?_⟩
  exact congrArg Units.val hy

end Rat

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The displayed scalar-extension quadratic form is its mapped Gram-matrix
quadratic value. -/
theorem commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue
    (K : Type*) [Field K] [CharZero K]
    (x : Fin n → K) :
    V.commutativeScalarExtensionQuadraticForm K x =
      gramQuadraticValue (V.specialOrthogonalMappedFormMatrix K) x := by
  simp only [commutativeScalarExtensionQuadraticForm,
    commutativeScalarExtensionFormMatrix,
    specialOrthogonalMappedFormMatrix, Matrix.toQuadraticMap',
    LinearMap.BilinMap.toQuadraticMap, gramQuadraticValue]
  exact Matrix.toLinearMap₂'_apply'
    (V.specialOrthogonalMappedFormMatrix K) x x

/-- The polar form of the displayed quadratic form is twice the mapped Gram
pairing. -/
theorem commutativeScalarExtensionQuadraticForm_polar_eq_gram
    (K : Type*) [Field K] [CharZero K]
    (x y : Fin n → K) :
    QuadraticMap.polar (V.commutativeScalarExtensionQuadraticForm K) x y =
      2 * (Matrix.mulVec (V.specialOrthogonalMappedFormMatrix K) x ⬝ᵥ y) := by
  let A := V.specialOrthogonalMappedFormMatrix K
  have hA : A.IsSymm := by
    exact V.form_symm.map (algebraMap ℚ K)
  rw [QuadraticMap.polar]
  rw [V.commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue,
    V.commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue,
    V.commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue]
  rw [gramQuadraticValue_add A hA]
  rw [gramBilinearValue_symm A hA x y, dotProduct_comm]
  ring

/-- In the displayed finite coordinates, the Clifford quadratic reflection
is literally the standard Gram reflection matrix. -/
theorem quadraticReflection_toMatrix'_eq_gramReflectionMatrix
    (K : Type*) [Field K] [CharZero K]
    (w : Fin n → K)
    [Invertible (V.commutativeScalarExtensionQuadraticForm K w)]
    (hw : gramQuadraticValue
      (V.specialOrthogonalMappedFormMatrix K) w ≠ 0) :
    LinearMap.toMatrix'
        (CliffordAlgebra.quadraticReflection
          (V.commutativeScalarExtensionQuadraticForm K) w).toLinearMap =
      gramReflectionMatrix (V.specialOrthogonalMappedFormMatrix K) w := by
  let Q := V.commutativeScalarExtensionQuadraticForm K
  let A := V.specialOrthogonalMappedFormMatrix K
  have hQw : Q w = gramQuadraticValue A w :=
    V.commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue K w
  have hinv : ⅟(Q w) = (gramQuadraticValue A w)⁻¹ := by
    apply invOf_eq_right_inv
    rw [hQw]
    exact mul_inv_cancel₀ hw
  apply (Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K]
    ((Fin n → K) →ₗ[K] (Fin n → K))).injective
  rw [Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, gramReflectionMatrix_mulVec]
  change CliffordAlgebra.quadraticReflection Q w x = _
  rw [CliffordAlgebra.quadraticReflection_apply, hinv]
  rw [V.commutativeScalarExtensionQuadraticForm_polar_eq_gram K]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [div_eq_mul_inv]
  ring

/-- The spinor norm of the concrete matrix attached to one certified pair is
the product of the two represented square classes. -/
theorem specialOrthogonalSpinorNormHom_reflectionPairMatrixGroup
    (K : Type*) [Field K] [CharZero K]
    (pair : V.ReflectionPair K) :
    V.specialOrthogonalSpinorNormHom K
        (V.reflectionPairMatrixGroup K pair) =
      reflectionPairSquareClass
        (V.commutativeScalarExtensionQuadraticForm K) pair := by
  let Q := V.commutativeScalarExtensionQuadraticForm K
  have heval :
      eval Q (flattenPairs Q [pair]) =
        V.specialOrthogonalMatrixGroupIsometryEquiv K
          (V.reflectionPairMatrixGroup K pair) := by
    apply DFunLike.ext _ _
    intro x
    have hlin :
        (eval Q (flattenPairs Q [pair])).toLinearEquiv.toLinearMap =
          (V.specialOrthogonalMatrixGroupIsometryEquiv K
            (V.reflectionPairMatrixGroup K pair)).toLinearEquiv.toLinearMap := by
      apply (LinearMap.toMatrix' (R := K)
        (m := Fin n) (n := Fin n)).injective
      calc
        LinearMap.toMatrix'
            (eval Q (flattenPairs Q [pair])).toLinearEquiv.toLinearMap =
            (V.reflectionPairsMatrixGroup K [pair]).1.1.1 :=
          (V.reflectionPairsMatrixGroup_apply_matrix K [pair]).symm
        _ = (V.reflectionPairMatrixGroup K pair).1.1.1 := by
          simp [reflectionPairsMatrixGroup]
        _ = LinearMap.toMatrix'
            (V.specialOrthogonalMatrixGroupIsometryEquiv K
              (V.reflectionPairMatrixGroup K pair)).toLinearEquiv.toLinearMap :=
          (V.specialOrthogonalMatrixGroupIsometryEquiv_toMatrix'
            K (V.reflectionPairMatrixGroup K pair)).symm
    exact LinearMap.congr_fun hlin x
  simpa [reflectionPairSquareClassProduct] using
    V.specialOrthogonalSpinorNormHom_eq_reflectionPairSquareClassProduct
      K (V.reflectionPairMatrixGroup K pair) [pair] heval

/-- If the product of the two represented values is nonsquare, the certified
reflection pair has nontrivial spinor norm. -/
theorem specialOrthogonalSpinorNormHom_reflectionPairMatrixGroup_ne_one
    (K : Type*) [Field K] [CharZero K]
    (pair : V.ReflectionPair K)
    (hprod : ¬ IsSquare
      (V.commutativeScalarExtensionQuadraticForm K pair.1.1 *
        V.commutativeScalarExtensionQuadraticForm K pair.2.1)) :
    V.specialOrthogonalSpinorNormHom K
        (V.reflectionPairMatrixGroup K pair) ≠ 1 := by
  rw [V.specialOrthogonalSpinorNormHom_reflectionPairMatrixGroup K pair]
  apply Rat.squareClass_unit_ne_one_of_not_isSquare
  exact hprod

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- Regard integral reflection data as an anisotropic vector for the
scalar-extended rational lattice form. -/
noncomputable def LocalPadicIntegralReflectionData.anisotropicVector
    {p : ℕ} [Fact p.Prime] {L : PositiveDefiniteIntegralLattice (r + 2)}
    (d : LocalPadicIntegralReflectionData L p) :
    (L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm
      ℚ_[p]).AnisotropicVector := by
  refine ⟨fun i ↦ (d.vector i : ℚ_[p]), ?_⟩
  rw [L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue
    ℚ_[p]]
  simpa [RationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix,
    L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField] using
      d.norm_ne_zero

/-- The certified reflection pair associated to two integral reflection
data. -/
noncomputable def LocalPadicIntegralReflectionData.reflectionPair
    {p : ℕ} [Fact p.Prime] {L : PositiveDefiniteIntegralLattice (r + 2)}
    (dFirst dSecond : LocalPadicIntegralReflectionData L p) :
    L.rationalQuadraticSpaceMatrix.ReflectionPair ℚ_[p] :=
  (dFirst.anisotropicVector, dSecond.anisotropicVector)

/-- The direct integral special-orthogonal representative of the product of
two integral reflections. -/
noncomputable def LocalPadicIntegralReflectionData.specialPairDifferential
    {p : ℕ} [Fact p.Prime] {L : PositiveDefiniteIntegralLattice (r + 2)}
    (dFirst dSecond : LocalPadicIntegralReflectionData L p) :
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p :=
  L.localPadicSpecialOrthogonalDifferentialStabilizerFromHistorical p
    (dFirst.specialPairHistorical dSecond)

/-- The direct integral representative is exactly the reflection-pair matrix
used by the spinor-norm API. -/
theorem LocalPadicIntegralReflectionData.specialPairDifferential_coe
    {p : ℕ} [Fact p.Prime] {L : PositiveDefiniteIntegralLattice (r + 2)}
    (dFirst dSecond : LocalPadicIntegralReflectionData L p) :
    (dFirst.specialPairDifferential dSecond).1 =
      L.rationalQuadraticSpaceMatrix.reflectionPairMatrixGroup ℚ_[p]
        (dFirst.reflectionPair dSecond) := by
  unfold LocalPadicIntegralReflectionData.specialPairDifferential
  let V := L.rationalQuadraticSpaceMatrix
  let Q := V.commutativeScalarExtensionQuadraticForm ℚ_[p]
  let xFirst := dFirst.anisotropicVector
  let xSecond := dSecond.anisotropicVector
  letI : Invertible (Q xFirst.1) := invertibleOfNonzero xFirst.2
  letI : Invertible (Q xSecond.1) := invertibleOfNonzero xSecond.2
  apply Subtype.ext
  apply Subtype.ext
  rw [L.localPadicSpecialOrthogonalDifferentialStabilizerFromHistorical_units]
  apply Units.ext
  change
    dSecond.stabilizer.1.1.1 * dFirst.stabilizer.1.1.1 =
      (V.reflectionPairMatrixGroup ℚ_[p] (xFirst, xSecond)).1.1.1
  rw [dSecond.stabilizer_matrix_eq_gramReflectionMatrix,
    dFirst.stabilizer_matrix_eq_gramReflectionMatrix]
  have hform :
      V.specialOrthogonalMappedFormMatrix ℚ_[p] =
        L.pairingMatrix_padicField p := by
    simp [V, RationalQuadraticSpaceMatrix.specialOrthogonalMappedFormMatrix,
      L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField]
  rw [← hform]
  change
    gramReflectionMatrix (V.specialOrthogonalMappedFormMatrix ℚ_[p]) xSecond.1 *
        gramReflectionMatrix (V.specialOrthogonalMappedFormMatrix ℚ_[p]) xFirst.1 = _
  rw [← V.quadraticReflection_toMatrix'_eq_gramReflectionMatrix
      ℚ_[p] xSecond.1 dSecond.norm_ne_zero,
    ← V.quadraticReflection_toMatrix'_eq_gramReflectionMatrix
      ℚ_[p] xFirst.1 dFirst.norm_ne_zero]
  rw [← LinearMap.toMatrix'_comp]
  rw [V.reflectionPairMatrixGroup_apply_matrix]
  rfl

local instance integralSpinorRangeLowerPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The product of two original integral reflections, regarded in the
height-one integral special-orthogonal carrier used by the Spin comparison. -/
noncomputable def LocalPadicIntegralReflectionData.specialPairHeightOneIntegral
    {L : PositiveDefiniteIntegralLattice (r + 2)}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (dFirst dSecond : LocalPadicIntegralReflectionData L
      (Rat.HeightOneSpectrum.primesEquiv v).1) :
    L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  let g := dFirst.specialPairDifferential dSecond
  refine ⟨g.1, ?_⟩
  rw [L.rationalQuadraticSpaceMatrix.mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff_padic]
  exact
    (L.mem_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup_iff_integral
      p g.1).mp g.2

@[simp]
theorem LocalPadicIntegralReflectionData.specialPairHeightOneIntegral_coe
    {L : PositiveDefiniteIntegralLattice (r + 2)}
    {v : IsDedekindDomain.HeightOneSpectrum ℤ}
    (dFirst dSecond : LocalPadicIntegralReflectionData L
      (Rat.HeightOneSpectrum.primesEquiv v).1) :
    (dFirst.specialPairHeightOneIntegral dSecond).1 =
      L.rationalQuadraticSpaceMatrix.reflectionPairMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (dFirst.reflectionPair dSecond) := by
  change (dFirst.specialPairDifferential dSecond).1 = _
  exact dFirst.specialPairDifferential_coe dSecond

/-- At an odd unimodular place in rank at least two, the restricted integral
spinor norm contains a nontrivial element. -/
theorem exists_heightOnePadicSpecialOrthogonalIntegralSpinorNorm_ne_one_of_rank_add_two
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hpodd : (Rat.HeightOneSpectrum.primesEquiv v).1 ≠ 2)
    (hdet : IsUnit
      (L.pairingMatrix_padic (Rat.HeightOneSpectrum.primesEquiv v).1).det) :
    ∃ g : L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalIntegralGroup v,
      L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom
          v g ≠ 1 := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  obtain ⟨c, dOne, dNonsquare, hc, hdOne, hdNonsquare⟩ :=
    exists_integralReflectionData_square_and_nonsquare_residue
      L p hpodd hdet
  let qOne : ℤ_[p] :=
    dOne.vector ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) dOne.vector
  let qNonsquare : ℤ_[p] :=
    dNonsquare.vector ⬝ᵥ
      Matrix.mulVec (L.pairingMatrix_padic p) dNonsquare.vector
  change PadicInt.toZMod qOne = 1 at hdOne
  change PadicInt.toZMod qNonsquare = c at hdNonsquare
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hc
    exact hzero.symm ▸ IsSquare.zero
  have hqOneUnit : IsUnit qOne :=
    isUnit_of_toZMod_ne_zero (hdOne.trans_ne one_ne_zero)
  have hqNonsquareUnit : IsUnit qNonsquare :=
    isUnit_of_toZMod_ne_zero (hdNonsquare.trans_ne hc0)
  have hqProductUnit : IsUnit (qOne * qNonsquare) :=
    hqOneUnit.mul hqNonsquareUnit
  have hqProductResidue : PadicInt.toZMod (qOne * qNonsquare) = c := by
    rw [map_mul, hdOne, hdNonsquare, one_mul]
  have hqProductNonsquare : ¬ IsSquare ((qOne * qNonsquare : ℤ_[p]) : ℚ_[p]) := by
    apply not_isSquare_padic_coe_of_not_isSquare_toZMod hpodd hqProductUnit
    rw [hqProductResidue]
    exact hc
  let g := dOne.specialPairHeightOneIntegral dNonsquare
  refine ⟨g, ?_⟩
  rw [L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom_apply]
  rw [show (g.1 :
      L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) =
        L.rationalQuadraticSpaceMatrix.reflectionPairMatrixGroup ℚ_[p]
          (dOne.reflectionPair dNonsquare) by
    exact dOne.specialPairHeightOneIntegral_coe dNonsquare]
  apply L.rationalQuadraticSpaceMatrix.specialOrthogonalSpinorNormHom_reflectionPairMatrixGroup_ne_one
  have hOneValue :
      L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm
          ℚ_[p] (dOne.reflectionPair dNonsquare).1.1 = (qOne : ℚ_[p]) := by
    rw [L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue]
    change gramQuadraticValue
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))
        (fun i ↦ (dOne.vector i : ℚ_[p])) = (qOne : ℚ_[p])
    rw [L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField]
    simp [qOne, gramQuadraticValue, dotProduct, Matrix.mulVec,
      pairingMatrix_padicField]
  have hNonsquareValue :
      L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm
          ℚ_[p] (dOne.reflectionPair dNonsquare).2.1 =
        (qNonsquare : ℚ_[p]) := by
    rw [L.rationalQuadraticSpaceMatrix.commutativeScalarExtensionQuadraticForm_apply_eq_gramQuadraticValue]
    change gramQuadraticValue
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))
        (fun i ↦ (dNonsquare.vector i : ℚ_[p])) =
      (qNonsquare : ℚ_[p])
    rw [L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField]
    simp [qNonsquare, gramQuadraticValue, dotProduct, Matrix.mulVec,
      pairingMatrix_padicField]
  rw [hOneValue, hNonsquareValue]
  exact hqProductNonsquare

/-- At an admissible odd unimodular place of rank at least two, the actual
restricted integral spinor-norm range has at least two elements. -/
theorem heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_ge_two_of_rank_add_two
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hpodd : (Rat.HeightOneSpectrum.primesEquiv v.1).1 ≠ 2)
    (hdet : IsUnit
      (L.pairingMatrix_padic (Rat.HeightOneSpectrum.primesEquiv v.1).1).det) :
    2 ≤
      L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree
        v.1 := by
  let V := L.rationalQuadraticSpaceMatrix
  let h := V.heightOnePadicSpecialOrthogonalIntegralSpinorNormHom v.1
  obtain ⟨g, hg⟩ :=
    exists_heightOnePadicSpecialOrthogonalIntegralSpinorNorm_ne_one_of_rank_add_two
      L v.1 hpodd hdet
  let oneRange : h.range := ⟨1, ⟨1, map_one h⟩⟩
  let nontrivialRange : h.range := ⟨h g, ⟨g, rfl⟩⟩
  have hne : oneRange ≠ nontrivialRange := by
    intro heq
    apply hg
    exact (congrArg Subtype.val heq).symm
  let f : Bool → h.range := fun b => if b then nontrivialRange else oneRange
  have hf : Function.Injective f := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · exfalso
      exact hne (by simpa [f] using hab)
    · exfalso
      exact hne (by simpa [f] using hab.symm)
    · rfl
  letI : Finite h.range :=
    V.heightOnePadicSpecialOrthogonalIntegralSpinorNormRange_finite S v
  have hcard := Nat.card_le_card_of_injective f hf
  have hbool : Nat.card Bool = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  rw [hbool] at hcard
  change 2 ≤ Nat.card h.range
  exact hcard

end PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance integralSpinorRangeConsequencePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- For a lattice rational form, the integral matrix stored in the generic
odd-unimodular good-place certificate is the p-adic form matrix. -/
theorem cliffordSpinCandidateIntegralSpinorRangeGoodPlace_integralFormMatrix_eq
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hgood :
      L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateIntegralSpinorRangeGoodPlace
        v) :
    hgood.integralFormMatrix =
      L.pairingMatrix_padic (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  apply Matrix.ext
  intro i j
  apply PadicInt.ext
  have hij := congrFun (congrFun hgood.integralFormMatrix_map i) j
  have hL := congrFun
    (congrFun (L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField p) i) j
  exact hij.trans hL

/-- Outside the explicit rational denominator/discriminant set, the lattice
p-adic form matrix has unit determinant. -/
theorem pairingMatrix_padic_det_isUnit_of_not_mem_cliffordSpinCandidateOddUnimodularBadPlaces
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    IsUnit (L.pairingMatrix_padic
      (Rat.HeightOneSpectrum.primesEquiv v).1).det := by
  let hgood :=
    L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralSpinorRangeGoodPlace_of_not_mem_badPlaces
      (by omega : 2 ≤ r + 2) v hv
  rw [← cliffordSpinCandidateIntegralSpinorRangeGoodPlace_integralFormMatrix_eq
    L v hgood]
  exact hgood.integralFormMatrix_det_isUnit

/-- The constructive lower bound holds uniformly outside the explicit
odd-unimodular bad-place set. -/
theorem heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_ge_two_of_not_mem_badPlaces
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hv : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces) :
    2 ≤
      L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree
        v.1 := by
  let hgood :=
    L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralSpinorRangeGoodPlace_of_not_mem_badPlaces
      (by omega : 2 ≤ r + 2) v.1 hv
  apply
    heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_ge_two_of_rank_add_two
      L S v hgood.prime_ne_two
  exact
    pairingMatrix_padic_det_isUnit_of_not_mem_cliffordSpinCandidateOddUnimodularBadPlaces
      L v.1 hv

/-- The constructive nontrivial range element and the independent
unit-valuedness upper inclusion evaluate the restricted range degree as two. -/
theorem heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_eq_two_of_rank_add_two
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hpodd : (Rat.HeightOneSpectrum.primesEquiv v.1).1 ≠ 2)
    (hdet : IsUnit
      (L.pairingMatrix_padic (Rat.HeightOneSpectrum.primesEquiv v.1).1).det)
    (hunit :
      L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateIntegralSpinorNormUnitValuedAt
        v.1) :
    L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree
        v.1 = 2 := by
  apply Nat.le_antisymm
  · exact
      L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_le_two_of_unitValued
        v.1 hpodd hunit
  · exact
      heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_ge_two_of_rank_add_two
        L S v hpodd hdet

/-- With integral lifting supplied independently, the completed two-sheet
formula and the exact range degree identify the integral Spin and `SO`
differential volumes. -/
theorem heightOnePadicCliffordSpinCandidateIntegralVolume_eq_soIntegralVolume_of_rank_add_two
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hpodd : (Rat.HeightOneSpectrum.primesEquiv v.1).1 ≠ 2)
    (hdet : IsUnit
      (L.pairingMatrix_padic (Rat.HeightOneSpectrum.primesEquiv v.1).1).det)
    (hunit :
      L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateIntegralSpinorNormUnitValuedAt
        v.1)
    (hlift :
      L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateIntegralLiftingAt S v) :
    L.rationalQuadraticSpaceMatrix.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume
        v.1 =
      L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume
        v.1 := by
  apply
    L.rationalQuadraticSpaceMatrix.heightOnePadicCliffordSpinCandidateIntegralVolume_eq_soIntegralVolume_of_lifting_of_spinorRangeDegree_eq_two
      S v hlift
  exact
    heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_eq_two_of_rank_add_two
      L S v hpodd hdet hunit

/-- Outside the explicit odd-unimodular bad-place set, the remaining
unit-valuedness certificate is exactly the upper arithmetic input needed to
evaluate the restricted integral spinor range. -/
theorem
    heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_eq_two_of_not_mem_badPlaces_of_unitValued
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hv : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hunit :
      L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateIntegralSpinorNormUnitValuedAt
        v.1) :
    L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree
        v.1 = 2 := by
  apply Nat.le_antisymm
  · exact
      L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_le_two_of_unitValued
        v.1
        (L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralSpinorRangeGoodPlace_of_not_mem_badPlaces
          (by omega : 2 ≤ r + 2) v.1 hv).prime_ne_two
        hunit
  · exact
      heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_ge_two_of_not_mem_badPlaces
        L S v hv

/-- Away from the two explicit finite coordinate/arithmetic bad-place sets,
integral lifting and unit-valuedness identify the Spin and `SO` integral
differential volumes.  The unit-valuedness hypothesis is stated explicitly:
it is the integral Cartan--Dieudonne input. -/
theorem
    heightOnePadicCliffordSpinCandidateIntegralVolume_eq_soIntegralVolume_of_not_mem_badPlaces_of_unitValued
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hvRange : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvLift : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralLiftingBadPlaces)
    (hunit :
      L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateIntegralSpinorNormUnitValuedAt
        v.1) :
    L.rationalQuadraticSpaceMatrix.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume
        v.1 =
      L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume
        v.1 := by
  apply
    L.rationalQuadraticSpaceMatrix.heightOnePadicCliffordSpinCandidateIntegralVolume_eq_soIntegralVolume_of_lifting_of_spinorRangeDegree_eq_two
      S v
  · exact
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralLiftingAt_of_not_mem_badPlaces
        S v hvLift
  · exact
      heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_eq_two_of_not_mem_badPlaces_of_unitValued
        L S v hvRange hunit

end PositiveDefiniteIntegralLattice

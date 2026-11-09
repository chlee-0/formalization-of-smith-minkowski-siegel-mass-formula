import SMSFormula.RationalFiniteAdeleQuadraticGaussStandardQuotient
import SMSFormula.RationalFiniteAdeleQuadraticGaussAnnihilatorContainment
import SMSFormula.RationalAdeleRankOneWeylBruhatAnalyticReduction

/-!
# The polar-dual finite quadratic phase and its denominator periodicity

This file gives the intrinsic polar-dual finite lattice its additive subtype
and raw restricted ambient Haar.  Multiplication by the exact polar matrix
identifies this subtype algebraically with the standard integral coordinate
lattice.  The literal denominator lattice embeds into the polar dual, has its
unchanged ambient mass, and preserves the quadratic phase.

Consequently the pre-existing ambient polar-dual Gauss integral is exactly an
integral of a denominator-periodic phase on the polar-dual subtype.  The total
polar-dual covolume, the induced finite quotient sum, and quadratic Gauss
reciprocity are deliberately not evaluated here.
-/

open PositiveDefiniteIntegralLattice MeasureTheory Matrix

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

def finitePolarDualAddSubgroup (L : PositiveDefiniteIntegralLattice n) :
    AddSubgroup (Fin n → RationalFiniteAdele) where
  carrier := L.rationalQuadraticSpaceMatrix.finitePolarDualLattice
  zero_mem' := by
    change L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec 0 ∈
      integralFiniteAdeleVectors n
    rw [Matrix.mulVec_zero]
    exact fun _ ↦ integralFiniteAdeleSubring.zero_mem
  add_mem' := by
    intro x y hx hy
    change L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec (x + y) ∈
      integralFiniteAdeleVectors n
    rw [Matrix.mulVec_add]
    exact fun i ↦ integralFiniteAdeleSubring.add_mem (hx i) (hy i)
  neg_mem' := by
    intro x hx
    change L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec (-x) ∈
      integralFiniteAdeleVectors n
    rw [Matrix.mulVec_neg]
    exact fun i ↦ integralFiniteAdeleSubring.neg_mem (hx i)

abbrev FinitePolarDualAdeleVector (L : PositiveDefiniteIntegralLattice n) :=
  finitePolarDualAddSubgroup L

theorem measurableSet_finitePolarDualLattice (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSet L.rationalQuadraticSpaceMatrix.finitePolarDualLattice := by
  change MeasurableSet
    ((fun x : Fin n → RationalFiniteAdele ↦
      L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x) ⁻¹'
        integralFiniteAdeleVectors n)
  exact (measurableSet_integralFiniteAdeleVectors n).preimage (by fun_prop)

theorem measurableSet_integralFiniteAdeleCoordinateNatDilationSet
    (d m : ℕ) (hm : m ≠ 0) :
    MeasurableSet (integralFiniteAdeleCoordinateNatDilationSet d m) := by
  let divide : (Fin d → RationalFiniteAdele) →
      (Fin d → RationalFiniteAdele) := fun x i ↦
    algebraMap ℚ RationalFiniteAdele ((m : ℚ)⁻¹) * x i
  have hset :
      integralFiniteAdeleCoordinateNatDilationSet d m =
        divide ⁻¹' integralFiniteAdeleVectors d := by
    ext x
    constructor
    · intro hx i
      rcases hx i (Set.mem_univ i) with ⟨y, hy⟩
      change algebraMap ℚ RationalFiniteAdele ((m : ℚ)⁻¹) * x i ∈
        integralFiniteAdeleSubring
      rw [← hy]
      change algebraMap ℚ RationalFiniteAdele ((m : ℚ)⁻¹) *
        (m • (y : RationalFiniteAdele)) ∈ integralFiniteAdeleSubring
      rw [nsmul_eq_mul]
      rw [show (m : RationalFiniteAdele) =
        algebraMap ℚ RationalFiniteAdele (m : ℚ) by norm_num]
      rw [← mul_assoc, ← map_mul]
      convert y.property using 1
      simp [hm]
    · intro hx i _hi
      let y : IntegralFiniteAdele := ⟨divide x i, hx i⟩
      refine ⟨y, ?_⟩
      change m • divide x i = x i
      dsimp [divide]
      rw [nsmul_eq_mul]
      rw [show (m : RationalFiniteAdele) =
        algebraMap ℚ RationalFiniteAdele (m : ℚ) by norm_num]
      rw [← mul_assoc, ← map_mul]
      simp [hm]
  rw [hset]
  exact (measurableSet_integralFiniteAdeleVectors d).preimage (by fun_prop)

/-- Ambient finite Haar restricted to the intrinsic polar-dual additive
subtype.  Its nonunit total mass is deliberately not evaluated here. -/
noncomputable def finitePolarDualAddHaarMeasure (L : PositiveDefiniteIntegralLattice n) :
    Measure (FinitePolarDualAdeleVector L) :=
  Measure.comap Subtype.val
    (rationalFiniteAdeleCoordinateAddHaarMeasure n)

theorem measurePreserving_finitePolarDualCoe (L : PositiveDefiniteIntegralLattice n) :
    MeasurePreserving
      (fun x : FinitePolarDualAdeleVector L ↦
        (x : Fin n → RationalFiniteAdele))
      (finitePolarDualAddHaarMeasure L)
      ((rationalFiniteAdeleCoordinateAddHaarMeasure n).restrict
        L.rationalQuadraticSpaceMatrix.finitePolarDualLattice) := by
  refine ⟨measurable_subtype_coe, ?_⟩
  change Measure.map Subtype.val
      (Measure.comap Subtype.val
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)) = _
  exact map_comap_subtype_coe
    (measurableSet_finitePolarDualLattice L) _

private theorem finiteAdelicPolarMatrix_det_isUnit
    (V : RationalQuadraticSpaceMatrix n) :
    IsUnit V.finiteAdelicPolarMatrix.det := by
  change IsUnit
    (((algebraMap ℚ RationalFiniteAdele).mapMatrix V.polarMatrix).det)
  rw [← RingHom.map_det]
  exact IsUnit.map (algebraMap ℚ RationalFiniteAdele)
    (isUnit_iff_ne_zero.mpr V.polarMatrix_det_ne_zero)

/-- The polar matrix acts invertibly on ambient finite-adelic coordinate
vectors. -/
noncomputable def finiteAdelicPolarMatrixLinearEquiv
    (V : RationalQuadraticSpaceMatrix n) :
    (Fin n → RationalFiniteAdele) ≃ₗ[RationalFiniteAdele]
      (Fin n → RationalFiniteAdele) :=
  Matrix.toLinearEquiv' V.finiteAdelicPolarMatrix
    (Matrix.invertibleOfIsUnitDet _
      V.finiteAdelicPolarMatrix_det_isUnit)

@[simp]
theorem finiteAdelicPolarMatrixLinearEquiv_apply
    (V : RationalQuadraticSpaceMatrix n)
    (x : Fin n → RationalFiniteAdele) :
    V.finiteAdelicPolarMatrixLinearEquiv x =
      V.finiteAdelicPolarMatrix.mulVec x := by
  change Matrix.toLin' V.finiteAdelicPolarMatrix x = _
  rw [Matrix.toLin'_apply]

/-- Multiplication by the polar matrix identifies the intrinsic polar-dual
lattice with the standard integral coordinate lattice. -/
noncomputable def finitePolarDualEquivIntegralCoordinates
    (L : PositiveDefiniteIntegralLattice n) :
    FinitePolarDualAdeleVector L ≃+
      (Fin n → IntegralFiniteAdele) where
  toFun x := fun i ↦
    ⟨(L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x.1) i,
      x.2 i⟩
  invFun z :=
    let y := L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrixLinearEquiv.symm
      (fun i ↦ (z i : RationalFiniteAdele))
    ⟨y, by
      change L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec y ∈
        integralFiniteAdeleVectors n
      have h := L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrixLinearEquiv
        |>.apply_symm_apply (fun i ↦ (z i : RationalFiniteAdele))
      intro i
      rw [show
        (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec y) i =
          (z i : RationalFiniteAdele) by
        simpa only [finiteAdelicPolarMatrixLinearEquiv_apply] using congrFun h i]
      exact (z i).property⟩
  left_inv x := by
    apply Subtype.ext
    exact L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrixLinearEquiv
      |>.symm_apply_apply x.1
  right_inv z := by
    funext i
    apply Subtype.ext
    have h := L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrixLinearEquiv
      |>.apply_symm_apply (fun i ↦ (z i : RationalFiniteAdele))
    exact congrFun h i
  map_add' x y := by
    funext i
    apply Subtype.ext
    simp [Matrix.mulVec_add]

private theorem integralFiniteAdeleVector_mem_finitePolarDual
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → IntegralFiniteAdele) :
    (fun i ↦ (x i : RationalFiniteAdele)) ∈
      finitePolarDualAddSubgroup L := by
  change L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec
      (fun i ↦ (x i : RationalFiniteAdele)) ∈ integralFiniteAdeleVectors n
  rw [rationalQuadraticSpaceMatrix_finiteAdelicPolarMatrix_eq_map_polarGramMatrix L]
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem integralFiniteAdeleSubring fun j _ ↦
    integralFiniteAdeleSubring.mul_mem
      (integer_mem_integralFiniteAdeleSubring (L.polarGramMatrix i j)) (x j).property

def integralFiniteAdeleCoordinateToPolarDual (L : PositiveDefiniteIntegralLattice n) :
    (Fin n → IntegralFiniteAdele) →+ FinitePolarDualAdeleVector L where
  toFun x := ⟨fun i ↦ (x i : RationalFiniteAdele),
    integralFiniteAdeleVector_mem_finitePolarDual L x⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def integralFiniteAdeleCoordinateNatDilationToPolarDual
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) :
    (Fin n → IntegralFiniteAdele) →+ FinitePolarDualAdeleVector L :=
  (integralFiniteAdeleCoordinateToPolarDual L).comp
    (integralFiniteAdeleCoordinateNatDilation n m)

theorem integralFiniteAdeleCoordinateNatDilationToPolarDual_range_eq_preimage
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) :
    ((integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range :
        Set (FinitePolarDualAdeleVector L)) =
      (fun x : FinitePolarDualAdeleVector L ↦
        (x : Fin n → RationalFiniteAdele)) ⁻¹'
          integralFiniteAdeleCoordinateNatDilationSet n m := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ i _hi
    exact ⟨y i, rfl⟩
  · intro hx
    choose y hy using fun i ↦ hx i (Set.mem_univ i)
    refine ⟨y, ?_⟩
    apply Subtype.ext
    funext i
    exact hy i

theorem measurableSet_integralFiniteAdeleCoordinateNatDilationToPolarDual_range
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) (hm : m ≠ 0) :
    MeasurableSet
      ((integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range :
        Set (FinitePolarDualAdeleVector L)) := by
  rw [integralFiniteAdeleCoordinateNatDilationToPolarDual_range_eq_preimage]
  exact (measurableSet_integralFiniteAdeleCoordinateNatDilationSet n m hm).preimage
    measurable_subtype_coe

private theorem subtype_image_integralFiniteAdeleCoordinateNatDilationToPolarDual_range
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) :
    (fun x : FinitePolarDualAdeleVector L ↦
      (x : Fin n → RationalFiniteAdele)) ''
        ((integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range :
          Set (FinitePolarDualAdeleVector L)) =
      integralFiniteAdeleCoordinateNatDilationSet n m := by
  ext x
  constructor
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩ i _hi
    exact ⟨y i, rfl⟩
  · intro hx
    choose y hy using fun i ↦ hx i (Set.mem_univ i)
    let z : FinitePolarDualAdeleVector L :=
      integralFiniteAdeleCoordinateNatDilationToPolarDual L m y
    refine ⟨z, ⟨y, rfl⟩, ?_⟩
    funext i
    exact hy i

/-- Every denominator coset inside the raw polar-dual Haar has the literal
ambient mass `(m⁻¹)^n`.  No total polar-dual covolume is evaluated. -/
theorem finitePolarDualAddHaarMeasure_denDilation_range
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) (hm : m ≠ 0) :
    finitePolarDualAddHaarMeasure L
        ((integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range :
          Set (FinitePolarDualAdeleVector L)) =
      ((m : ENNReal)⁻¹) ^ n := by
  let hval : MeasurableEmbedding
      (fun x : FinitePolarDualAdeleVector L ↦
        (x : Fin n → RationalFiniteAdele)) :=
    MeasurableEmbedding.subtype_coe
      (measurableSet_finitePolarDualLattice L)
  change (Measure.comap Subtype.val
      (rationalFiniteAdeleCoordinateAddHaarMeasure n))
        ((integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range :
          Set (FinitePolarDualAdeleVector L)) = _
  rw [hval.comap_apply]
  rw [subtype_image_integralFiniteAdeleCoordinateNatDilationToPolarDual_range]
  exact rationalFiniteAdeleCoordinateAddHaarMeasure_natDilationSet n m hm

/-- The integral polar matrix on standard integral finite-adelic coordinates. -/
def integralFiniteAdelePolarMatrixEnd (L : PositiveDefiniteIntegralLattice n) :
    (Fin n → IntegralFiniteAdele) →+ (Fin n → IntegralFiniteAdele) where
  toFun x := fun i ↦
    ⟨(L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec
      (fun j ↦ (x j : RationalFiniteAdele))) i,
      (integralFiniteAdeleVector_mem_finitePolarDual L x) i⟩
  map_zero' := by
    funext i
    apply Subtype.ext
    change
      (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec
        (0 : Fin n → RationalFiniteAdele)) i = 0
    rw [Matrix.mulVec_zero]
    rfl
  map_add' x y := by
    funext i
    apply Subtype.ext
    change
      (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec
        ((fun j ↦ (x j : RationalFiniteAdele)) +
          (fun j ↦ (y j : RationalFiniteAdele)))) i =
        (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec
          (fun j ↦ (x j : RationalFiniteAdele))) i +
        (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec
          (fun j ↦ (y j : RationalFiniteAdele))) i
    rw [Matrix.mulVec_add]
    rfl

@[simp]
theorem finitePolarDualEquivIntegralCoordinates_integral_apply
    (L : PositiveDefiniteIntegralLattice n) (x : Fin n → IntegralFiniteAdele) :
    finitePolarDualEquivIntegralCoordinates L
        (integralFiniteAdeleCoordinateToPolarDual L x) =
      integralFiniteAdelePolarMatrixEnd L x :=
  rfl

theorem finitePolarDualEquivIntegralCoordinates_map_denDilation_range
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) :
    (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range.map
        (finitePolarDualEquivIntegralCoordinates L).toAddMonoidHom =
      ((integralFiniteAdelePolarMatrixEnd L).comp
        (integralFiniteAdeleCoordinateNatDilation n m)).range := by
  ext z
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨integralFiniteAdeleCoordinateNatDilationToPolarDual L m x,
      ⟨x, rfl⟩, rfl⟩

def rationalFiniteAdelePolarDualQuadraticPhase
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ)
    (x : FinitePolarDualAdeleVector L) : ℂ :=
  (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x.1 : ℂ)

private theorem finiteAdelicPolarPairing_mem_integral_of_mem_dual
    (L : PositiveDefiniteIntegralLattice n)
    (x : Fin n → RationalFiniteAdele)
    (y : Fin n → RationalFiniteAdele)
    (hx : x ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice)
    (hy : y ∈ integralFiniteAdeleVectors n) :
    dotProduct x
        (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec y) ∈
      integralFiniteAdeleSubring := by
  have hsymm := L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix_isSymm
  have heq :
      dotProduct x
          (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec y) =
        dotProduct
          (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec x) y := by
    rw [Matrix.dotProduct_mulVec]
    rw [← Matrix.mulVec_transpose]
    rw [hsymm]
  rw [heq]
  exact Subring.sum_mem integralFiniteAdeleSubring fun i _ ↦
    integralFiniteAdeleSubring.mul_mem (hx i) (hy i)

private theorem finiteAdelicQuadraticFormValue_nsmul'
    (V : RationalQuadraticSpaceMatrix n) (m : ℕ)
    (x : Fin n → RationalFiniteAdele) :
    V.finiteAdelicQuadraticFormValue (m • x) =
      (m : RationalFiniteAdele) ^ 2 * V.finiteAdelicQuadraticFormValue x := by
  simp only [finiteAdelicQuadraticFormValue, Matrix.mulVec, dotProduct,
    Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  ring_nf

private theorem rational_den_coefficient_mem_integral'
    (t : ℚ) :
    algebraMap ℚ RationalFiniteAdele t * (t.den : RationalFiniteAdele) ∈
      integralFiniteAdeleSubring := by
  have hcoeff :
      algebraMap ℚ RationalFiniteAdele t * (t.den : RationalFiniteAdele) =
        algebraMap ℚ RationalFiniteAdele (t.num : ℚ) := by
    rw [show (t.den : RationalFiniteAdele) =
      algebraMap ℚ RationalFiniteAdele (t.den : ℚ) by norm_num]
    rw [← map_mul, Rat.mul_den_eq_num]
  rw [hcoeff]
  exact integer_mem_integralFiniteAdeleSubring t.num

private theorem rational_den_sq_coefficient_mem_integral'
    (t : ℚ) :
    algebraMap ℚ RationalFiniteAdele t * (t.den : RationalFiniteAdele) ^ 2 ∈
      integralFiniteAdeleSubring := by
  rw [pow_two, ← mul_assoc]
  exact integralFiniteAdeleSubring.mul_mem
    (rational_den_coefficient_mem_integral' t)
    (by
      exact_mod_cast
        integer_mem_integralFiniteAdeleSubring (t.den : ℤ))

private theorem dotProduct_scaledFiniteAdelicPolarFrequency_nsmul'
    (V : RationalQuadraticSpaceMatrix n) (t : ℚ) (m : ℕ)
    (x y : Fin n → RationalFiniteAdele) :
    dotProduct x (V.scaledFiniteAdelicPolarFrequency t (m • y)) =
      (algebraMap ℚ RationalFiniteAdele t * (m : RationalFiniteAdele)) *
        dotProduct x (V.finiteAdelicPolarMatrix.mulVec y) := by
  simp only [scaledFiniteAdelicPolarFrequency, Matrix.mulVec, dotProduct,
    Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

theorem rationalFiniteAdelePolarDualQuadraticPhase_add_denDilation
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ)
    (x z : FinitePolarDualAdeleVector L)
    (hz : z ∈
      (integralFiniteAdeleCoordinateNatDilationToPolarDual L t.den).range) :
    rationalFiniteAdelePolarDualQuadraticPhase L t (x + z) =
      rationalFiniteAdelePolarDualQuadraticPhase L t x := by
  rcases hz with ⟨w, rfl⟩
  let xa : Fin n → RationalFiniteAdele := x.1
  let wa : Fin n → RationalFiniteAdele := fun i ↦ w i
  have hxa : xa ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice := x.2
  have hwa : wa ∈ integralFiniteAdeleVectors n := fun i ↦ (w i).property
  have harg :
      ((x + integralFiniteAdeleCoordinateNatDilationToPolarDual L t.den w :
          FinitePolarDualAdeleVector L) : Fin n → RationalFiniteAdele) =
        xa + t.den • wa := by
    rfl
  unfold rationalFiniteAdelePolarDualQuadraticPhase
  rw [harg]
  rw [L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase_add]
  have hq :
      L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue wa ∈
        integralFiniteAdeleSubring := by
    simpa [finiteAdelicQuadraticFormValue] using
      L.finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring
        wa wa hwa hwa
  have hphase :
      L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t
          (t.den • wa) = 1 := by
    unfold rationalFiniteAdeleQuadraticPhase
    apply rationalFiniteAdeleFourierChar_eq_one_of_mem_integral
    rw [finiteAdelicQuadraticFormValue_nsmul']
    simpa [mul_assoc] using integralFiniteAdeleSubring.mul_mem
      (rational_den_sq_coefficient_mem_integral' t) hq
  have hpair :
      rationalFiniteAdeleVectorPairingChar xa
        (L.rationalQuadraticSpaceMatrix.scaledFiniteAdelicPolarFrequency t
          (t.den • wa)) = 1 := by
    unfold rationalFiniteAdeleVectorPairingChar
    apply rationalFiniteAdeleFourierChar_eq_one_of_mem_integral
    rw [dotProduct_scaledFiniteAdelicPolarFrequency_nsmul']
    exact integralFiniteAdeleSubring.mul_mem
      (rational_den_coefficient_mem_integral' t)
      (finiteAdelicPolarPairing_mem_integral_of_mem_dual L xa wa hxa hwa)
  rw [hphase, hpair]
  simp [xa]

theorem rationalFiniteAdeleQuadraticPhase_mul_polarDualIndicator_eq_indicator
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    (fun x : Fin n → RationalFiniteAdele ↦
      (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) *
        L.rationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator x) =
      L.rationalQuadraticSpaceMatrix.finitePolarDualLattice.indicator fun x ↦
        (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t x : ℂ) := by
  funext x
  by_cases hx : x ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice
  · rw [finitePolarDualLatticeIndicator_of_mem _ hx]
    simp [hx]
  · rw [finitePolarDualLatticeIndicator_of_not_mem _ hx]
    simp [hx]

/-- The ambient polar-dual Gauss integral is exactly the quadratic phase
integral on the intrinsic polar-dual additive subtype.  The subtype Haar is
still the raw ambient restriction and is not probability normalized. -/
theorem rationalFiniteAdeleDualQuadraticGaussIntegral_eq_polarDualQuadraticPhase
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral t =
      ∫ x : FinitePolarDualAdeleVector L,
        rationalFiniteAdelePolarDualQuadraticPhase L t x
        ∂finitePolarDualAddHaarMeasure L := by
  unfold rationalFiniteAdeleDualQuadraticGaussIntegral
  rw [rationalFiniteAdeleQuadraticPhase_mul_polarDualIndicator_eq_indicator L t]
  rw [integral_indicator (measurableSet_finitePolarDualLattice L)]
  have hcontinuous : Continuous
      (L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticPhase t) := by
    unfold rationalFiniteAdeleQuadraticPhase finiteAdelicQuadraticFormValue
    apply continuous_rationalFiniteAdeleFourierChar.comp
    fun_prop
  rw [← (measurePreserving_finitePolarDualCoe L).map_eq]
  rw [integral_map
    (measurePreserving_finitePolarDualCoe L).aemeasurable
    hcontinuous.subtype_val.aestronglyMeasurable]
  rfl

end RationalQuadraticSpaceMatrix

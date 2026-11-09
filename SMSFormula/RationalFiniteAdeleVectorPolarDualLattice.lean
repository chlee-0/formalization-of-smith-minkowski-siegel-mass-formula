import SMSFormula.RationalAdeleVectorPolarPairing

/-!
# The finite polar-dual coordinate lattice

For the exact polar matrix `C = 2F`, this file identifies the annihilator of
the standard finite coordinate lattice without choosing a matrix inverse or a
representative.  The polar-dual lattice is defined intrinsically as the
preimage of `Zhat^n` under `C`; the scalar finite-character kernel theorem then
proves that this preimage is exactly the character annihilator.

The only Fourier integral used is the elementary finite product of the
already certified scalar indicator calculation. No determinant
normalization, Gaussian, shell decomposition, or Tamagawa-number assertion is
made here.
-/

noncomputable section

open Matrix
open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped BigOperators FourierTransform

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Diagonal scalar extension of the exact polar matrix to the finite adeles. -/
def finiteAdelicPolarMatrix (V : RationalQuadraticSpaceMatrix n) :
    Matrix (Fin n) (Fin n) RationalFiniteAdele :=
  V.polarMatrix.map (algebraMap ℚ RationalFiniteAdele)

theorem finiteAdelicPolarMatrix_isSymm
    (V : RationalQuadraticSpaceMatrix n) :
    V.finiteAdelicPolarMatrix.IsSymm :=
  V.polarMatrix_isSymm.map _

/-- The standard finite coordinate pairing attached to the fixed additive
character. -/
def rationalFiniteAdeleVectorPairingChar
    (x y : Fin n → RationalFiniteAdele) : Circle :=
  rationalFiniteAdeleFourierChar (dotProduct x y)

/-- Product of the fixed finite additive character over a finite coordinate
space. -/
noncomputable def rationalFiniteAdeleCoordinateFourierChar (d : ℕ) :
    AddChar (Fin d → RationalFiniteAdele) Circle where
  toFun x := ∏ i, rationalFiniteAdeleFourierChar (x i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Pi.add_apply, AddChar.map_add_eq_mul]
    exact Finset.prod_mul_distrib

@[simp]
theorem rationalFiniteAdeleCoordinateFourierChar_apply
    (d : ℕ) (x : Fin d → RationalFiniteAdele) :
    rationalFiniteAdeleCoordinateFourierChar d x =
      ∏ i, rationalFiniteAdeleFourierChar (x i) :=
  rfl

/-- The product coordinate character on a pointwise product is the scalar
character of the coordinate dot product. -/
theorem rationalFiniteAdeleCoordinateFourierChar_mul_eq_dotProduct
    (x y : Fin n → RationalFiniteAdele) :
    rationalFiniteAdeleCoordinateFourierChar n (x * y) =
      rationalFiniteAdeleVectorPairingChar x y := by
  simp only [rationalFiniteAdeleCoordinateFourierChar_apply, Pi.mul_apply,
    rationalFiniteAdeleVectorPairingChar, dotProduct]
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha,
        AddChar.map_add_eq_mul, ih]

/-- The standard coordinate lattice is its own annihilator for the
componentwise finite pairing. -/
theorem rationalFiniteAdeleVector_integral_annihilator_iff
    (y : Fin n → RationalFiniteAdele) :
    (∀ x : Fin n → RationalFiniteAdele,
      x ∈ integralFiniteAdeleVectors n →
        rationalFiniteAdeleVectorPairingChar x y = 1) ↔
      y ∈ integralFiniteAdeleVectors n := by
  classical
  constructor
  · intro h i
    rw [← rationalFiniteAdele_integral_annihilator_iff (y i)]
    intro a ha
    let x : Fin n → RationalFiniteAdele := Pi.single i a
    have hx : x ∈ integralFiniteAdeleVectors n := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [x] using ha
      · simp [x, hji, integralFiniteAdeleSubring.zero_mem]
    have hxy := h x hx
    simpa [rationalFiniteAdeleVectorPairingChar, x, dotProduct,
      Pi.single_apply] using hxy
  · intro hy x hx
    apply rationalFiniteAdeleFourierChar_eq_one_of_mem_integral
    rw [dotProduct]
    exact Subring.sum_mem integralFiniteAdeleSubring fun i _ ↦
      integralFiniteAdeleSubring.mul_mem (hx i) (hy i)

/-- The finite `C`-dual of the standard coordinate lattice, defined without
choosing `C⁻¹`: it is the preimage of `Zhat^n` under the polar matrix. -/
def finitePolarDualLattice (V : RationalQuadraticSpaceMatrix n) :
    Set (Fin n → RationalFiniteAdele) :=
  {y | V.finiteAdelicPolarMatrix.mulVec y ∈ integralFiniteAdeleVectors n}

@[simp]
theorem mem_finitePolarDualLattice_iff
    (V : RationalQuadraticSpaceMatrix n)
    (y : Fin n → RationalFiniteAdele) :
    y ∈ V.finitePolarDualLattice ↔
      V.finiteAdelicPolarMatrix.mulVec y ∈
        integralFiniteAdeleVectors n :=
  Iff.rfl

/-- The finite polar kernel. -/
def rationalFiniteAdeleVectorPolarChar
    (V : RationalQuadraticSpaceMatrix n)
    (x y : Fin n → RationalFiniteAdele) : Circle :=
  rationalFiniteAdeleVectorPairingChar x
    (V.finiteAdelicPolarMatrix.mulVec y)

/-- The annihilator of the standard finite coordinate lattice under the exact
polar kernel is precisely its intrinsic `C`-dual lattice. -/
theorem rationalFiniteAdeleVector_polar_annihilator_iff
    (V : RationalQuadraticSpaceMatrix n)
    (y : Fin n → RationalFiniteAdele) :
    (∀ x : Fin n → RationalFiniteAdele,
      x ∈ integralFiniteAdeleVectors n →
        V.rationalFiniteAdeleVectorPolarChar x y = 1) ↔
      y ∈ V.finitePolarDualLattice := by
  exact rationalFiniteAdeleVector_integral_annihilator_iff
    (V.finiteAdelicPolarMatrix.mulVec y)

/-! ## The finite standard-lattice Fourier integral -/

/-- Literal finite product of the fixed scalar finite-adelic Haar measure. -/
noncomputable def rationalFiniteAdeleCoordinateAddHaarMeasure (d : ℕ) :
    Measure (Fin d → RationalFiniteAdele) :=
  Measure.pi (fun _ : Fin d ↦ rationalFiniteAdeleAddHaarMeasure)

/-- Product indicator of the standard finite coordinate lattice. -/
def rationalFiniteAdeleVectorIntegralIndicator
    (x : Fin n → RationalFiniteAdele) : ℂ :=
  ∏ i, rationalFiniteAdeleIntegralIndicator (x i)

@[simp]
theorem rationalFiniteAdeleVectorIntegralIndicator_of_mem
    {x : Fin n → RationalFiniteAdele}
    (hx : x ∈ integralFiniteAdeleVectors n) :
    rationalFiniteAdeleVectorIntegralIndicator x = 1 := by
  apply Finset.prod_eq_one
  intro i _hi
  exact rationalFiniteAdeleIntegralIndicator_of_mem (hx i)

@[simp]
theorem rationalFiniteAdeleVectorIntegralIndicator_of_not_mem
    {x : Fin n → RationalFiniteAdele}
    (hx : x ∉ integralFiniteAdeleVectors n) :
    rationalFiniteAdeleVectorIntegralIndicator x = 0 := by
  classical
  change ¬ ∀ i, x i ∈ integralFiniteAdeleSubring at hx
  obtain ⟨i, hi⟩ := not_forall.mp hx
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact rationalFiniteAdeleIntegralIndicator_of_not_mem hi

/-- The standard finite coordinate indicator is fixed by the actual product
Fourier integral. -/
@[simp]
theorem rationalFiniteAdeleCoordinate_fourierIntegral_integralIndicator
    (d : ℕ) (w : Fin d → RationalFiniteAdele) :
    Fourier.fourierIntegral (rationalFiniteAdeleCoordinateFourierChar d)
        (rationalFiniteAdeleCoordinateAddHaarMeasure d)
        rationalFiniteAdeleVectorIntegralIndicator w =
      rationalFiniteAdeleVectorIntegralIndicator w := by
  rw [Fourier.fourierIntegral_def]
  have hintegrand :
      (fun v : Fin d → RationalFiniteAdele ↦
        rationalFiniteAdeleCoordinateFourierChar d (-(v * w)) •
          rationalFiniteAdeleVectorIntegralIndicator v) =
      (fun v : Fin d → RationalFiniteAdele ↦
        ∏ i, rationalFiniteAdeleFourierChar (-(v i * w i)) •
          rationalFiniteAdeleIntegralIndicator (v i)) := by
    funext v
    simp only [rationalFiniteAdeleCoordinateFourierChar_apply,
      rationalFiniteAdeleVectorIntegralIndicator, Pi.neg_apply, Pi.mul_apply,
      Circle.smul_def, smul_eq_mul]
    change Circle.coeHom
        (∏ i, rationalFiniteAdeleFourierChar (-(v i * w i))) *
          ∏ i, rationalFiniteAdeleIntegralIndicator (v i) = _
    rw [map_prod]
    change (∏ i, (rationalFiniteAdeleFourierChar (-(v i * w i)) : ℂ)) *
        ∏ i, rationalFiniteAdeleIntegralIndicator (v i) = _
    rw [Finset.prod_mul_distrib]
  rw [hintegrand, rationalFiniteAdeleCoordinateAddHaarMeasure]
  calc
    (∫ v : Fin d → RationalFiniteAdele,
        ∏ i, rationalFiniteAdeleFourierChar (-(v i * w i)) •
          rationalFiniteAdeleIntegralIndicator (v i)
        ∂Measure.pi (fun _ : Fin d ↦ rationalFiniteAdeleAddHaarMeasure)) =
      ∏ i, ∫ v : RationalFiniteAdele,
        rationalFiniteAdeleFourierChar (-(v * w i)) •
          rationalFiniteAdeleIntegralIndicator v
        ∂rationalFiniteAdeleAddHaarMeasure :=
      integral_fintype_prod_eq_prod
        (μ := fun _ : Fin d ↦ rationalFiniteAdeleAddHaarMeasure)
        (fun i (v : RationalFiniteAdele) ↦
          rationalFiniteAdeleFourierChar (-(v * w i)) •
            rationalFiniteAdeleIntegralIndicator v)
    _ = rationalFiniteAdeleVectorIntegralIndicator w := by
      simp only [← Fourier.fourierIntegral_def,
        rationalFiniteAdele_fourierIntegral_integralIndicator,
        rationalFiniteAdeleVectorIntegralIndicator]

/-- Indicator of the intrinsic finite polar-dual lattice. -/
def finitePolarDualLatticeIndicator
    (V : RationalQuadraticSpaceMatrix n)
    (y : Fin n → RationalFiniteAdele) : ℂ :=
  rationalFiniteAdeleVectorIntegralIndicator
    (V.finiteAdelicPolarMatrix.mulVec y)

@[simp]
theorem finitePolarDualLatticeIndicator_of_mem
    (V : RationalQuadraticSpaceMatrix n)
    {y : Fin n → RationalFiniteAdele}
    (hy : y ∈ V.finitePolarDualLattice) :
    V.finitePolarDualLatticeIndicator y = 1 :=
  rationalFiniteAdeleVectorIntegralIndicator_of_mem hy

@[simp]
theorem finitePolarDualLatticeIndicator_of_not_mem
    (V : RationalQuadraticSpaceMatrix n)
    {y : Fin n → RationalFiniteAdele}
    (hy : y ∉ V.finitePolarDualLattice) :
    V.finitePolarDualLatticeIndicator y = 0 :=
  rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hy

/-- For the exact polar kernel, the Fourier integral of the standard lattice
indicator is the indicator of the intrinsic `C`-dual lattice.  The frequency
is changed by `C`; no Haar measure is rescaled in this statement. -/
theorem rationalFiniteAdeleVectorPolar_fourierIntegral_integralIndicator
    (V : RationalQuadraticSpaceMatrix n)
    (y : Fin n → RationalFiniteAdele) :
    Fourier.fourierIntegral (rationalFiniteAdeleCoordinateFourierChar n)
        (rationalFiniteAdeleCoordinateAddHaarMeasure n)
        rationalFiniteAdeleVectorIntegralIndicator
        (V.finiteAdelicPolarMatrix.mulVec y) =
      V.finitePolarDualLatticeIndicator y := by
  rw [rationalFiniteAdeleCoordinate_fourierIntegral_integralIndicator]
  rfl

end RationalQuadraticSpaceMatrix

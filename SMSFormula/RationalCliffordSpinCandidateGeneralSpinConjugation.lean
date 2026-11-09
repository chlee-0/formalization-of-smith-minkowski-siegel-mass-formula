import SMSFormula.RationalCliffordGeneralSpinVerticalEquivalence
import SMSFormula.RationalCliffordSpinCandidateAdelicLeftQuotientTopology

/-!
# Conjugation of represented Spin by intrinsic general Spin

The represented Spin subgroup is the similitude kernel inside the
intrinsic general-Spin group.  This file uses that exactness, rather than a
chosen local product presentation, to construct conjugation by an arbitrary
general-Spin point as an automorphism of represented Spin.  The construction
is compatible with scalar extension and is continuous in the Spin variable.

For a rational general-Spin point the automorphism preserves the rational
diagonal and hence descends to the rational adelic Spin left quotient.  No
measure-preservation statement is made here; that needs the global
differential normalization for the vertical comparison.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Conjugation by an intrinsic general-Spin point, lifted uniquely from the
literal similitude kernel to the represented Spin carrier. -/
def cliffordSpinCandidateGeneralSpinConjugation
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : V.CliffordGeneralSpinIntrinsicPoint A)
    (x : V.CliffordSpinCandidateGroup A) :
    V.CliffordSpinCandidateGroup A :=
  Classical.choose (by
    have hker : g⁻¹ * V.cliffordSpinCandidateToCliffordGeneralSpinHom A x * g ∈
        (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V A).ker := by
      change
        CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V A
            (g⁻¹ * V.cliffordSpinCandidateToCliffordGeneralSpinHom A x * g) = 1
      rw [map_mul, map_mul, map_inv,
        show CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V A
            (V.cliffordSpinCandidateToCliffordGeneralSpinHom A x) = 1 by
          exact V.cliffordSpinCandidateToCliffordGeneralSpinHom_apply_similitude A x]
      simp
    rw [← V.range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker A] at hker
    exact hker)

/-- The chosen Spin conjugate has the required literal image in intrinsic
general Spin. -/
@[simp]
theorem cliffordSpinCandidateToCliffordGeneralSpinHom_conjugation
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : V.CliffordGeneralSpinIntrinsicPoint A)
    (x : V.CliffordSpinCandidateGroup A) :
    V.cliffordSpinCandidateToCliffordGeneralSpinHom A
        (V.cliffordSpinCandidateGeneralSpinConjugation A g x) =
      g⁻¹ * V.cliffordSpinCandidateToCliffordGeneralSpinHom A x * g :=
  Classical.choose_spec (by
    have hker : g⁻¹ * V.cliffordSpinCandidateToCliffordGeneralSpinHom A x * g ∈
        (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V A).ker := by
      change
        CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V A
            (g⁻¹ * V.cliffordSpinCandidateToCliffordGeneralSpinHom A x * g) = 1
      rw [map_mul, map_mul, map_inv,
        show CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V A
            (V.cliffordSpinCandidateToCliffordGeneralSpinHom A x) = 1 by
          exact V.cliffordSpinCandidateToCliffordGeneralSpinHom_apply_similitude A x]
      simp
    rw [← V.range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker A] at hker
    exact hker)

/-- Conjugation by a general-Spin point is an automorphism of the represented
Spin group. -/
def cliffordSpinCandidateGeneralSpinConjugationMulEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : V.CliffordGeneralSpinIntrinsicPoint A) :
    V.CliffordSpinCandidateGroup A ≃* V.CliffordSpinCandidateGroup A where
  toFun := V.cliffordSpinCandidateGeneralSpinConjugation A g
  invFun := V.cliffordSpinCandidateGeneralSpinConjugation A g⁻¹
  left_inv x := by
    apply V.cliffordSpinCandidateToCliffordGeneralSpinHom_injective A
    simp [mul_assoc]
  right_inv x := by
    apply V.cliffordSpinCandidateToCliffordGeneralSpinHom_injective A
    simp [mul_assoc]
  map_mul' x y := by
    apply V.cliffordSpinCandidateToCliffordGeneralSpinHom_injective A
    simp [mul_assoc]

@[simp]
theorem cliffordSpinCandidateGeneralSpinConjugationMulEquiv_apply
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : V.CliffordGeneralSpinIntrinsicPoint A)
    (x : V.CliffordSpinCandidateGroup A) :
    V.cliffordSpinCandidateGeneralSpinConjugationMulEquiv A g x =
      V.cliffordSpinCandidateGeneralSpinConjugation A g x :=
  rfl

/-- Conjugation commutes with coefficientwise scalar extension. -/
theorem cliffordSpinCandidateGeneralSpinConjugation_naturality
    (A B : Type*) [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B)
    (g : V.CliffordGeneralSpinIntrinsicPoint A)
    (x : V.CliffordSpinCandidateGroup A) :
    V.cliffordSpinCandidateGroupMap f
        (V.cliffordSpinCandidateGeneralSpinConjugation A g x) =
      V.cliffordSpinCandidateGeneralSpinConjugation B
        (CliffordGeneralSpinIntrinsicPoint.mapGroupHom V f g)
        (V.cliffordSpinCandidateGroupMap f x) := by
  apply V.cliffordSpinCandidateToCliffordGeneralSpinHom_injective B
  rw [← V.cliffordSpinCandidateToCliffordGeneralSpinHom_naturality A f]
  simp only [V.cliffordSpinCandidateToCliffordGeneralSpinHom_conjugation]
  rw [map_mul, map_mul, map_inv,
    V.cliffordSpinCandidateToCliffordGeneralSpinHom_naturality A f]

/-- For a fixed general-Spin origin, conjugation is continuous on the
finite-coordinate represented Spin carrier. -/
theorem continuous_cliffordSpinCandidateGeneralSpinConjugation
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (g : V.CliffordGeneralSpinIntrinsicPoint A) :
    Continuous (V.cliffordSpinCandidateGeneralSpinConjugation A g) := by
  apply continuous_induced_rng.mpr
  have hambient : Continuous
      (fun x : V.CliffordSpinCandidateGroup A =>
        g⁻¹ * V.cliffordSpinCandidateToCliffordGeneralSpinHom A x * g) :=
    continuous_const.mul
      (V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom A) |>.mul
        continuous_const
  apply Continuous.prodMk
  · apply continuous_pi
    intro s
    have h := V.continuous_cliffordGeneralSpinCliffordCoordinate A s |>.comp hambient
    convert h using 1
    funext x
    rw [Function.comp_apply]
    rw [← V.cliffordSpinCandidateElementOfCoordinateAlgHom_repr A
      (V.cliffordSpinCandidateGeneralSpinConjugation A g x) s]
    change
      (V.cliffordCoordinateBaseChangeBasis A).repr
          ((V.cliffordSpinCandidateToCliffordGeneralSpinHom A
            (V.cliffordSpinCandidateGeneralSpinConjugation A g x)).cliffordUnit :
              V.cliffordCoordinateBaseChangeAlgebra A) s = _
    rw [V.cliffordSpinCandidateToCliffordGeneralSpinHom_conjugation]
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have h := V.continuous_cliffordGeneralSpinMatrixCoordinate A i j |>.comp hambient
    convert h using 1
    funext x
    rw [Function.comp_apply]
    rw [← V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply A
      (V.cliffordSpinCandidateGeneralSpinConjugation A g x) i j]
    change
      (V.cliffordSpinCandidateToCliffordGeneralSpinHom A
        (V.cliffordSpinCandidateGeneralSpinConjugation A g x)).matrixPoint.1 i j = _
    rw [V.cliffordSpinCandidateToCliffordGeneralSpinHom_conjugation]

/-- The conjugation automorphism as a continuous multiplicative equivalence.
-/
def cliffordSpinCandidateGeneralSpinConjugationContinuousMulEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (g : V.CliffordGeneralSpinIntrinsicPoint A) :
    V.CliffordSpinCandidateGroup A ≃ₜ* V.CliffordSpinCandidateGroup A where
  toMulEquiv := V.cliffordSpinCandidateGeneralSpinConjugationMulEquiv A g
  continuous_toFun := V.continuous_cliffordSpinCandidateGeneralSpinConjugation A g
  continuous_invFun :=
    V.continuous_cliffordSpinCandidateGeneralSpinConjugation A g⁻¹

/-! ## Rational conjugation on the full adelic Spin quotient -/

/-- Scalar extension of a rational conjugate is the conjugate by the rational
full-adelic diagonal point. -/
theorem rational_fullAdelic_diagonal_generalSpinConjugation
    (gamma : V.RationalCliffordGeneralSpinGroup)
    (x : V.RationalCliffordSpinCandidateGroup) :
    V.rationalCliffordSpinCandidateFullAdelicDiagonalHom
        (V.cliffordSpinCandidateGeneralSpinConjugation ℚ gamma x) =
      V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
        (V.rationalCliffordSpinCandidateFullAdelicDiagonalHom x) := by
  exact V.cliffordSpinCandidateGeneralSpinConjugation_naturality
    ℚ RationalAdele (Algebra.ofId ℚ RationalAdele) gamma x

/-- Conjugation by a rational general-Spin point on the rational adelic Spin
left quotient. -/
def fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
    (gamma : V.RationalCliffordGeneralSpinGroup) :
    V.FullAdelicCliffordSpinCandidateLeftQuotient →
      V.FullAdelicCliffordSpinCandidateLeftQuotient :=
  Quot.lift
    (fun x => V.fullAdelicCliffordSpinCandidateLeftQuotientMap
      (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) x)) (by
      intro x y hxy
      rcases hxy with ⟨delta, rfl⟩
      rcases delta.2 with ⟨d, hd⟩
      have hdelta :
          (delta : V.FullAdelicCliffordSpinCandidateGroup) =
            V.rationalCliffordSpinCandidateFullAdelicDiagonalHom d := hd.symm
      change
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap
            (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
              (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) x) =
          V.fullAdelicCliffordSpinCandidateLeftQuotientMap
            (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
              (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
              ((delta : V.FullAdelicCliffordSpinCandidateGroup) * x))
      have hmul :=
        (V.cliffordSpinCandidateGeneralSpinConjugationMulEquiv RationalAdele
          (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)).map_mul
            (delta : V.FullAdelicCliffordSpinCandidateGroup) x
      change V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
          (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
            ((delta : V.FullAdelicCliffordSpinCandidateGroup) * x) =
        V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
            (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) delta *
          V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
            (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) x at hmul
      rw [hmul, hdelta,
        ← V.rational_fullAdelic_diagonal_generalSpinConjugation]
      exact (leftCosetMap_gamma_mul
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
        ⟨V.rationalCliffordSpinCandidateFullAdelicDiagonalHom
            (V.cliffordSpinCandidateGeneralSpinConjugation ℚ gamma d),
          ⟨V.cliffordSpinCandidateGeneralSpinConjugation ℚ gamma d, rfl⟩⟩
        (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
          (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) x)).symm)

@[simp]
theorem fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation_mk
    (gamma : V.RationalCliffordGeneralSpinGroup)
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation gamma
        (V.fullAdelicCliffordSpinCandidateLeftQuotientMap x) =
      V.fullAdelicCliffordSpinCandidateLeftQuotientMap
        (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
          (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) x) :=
  rfl

/-- Rational general-Spin conjugation on the Spin quotient is measurable. -/
theorem measurable_fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
    (gamma : V.RationalCliffordGeneralSpinGroup) :
    Measurable
      (V.fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
        gamma) := by
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.mp ?_
  have hrep : Measurable
      (fun x : V.FullAdelicCliffordSpinCandidateGroup =>
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap
          (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
            (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) x)) :=
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_measurable.comp
      (V.continuous_cliffordSpinCandidateGeneralSpinConjugation RationalAdele
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)).measurable
  simpa [fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation,
    Function.comp_def] using measurable_iff_comap_le.mp hrep

/-- Rational general-Spin conjugation is a measurable equivalence of the
rational adelic Spin left quotient. -/
def fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugationMeasurableEquiv
    (gamma : V.RationalCliffordGeneralSpinGroup) :
    V.FullAdelicCliffordSpinCandidateLeftQuotient ≃ᵐ
      V.FullAdelicCliffordSpinCandidateLeftQuotient where
  toFun :=
    V.fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
      gamma
  invFun :=
    V.fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
      gamma⁻¹
  left_inv q := by
    induction q using Quot.inductionOn with
    | _ x =>
      change V.fullAdelicCliffordSpinCandidateLeftQuotientMap
          (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
            (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma⁻¹)
            (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
              (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) x)) =
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap x
      have h :=
        (V.cliffordSpinCandidateGeneralSpinConjugationMulEquiv RationalAdele
          (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)).left_inv x
      simpa only [map_inv] using congrArg
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap h
  right_inv q := by
    induction q using Quot.inductionOn with
    | _ x =>
      change V.fullAdelicCliffordSpinCandidateLeftQuotientMap
          (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
            (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
            (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
              (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma⁻¹) x)) =
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap x
      have h :=
        (V.cliffordSpinCandidateGeneralSpinConjugationMulEquiv RationalAdele
          (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)).right_inv x
      simpa only [map_inv] using congrArg
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap h
  measurable_toFun :=
    V.measurable_fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
      gamma
  measurable_invFun :=
    V.measurable_fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
      gamma⁻¹

/-- After inclusion in the rational adelic `GSpin` quotient, rational
conjugation of the neutral Spin quotient is exactly right translation by the
rational general-Spin diagonal point.  The left conjugating factor disappears
only here, in the left quotient. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_conjugation
    (gamma : V.RationalCliffordGeneralSpinGroup)
    (q : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
        (V.fullAdelicCliffordSpinCandidateLeftQuotientRationalGeneralSpinConjugation
          gamma q) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
        (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin q) := by
  induction q using Quot.inductionOn with
  | _ x =>
    change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom
          (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
            (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) x)) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x *
          V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
    change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele
          (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
            (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) x)) = _
    rw [V.cliffordSpinCandidateToCliffordGeneralSpinHom_conjugation]
    simpa only [fullAdelicCliffordSpinCandidateToGeneralSpinHom, mul_assoc] using
      leftCosetMap_gamma_mul
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
        ⟨(V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)⁻¹,
          ⟨gamma⁻¹, by simp⟩⟩
        (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x *
          V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)

end RationalQuadraticSpaceMatrix

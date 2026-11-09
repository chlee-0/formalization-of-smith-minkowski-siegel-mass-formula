import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellHorizontalThetaDensity
import SMSFormula.RationalCliffordGeneralSpinAllRationalShellIndex
import SMSFormula.RationalQuadraticIsometrySpinCandidateFiniteCarrierTransport
import SMSFormula.RationalCliffordSpinCandidateRawNormalizationUniqueness

/-!
# Presentation-covariant one-shell Spin coefficients

The exact one-shell cutoff is initially stated on a lattice-backed block
presentation.  Its lower-rank Spin volume is normalized by the Spin volume of
the block ambient group.  A supplied complement presentation identifies that
block with an arbitrary ambient rational quadratic space.

This file applies the exact raw Spin presentation covariance theorem to that
normalization.  The block denominator is replaced by the ambient
Spin Tamagawa number, and the normalized cutoff formula retains precisely the
ratio `tau(Spin(x⊥)) / tau(Spin(V))`.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n m : ℕ}

noncomputable local instance oneShellCoefficientTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix m) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance oneShellCoefficientTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix m) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

/-- A supplied lattice-coordinate presentation of an intrinsic orthogonal
complement.  The lower matrix is definitionally the matrix of `L`; only the
quadratic isometry is supplied. -/
def integralLatticeAnisotropicComplementPresentation
    (L : PositiveDefiniteIntegralLattice m) (V : RationalQuadraticSpaceMatrix n)
    (x : Fin n → ℚ)
    (e : L.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
      (V.nativeRationalQuadraticForm.orthogonalRestriction x)) :
    V.AnisotropicComplementPresentation x m where
  lowerSpace := L.rationalQuadraticSpaceMatrix
  complementIsometry := e

/-- The normalized one-shell coefficient attached to supplied lower and
ambient raw Spin data.  The presentation enters only through its lower
matrix; its role is to certify that this is the intrinsic complement of the
ambient source point. -/
def AnisotropicComplementPresentation.oneShellSpinTamagawaCoefficient
    {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
    (P : V.AnisotropicComplementPresentation x m)
    (DLower : P.lowerSpace.CliffordSpinCandidateRawOnoTamagawaData)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData) : ℝ≥0∞ :=
  DLower.spinTamagawaNumberENNReal /
    DAmbient.spinTamagawaNumberENNReal

/-- The represented nonzero norm determined by a supplied anisotropic
rational vector.  This packages the vector's value, but does not select a
vector from an arbitrary represented-norm fiber. -/
def representedNonzeroRationalNormOfVector
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    V.RepresentedNonzeroRationalNorm :=
  ⟨V.nativeRationalQuadraticForm x, hx, x, rfl⟩

namespace AnisotropicComplementPresentation

variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- Arbitrary certified raw data on the same lower and ambient matrices give
the same normalized one-shell coefficient. -/
theorem oneShellSpinTamagawaCoefficient_eq_of_rawData
    (DLower ELower :
      P.lowerSpace.CliffordSpinCandidateRawOnoTamagawaData)
    (DAmbient EAmbient :
      V.CliffordSpinCandidateRawOnoTamagawaData) :
    P.oneShellSpinTamagawaCoefficient DLower DAmbient =
      P.oneShellSpinTamagawaCoefficient ELower EAmbient := by
  rw [oneShellSpinTamagawaCoefficient,
    DLower.spinTamagawaNumberENNReal_eq ELower,
    DAmbient.spinTamagawaNumberENNReal_eq EAmbient]
  rfl

/-- The supplied one-shell coefficient as a function on the literal rational
fiber through `x`.  It is constant by construction after all presentation
normalization has been absorbed into the ambient denominator. -/
def oneShellSpinTamagawaCoefficientOnRationalFiber
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (DLower : P.lowerSpace.CliffordSpinCandidateRawOnoTamagawaData)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData) :
    (representedNonzeroRationalNormOfVector V x hx).rationalVectorFiber V →
      ℝ≥0∞ :=
  fun _ ↦ P.oneShellSpinTamagawaCoefficient DLower DAmbient

/-- The normalized Spin coefficient is literally constant on the complete
represented-norm fiber through the supplied source point. -/
theorem oneShellSpinTamagawaCoefficientOnRationalFiber_eq
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (DLower : P.lowerSpace.CliffordSpinCandidateRawOnoTamagawaData)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (y : (representedNonzeroRationalNormOfVector V x hx)
      |>.rationalVectorFiber V) :
    P.oneShellSpinTamagawaCoefficientOnRationalFiber
        hx DLower DAmbient y =
      P.oneShellSpinTamagawaCoefficient DLower DAmbient :=
  rfl

/-- Tonelli-ready form of the literal fiber constancy: the normalized Spin
coefficient factors from an arbitrary nonnegative sum over the whole rational
fiber. -/
theorem tsum_oneShellSpinTamagawaCoefficientOnRationalFiber_mul
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (DLower : P.lowerSpace.CliffordSpinCandidateRawOnoTamagawaData)
    (DAmbient : V.CliffordSpinCandidateRawOnoTamagawaData)
    (F : (representedNonzeroRationalNormOfVector V x hx)
      |>.rationalVectorFiber V → ℝ≥0∞) :
    (∑' y,
        P.oneShellSpinTamagawaCoefficientOnRationalFiber
          hx DLower DAmbient y * F y) =
      P.oneShellSpinTamagawaCoefficient DLower DAmbient *
        ∑' y, F y := by
  exact ENNReal.tsum_mul_left

end AnisotropicComplementPresentation

/-! ## Exact normalized cutoff -/

/-- Dividing the exact one-shell cutoff by a certified target Spin volume
retains the lower/target Spin ratio.  This is pure `ENNReal` normalization;
no finiteness or coefficient-one assertion is used. -/
theorem
    lintegral_fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure_logCutoff_div_spinTamagawa_eq
    (L : PositiveDefiniteIntegralLattice m) (hm : 3 ≤ m) [NeZero m]
    (a : ℚ) (ha : a ≠ 0)
    (DLower :
      L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (DTarget : (L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
      |>.CliffordSpinCandidateRawOnoTamagawaData)
    (phi : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ((∫⁻ z, f
        ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
      ∂fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure
        L hm a ha DLower hsurj phi) /
        DTarget.spinTamagawaNumberENNReal) =
      ((∫⁻ y, phi y
        ∂(L.rationalQuadraticSpaceMatrix
          |>.fullAdelicNonisotropicLastShellMeasure a ha)) *
        rationalIdeleClassLogCutoffLIntegral f) *
          (DLower.spinTamagawaNumberENNReal /
            DTarget.spinTamagawaNumberENNReal) := by
  rw [lintegral_fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure_logCutoff_eq
    L hm a ha DLower hsurj phi hphi f hf]
  rw [mul_div_assoc]

end RationalQuadraticSpaceMatrix

end

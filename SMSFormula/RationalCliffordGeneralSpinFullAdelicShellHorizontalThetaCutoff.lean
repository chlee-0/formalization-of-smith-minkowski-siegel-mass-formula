import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellOneShellCalibration
import SMSFormula.RationalCliffordGeneralSpinHorizontalFundamentalDomainComparison

/-!
# The horizontal theta cutoff on the rational block GSpin quotient

The complete rational shell-coset orbit sum gives a representative-free
nonnegative function on the ambient block `GSpin` group.  This file begins
the independent horizontal construction of the one-shell cutoff: it packages
the orbit sum itself, proves measurability and rational-left invariance, and
descends it to the existing rational adelic `GSpin` quotient.

No shell representative, global section, singleton-coset restriction, or
Fourier statement is used in these definitions.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

noncomputable local instance horizontalThetaCutoffRationalShellCosetCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Countable
      ((W.nonisotropicLastExtension a ha
        |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
          W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha) := by
  let V := W.nonisotropicLastExtension a ha
  letI : Countable V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup_countable
  exact Function.Surjective.countable
    (f := QuotientGroup.mk) Quotient.mk_surjective

private theorem coe_mem_nonisotropicLastComplementGeneralSpinStabilizer_of_mem_diagonalImage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (s : (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup))
    (hs : s ∈ W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha) :
    (s : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup)) ∈
      W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele := by
  rcases hs with ⟨lower, rfl⟩
  rw [W.nonisotropicLastComplementGeneralSpinDiagonalHom_coe a ha lower]
  exact
    (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
      a ha RationalAdele
      (lower : W.FullAdelicCliffordGeneralSpinGroup)).property

/-- For an ambient block point `g` and a rational shell right coset, the
shell point represented by `g⁻¹ * gamma`.  The definition descends through
the right coset itself; it does not select a rational representative. -/
noncomputable def fullAdelicNonisotropicLastRationalShellCosetInvOrbit
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup)) :
    ((W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha) →
      W.nonisotropicLastQuadraticShell a ha RationalAdele :=
  Quotient.lift
    (fun gamma : (W.nonisotropicLastExtension a ha
        |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) =>
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalAdele
        (g⁻¹ * (gamma : (W.nonisotropicLastExtension a ha
          |>.FullAdelicCliffordGeneralSpinGroup)))) (by
      intro gamma delta hrel
      apply
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_leftRel_iff
          W a ha _ _).1
      rw [QuotientGroup.leftRel_apply]
      have himage : gamma⁻¹ * delta ∈
          W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha := by
        change QuotientGroup.leftRel
          (W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha)
            gamma delta at hrel
        rw [QuotientGroup.leftRel_apply] at hrel
        exact hrel
      convert
        coe_mem_nonisotropicLastComplementGeneralSpinStabilizer_of_mem_diagonalImage
          W a ha (gamma⁻¹ * delta) himage using 1
      all_goals simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      all_goals group)

@[simp]
theorem fullAdelicNonisotropicLastRationalShellCosetInvOrbit_mk
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (g : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup))
    (gamma : (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
    W.fullAdelicNonisotropicLastRationalShellCosetInvOrbit a ha g
        (QuotientGroup.mk gamma) =
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalAdele
        (g⁻¹ * (gamma : (W.nonisotropicLastExtension a ha
          |>.FullAdelicCliffordGeneralSpinGroup))) :=
  rfl

theorem measurable_fullAdelicNonisotropicLastRationalShellCosetInvOrbit
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (xi : (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha) :
    Measurable (fun g : (W.nonisotropicLastExtension a ha
        |>.FullAdelicCliffordGeneralSpinGroup) =>
      W.fullAdelicNonisotropicLastRationalShellCosetInvOrbit a ha g xi) := by
  rw [show xi = QuotientGroup.mk (Quot.out xi) by exact (Quot.out_eq xi).symm]
  simp only [fullAdelicNonisotropicLastRationalShellCosetInvOrbit_mk]
  exact (W.continuous_fullAdelic_nonisotropicLastShellOrbitMap a ha).measurable.comp
    (by fun_prop)

/-- The complete rational theta orbit sum attached to a nonnegative shell
test function. -/
noncomputable def fullAdelicNonisotropicLastShellThetaOrbitSum
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (phi : W.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (g : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup)) : ℝ≥0∞ :=
  ∑' xi,
    phi (W.fullAdelicNonisotropicLastRationalShellCosetInvOrbit a ha g xi)

theorem measurable_fullAdelicNonisotropicLastShellThetaOrbitSum
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (phi : W.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi) :
    Measurable (W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi) := by
  unfold fullAdelicNonisotropicLastShellThetaOrbitSum
  exact Measurable.ennreal_tsum fun xi =>
    hphi.comp
      (W.measurable_fullAdelicNonisotropicLastRationalShellCosetInvOrbit
        a ha xi)

private theorem fullAdelicNonisotropicLastRationalShellCosetInvOrbit_smul
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (delta : (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup))
    (g : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup))
    (xi : (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha) :
    W.fullAdelicNonisotropicLastRationalShellCosetInvOrbit a ha
        ((delta : (W.nonisotropicLastExtension a ha
          |>.FullAdelicCliffordGeneralSpinGroup)) * g) xi =
      W.fullAdelicNonisotropicLastRationalShellCosetInvOrbit a ha g
        (delta⁻¹ • xi) := by
  induction xi using Quotient.inductionOn with
  | _ gamma =>
      change
        CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalAdele
            ((((delta : (W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup)) * g)⁻¹) *
              (gamma : (W.nonisotropicLastExtension a ha
                |>.FullAdelicCliffordGeneralSpinGroup))) =
          CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalAdele
            (g⁻¹ * (((delta⁻¹ * gamma :
              (W.nonisotropicLastExtension a ha
                |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup))) :
              (W.nonisotropicLastExtension a ha
                |>.FullAdelicCliffordGeneralSpinGroup)))
      congr 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group

theorem fullAdelicNonisotropicLastShellThetaOrbitSum_rational_mul
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (phi : W.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (delta : (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup))
    (g : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup)) :
    W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi
        ((delta : (W.nonisotropicLastExtension a ha
          |>.FullAdelicCliffordGeneralSpinGroup)) * g) =
      W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi g := by
  unfold fullAdelicNonisotropicLastShellThetaOrbitSum
  simp_rw [W.fullAdelicNonisotropicLastRationalShellCosetInvOrbit_smul
    a ha delta g]
  exact (MulAction.toPerm delta⁻¹).tsum_eq
    (fun xi => phi
      (W.fullAdelicNonisotropicLastRationalShellCosetInvOrbit a ha g xi))

/-- The independent theta orbit sum descended to the existing rational left
quotient. -/
noncomputable def fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (phi : W.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞) :
    (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinLeftQuotient) → ℝ≥0∞ :=
  Quot.lift
    (W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi) (by
      intro g h hrel
      rcases hrel with ⟨delta, rfl⟩
      exact
        (W.fullAdelicNonisotropicLastShellThetaOrbitSum_rational_mul
          a ha phi delta g).symm)

@[simp]
theorem fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient_mk
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (phi : W.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (g : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup)) :
    W.fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient a ha phi
        ((W.nonisotropicLastExtension a ha
          |>.fullAdelicCliffordGeneralSpinLeftQuotientMap) g) =
      W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi g :=
  rfl

theorem measurable_fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (phi : W.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi) :
    Measurable
      (W.fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient
        a ha phi) := by
  let V := W.nonisotropicLastExtension a ha
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.mp ?_
  intro s hs
  rcases hs with ⟨s', hs', rfl⟩
  rcases hs' with ⟨t, ht, rfl⟩
  simpa only [Set.preimage_preimage,
    fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient_mk] using
      (measurable_iff_comap_le.mp
        (W.measurable_fullAdelicNonisotropicLastShellThetaOrbitSum
          a ha phi hphi))
        ((W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi) ⁻¹' t)
        ⟨t, ht, rfl⟩

/-- Adding the representative-free theta density on the rational quotient
commutes exactly with rational-diagonal periodization. -/
theorem
    fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_withDensity_thetaOrbitSum
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (phi : W.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi)
    (mu : Measure ((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinLeftQuotient)) :
    let V := W.nonisotropicLastExtension a ha
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (mu.withDensity
          (W.fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient
            a ha phi)) =
      (V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift mu).withDensity
        (W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi) := by
  let V := W.nonisotropicLastExtension a ha
  let theta := W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi
  let thetaQ :=
    W.fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient a ha phi
  have htheta : Measurable theta :=
    W.measurable_fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi hphi
  have hthetaQ : Measurable thetaQ :=
    W.measurable_fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient
      a ha phi hphi
  dsimp only
  apply Measure.ext_of_lintegral
  intro f hf
  rw [V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
    (mu.withDensity thetaQ) f hf]
  rw [lintegral_withDensity_eq_lintegral_mul _ htheta hf]
  rw [V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
    mu (theta * f) (htheta.mul hf)]
  apply tsum_congr
  intro gamma
  change
    (∫⁻ y, f
        (V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection
          gamma y) ∂mu.withDensity thetaQ) = _
  calc
    (∫⁻ y, f
        (V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection
          gamma y) ∂mu.withDensity thetaQ) =
        ∫⁻ y, thetaQ y * f
          (V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection
            gamma y) ∂mu := by
      simpa only [Pi.mul_apply, Function.comp_apply] using
        (lintegral_withDensity_eq_lintegral_mul mu hthetaQ
          (hf.comp
            (V.measurable_fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection
              gamma)))
    _ = _ := by
      apply lintegral_congr
      intro y
      congr 1
      change thetaQ y = theta
        (V.fullAdelicCliffordGeneralSpinRationalTranslateFundamentalSection gamma y)
      rw [show thetaQ y = theta
          (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y) by
        have hmk :=
          W.fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient_mk
            a ha phi (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y)
        rw [V.fullAdelicCliffordGeneralSpinLeftQuotientMap_fundamentalDomainSection y]
          at hmk
        exact hmk]
      exact
        (W.fullAdelicNonisotropicLastShellThetaOrbitSum_rational_mul
          a ha phi gamma
          (V.fullAdelicCliffordGeneralSpinFundamentalDomainSection y)).symm

/-- Periodizing the horizontally normalized rational quotient measure
recovers the established horizontal full-adelic Haar exactly. -/
theorem fullAdelicCliffordGeneralSpinPeriodizedHorizontalQuotientMeasure_eq
    (V : RationalQuadraticSpaceMatrix n) :
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure =
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  let D := V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
  apply Measure.ext_of_lintegral
  intro f hf
  rw [V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
    D.quotientMeasure f hf]
  exact D.isMeasurableWeilQuotientMeasure.lintegral_leftPeriodize_eq f hf

theorem fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_smul
    (V : RationalQuadraticSpaceMatrix n)
    (c : ℝ≥0∞)
    (mu : Measure V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift (c • mu) =
      c • V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift mu := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
    (c • mu) f hf]
  rw [lintegral_smul_measure]
  rw [lintegral_smul_measure]
  rw [V.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
    mu f hf]

/-- The normalized target horizontal theta cutoff on the existing block
rational `GSpin` quotient.  It is defined independently from the crossed
one-shell quotient measure. -/
noncomputable def fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (phi : W.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞) :
    Measure ((W.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinLeftQuotient) :=
  ((W.nonisotropicLastExtension a ha)
      |>.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
      |>.quotientMeasure).withDensity
    (W.fullAdelicNonisotropicLastShellThetaOrbitSumOnLeftQuotient a ha phi)

theorem
    periodized_fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (phi : W.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi) :
    let V := W.nonisotropicLastExtension a ha
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (W.fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure a ha phi) =
      V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.withDensity
        (W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi) := by
  let V := W.nonisotropicLastExtension a ha
  dsimp only
  rw [fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure]
  rw [W.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_withDensity_thetaOrbitSum
    a ha phi hphi
      V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure]
  rw [V.fullAdelicCliffordGeneralSpinPeriodizedHorizontalQuotientMeasure_eq]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {r : ℕ}

/-- The target horizontal theta cutoff at the calibrated lattice scale.  Its
density is the independent complete rational theta orbit sum; the only outer
coefficient is the existing horizontal periodization scalar. -/
noncomputable def fullAdelicNonisotropicLastCalibratedHorizontalThetaCutoffMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (a : ℚ) (ha : a ≠ 0)
    (phi : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞) :
    Measure ((L.rationalQuadraticSpaceMatrix.nonisotropicLastExtension a ha)
      |>.FullAdelicCliffordGeneralSpinLeftQuotient) :=
  L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
      (by omega : 3 ≤ r + 2) inst hP hconv •
    (L.rationalQuadraticSpaceMatrix
      |>.fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure a ha phi)

/-- The calibrated target cutoff periodizes to the concrete horizontal
scalar times horizontal Haar with the complete theta density.  Thus the sole
remaining Gate-2 ambient comparison is the coefficient-one identification of
that density measure with the weighted raw coset-sum bind. -/
theorem
    periodized_fullAdelicNonisotropicLastCalibratedHorizontalThetaCutoffMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (a : ℚ) (ha : a ≠ 0)
    (phi : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi) :
    let W := L.rationalQuadraticSpaceMatrix
    let V := W.nonisotropicLastExtension a ha
    V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (L.fullAdelicNonisotropicLastCalibratedHorizontalThetaCutoffMeasure
          hr inst hP hconv a ha phi) =
      L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
          (by omega) inst hP hconv •
        V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure.withDensity
          (W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi) := by
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  let c := L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
    (by omega : 3 ≤ r + 2) inst hP hconv
  dsimp only
  rw [fullAdelicNonisotropicLastCalibratedHorizontalThetaCutoffMeasure]
  rw [V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_smul]
  rw [W.periodized_fullAdelicNonisotropicLastHorizontalThetaCutoffMeasure
    a ha phi hphi]

end PositiveDefiniteIntegralLattice

end

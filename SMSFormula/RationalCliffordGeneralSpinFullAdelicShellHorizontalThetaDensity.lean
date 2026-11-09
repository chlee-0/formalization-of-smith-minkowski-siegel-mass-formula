import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellHorizontalThetaCutoff

/-!
# Identifying the horizontal theta density with the weighted raw shell bind

The complete rational shell-coset theta density on horizontal full-adelic
`GSpin` Haar is exactly the native-shell bind of the weighted complete raw
coset-sum kernel.  The proof decomposes the raw kernel only internally into
transformed standard orbit fibers, applies the coefficient-one measurable Weil
identity to each summand, and reassembles the genuine countable rational
shell-coset sum.

This closes Gate 2: periodization injectivity identifies the independently
constructed calibrated horizontal theta cutoff with the crossed one-shell
measure, whose logarithmic integral has the lower-rank Spin Tamagawa number as
its sole nontrivial coefficient.  No Fourier statement, shell section, public
coset representative, new carrier, or additional scalar is introduced.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance horizontalThetaDensityInfiniteT2Space : T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance horizontalThetaDensityFiniteT2Space : T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance horizontalThetaDensityT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance horizontalThetaDensitySourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance horizontalThetaDensitySourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance horizontalThetaDensitySourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance horizontalThetaDensitySourcePolishSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    PolishSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupPolishSpaceForMeasurableDescent

noncomputable local instance horizontalThetaDensityTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance horizontalThetaDensityTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

noncomputable local instance horizontalThetaDensityCountable
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

private noncomputable def fullAdelicNonisotropicLastShellThetaTransformedOrbitKernel
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (gamma : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup)) :
    Kernel
      (W.nonisotropicLastQuadraticShell a ha RationalAdele)
      ((W.nonisotropicLastExtension a ha)
        |>.FullAdelicCliffordGeneralSpinGroup) :=
  Kernel.map
    (W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha)
    (fun z => (z * gamma⁻¹)⁻¹)

private theorem fullAdelicNonisotropicLastShellRawCosetSumKernel_eq_sum_thetaTransformed
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    W.fullAdelicNonisotropicLastShellRawCosetSumKernel a ha =
      Kernel.sum fun xi :
          (W.nonisotropicLastExtension a ha
            |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
              W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha =>
        fullAdelicNonisotropicLastShellThetaTransformedOrbitKernel W a ha
          ((Quot.out xi :
            (W.nonisotropicLastExtension a ha
              |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
            (W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup)) := by
  apply Kernel.ext
  intro x
  obtain ⟨g, rfl⟩ :=
    CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_surjective
      W a ha x
  rw [W.fullAdelicNonisotropicLastShellRawCosetSumKernel_orbit a ha g]
  rw [Kernel.sum_apply]
  rw [fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberSumMeasure]
  rw [Measure.map_sum (measurable_mul_const g⁻¹).aemeasurable]
  congr 1
  funext xi
  let gamma := Quot.out xi
  let gammaA : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup) := gamma
  have hraw :
      W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure
          a ha xi =
        W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel a ha gammaA := by
    rw [show xi = QuotientGroup.mk gamma by exact (Quot.out_eq xi).symm]
    exact
      W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure_mk
        a ha gamma
  change Measure.map (fun z => z * g⁻¹)
      (W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure
        a ha xi) =
    fullAdelicNonisotropicLastShellThetaTransformedOrbitKernel W a ha gammaA
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalAdele g)
  rw [hraw]
  rw [W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel_apply]
  have htransform : Measurable
      (fun z : (W.nonisotropicLastExtension a ha
        |>.FullAdelicCliffordGeneralSpinGroup) =>
          (z * gammaA⁻¹)⁻¹) := by fun_prop
  rw [fullAdelicNonisotropicLastShellThetaTransformedOrbitKernel, Kernel.map_apply _ htransform]
  rw [W.fullAdelicNonisotropicLastShellOrbitFiberKernel_orbit a ha g]
  let muH :=
    W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha
  have hleft : Measurable
      (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha =>
        gammaA * h.1) := by fun_prop
  have hright : Measurable
      (fun z : (W.nonisotropicLastExtension a ha
        |>.FullAdelicCliffordGeneralSpinGroup) => z * g⁻¹) := by fun_prop
  have horbit : Measurable
      (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha =>
        g * h.1) := by fun_prop
  rw [Measure.map_map hright hleft, Measure.map_map htransform horbit]
  let psi := fun h :
      W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha =>
    gammaA * h.1 * g⁻¹
  have hinv : Measure.map (fun h :
      W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha => h⁻¹)
      muH = muH := by
    change muH.inv = muH
    exact Measure.inv_eq_self muH
  calc
    Measure.map ((fun z => z * g⁻¹) ∘ fun h => gammaA * h.1) muH =
        Measure.map psi muH := by rfl
    _ = Measure.map psi
        (Measure.map (fun h :
          W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha => h⁻¹)
          muH) := by rw [hinv]
    _ = Measure.map (psi ∘ fun h :
          W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha => h⁻¹)
        muH := by rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = Measure.map ((fun z => (z * gammaA⁻¹)⁻¹) ∘ fun h => g * h.1)
        muH := by
      congr 1
      funext h
      simp only [psi, Function.comp_apply, Subgroup.coe_inv, mul_inv_rev,
        inv_inv, mul_assoc]

private theorem lintegral_fullAdelicHorizontalGSpin_transform_eq_self
    (W : RationalQuadraticSpaceMatrix n)
    (a : ℚ) (ha : a ≠ 0)
    (gamma : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup))
    (F : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup) → ℝ≥0∞) :
    ∫⁻ z, F ((z * gamma⁻¹)⁻¹)
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) =
      ∫⁻ z, F z
        ∂((W.nonisotropicLastExtension a ha)
          |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure) := by
  let V := W.nonisotropicLastExtension a ha
  let muG := V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  letI : Measure.IsMulLeftInvariant muG :=
    (V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
      |>.toIsMulLeftInvariant)
  have hinv : Measure.map
      (fun z : V.FullAdelicCliffordGeneralSpinGroup => z⁻¹) muG = muG := by
    change muG.inv = muG
    exact Measure.inv_eq_self muG
  calc
    (∫⁻ z, F ((z * gamma⁻¹)⁻¹) ∂muG) =
        ∫⁻ z, F (gamma * z⁻¹) ∂muG := by
      apply lintegral_congr
      intro z
      rw [mul_inv_rev, inv_inv]
    _ = ∫⁻ z, F (gamma * z) ∂muG := by
      have h := lintegral_map_equiv
        (μ := muG)
        (fun z : V.FullAdelicCliffordGeneralSpinGroup => F (gamma * z))
        (MeasurableEquiv.inv V.FullAdelicCliffordGeneralSpinGroup)
      have hinv' : Measure.map
          (MeasurableEquiv.inv V.FullAdelicCliffordGeneralSpinGroup) muG =
          muG := by
        change Measure.map
          (fun z : V.FullAdelicCliffordGeneralSpinGroup => z⁻¹) muG = muG
        exact hinv
      rw [hinv'] at h
      simpa using h.symm
    _ = ∫⁻ z, F z ∂muG := lintegral_mul_left_eq_self F gamma

private theorem fullAdelicNonisotropicLastShellWeighted_bind_thetaTransformed
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (phi : W.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi)
    (gamma : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup)) :
    ((W.fullAdelicNonisotropicLastShellMeasure a ha).withDensity phi).bind
        (fullAdelicNonisotropicLastShellThetaTransformedOrbitKernel W a ha gamma) =
      ((W.nonisotropicLastExtension a ha)
        |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure).withDensity
          (fun z => phi
            (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
              W a ha RationalAdele (z⁻¹ * gamma))) := by
  let V := W.nonisotropicLastExtension a ha
  let X := W.nonisotropicLastQuadraticShell a ha RationalAdele
  let muX := W.fullAdelicNonisotropicLastShellMeasure a ha
  let muG := V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let orbit := CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
    W a ha RationalAdele
  let transform := fun z : V.FullAdelicCliffordGeneralSpinGroup =>
    (z * gamma⁻¹)⁻¹
  have horbit : Measurable orbit :=
    (W.continuous_fullAdelic_nonisotropicLastShellOrbitMap a ha).measurable
  have htransform : Measurable transform := by fun_prop
  have hdensity : Measurable (fun z : V.FullAdelicCliffordGeneralSpinGroup =>
      phi (orbit (z⁻¹ * gamma))) := by fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind
    (fullAdelicNonisotropicLastShellThetaTransformedOrbitKernel W a ha gamma).aemeasurable
    hf.aemeasurable]
  rw [lintegral_withDensity_eq_lintegral_mul muX hphi hf.lintegral_kernel]
  rw [lintegral_withDensity_eq_lintegral_mul muG hdensity hf]
  have hinner (x : X) :
      (∫⁻ z, f z ∂fullAdelicNonisotropicLastShellThetaTransformedOrbitKernel W a ha gamma x) =
        ∫⁻ z, f (transform z)
          ∂W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha x := by
    rw [fullAdelicNonisotropicLastShellThetaTransformedOrbitKernel, Kernel.map_apply _ htransform]
    rw [lintegral_map hf htransform]
  simp_rw [hinner]
  have hfiber (x : X) :
      phi x *
          (∫⁻ z, f (transform z)
            ∂W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha x) =
        ∫⁻ z, phi (orbit z) * f (transform z)
          ∂W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha x := by
    obtain ⟨g, rfl⟩ :=
      CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_surjective
        W a ha x
    rw [W.lintegral_fullAdelicNonisotropicLastShellOrbitFiberKernel_orbit
      a ha (fun z => f (transform z)) (hf.comp htransform) g]
    rw [W.lintegral_fullAdelicNonisotropicLastShellOrbitFiberKernel_orbit
      a ha (fun z => phi (orbit z) * f (transform z))
        ((hphi.comp horbit).mul (hf.comp htransform)) g]
    rw [← lintegral_const_mul _ (by fun_prop)]
    apply lintegral_congr
    intro h
    have horbitmul : orbit (g * h.1) = orbit g :=
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_mul_of_mem_stabilizer
        W a ha g h.1 h.2
    rw [horbitmul]
  rw [show
    (phi * fun x : X =>
      ∫⁻ z, f (transform z)
        ∂W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha x) =
      (fun x : X => ∫⁻ z, phi (orbit z) * f (transform z)
        ∂W.fullAdelicNonisotropicLastShellOrbitFiberKernel a ha x) by
    funext x
    simpa only [Pi.mul_apply] using hfiber x]
  rw [W.lintegral_fullAdelicNonisotropicLastShellOrbitFiberKernel_measurable
    a ha (fun z => phi (orbit z) * f (transform z))
      ((hphi.comp horbit).mul (hf.comp htransform))]
  let H := fun z : V.FullAdelicCliffordGeneralSpinGroup =>
    phi (orbit (z⁻¹ * gamma)) * f z
  calc
    (∫⁻ z, phi (orbit z) * f (transform z) ∂muG) =
        ∫⁻ z, H (transform z) ∂muG := by
      apply lintegral_congr
      intro z
      change phi (orbit z) * f (transform z) =
        phi (orbit ((transform z)⁻¹ * gamma)) * f (transform z)
      rw [show (transform z)⁻¹ * gamma = z by
        simp only [transform, inv_inv, mul_assoc, inv_mul_cancel, mul_one]]
    _ = ∫⁻ z, H z ∂muG :=
      lintegral_fullAdelicHorizontalGSpin_transform_eq_self W a ha gamma H
    _ = ∫⁻ z, ((fun z => phi (orbit (z⁻¹ * gamma))) * f) z ∂muG := by
      rfl

/-- Horizontal full-adelic GSpin Haar with the complete rational theta density
is exactly the native shell measure bound against the weighted complete raw
coset-sum kernel.  The rational shell-coset decomposition is internal to the
proof and every summand occurs with coefficient one. -/
theorem fullAdelicNonisotropicLastShellHorizontal_withDensity_thetaOrbitSum_eq_weightedRawCosetSum
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (phi : W.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi) :
    ((W.nonisotropicLastExtension a ha)
      |>.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure).withDensity
        (W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi) =
      W.fullAdelicNonisotropicLastShellWeightedRawCosetSumBoundMeasure
        a ha phi := by
  let V := W.nonisotropicLastExtension a ha
  let X := W.nonisotropicLastQuadraticShell a ha RationalAdele
  let Xi :=
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
      W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha
  let muX := W.fullAdelicNonisotropicLastShellMeasure a ha
  let muG := V.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
  let orbit := CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
    W a ha RationalAdele
  let kappa : Xi → Kernel X V.FullAdelicCliffordGeneralSpinGroup :=
    fun xi => fullAdelicNonisotropicLastShellThetaTransformedOrbitKernel W a ha
      ((Quot.out xi : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
        V.FullAdelicCliffordGeneralSpinGroup)
  let density : Xi → V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞ :=
    fun xi z => phi (orbit (z⁻¹ *
      ((Quot.out xi : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
        V.FullAdelicCliffordGeneralSpinGroup)))
  have htheta :
      Measurable (W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi) :=
    by
      unfold fullAdelicNonisotropicLastShellThetaOrbitSum
      apply Measurable.ennreal_tsum
      intro xi
      rw [show xi = QuotientGroup.mk (Quot.out xi) by
        exact (Quot.out_eq xi).symm]
      simp only [fullAdelicNonisotropicLastRationalShellCosetInvOrbit_mk]
      exact hphi.comp
        ((W.continuous_fullAdelic_nonisotropicLastShellOrbitMap a ha).measurable.comp
          (by fun_prop))
  have horbit : Measurable orbit :=
    (W.continuous_fullAdelic_nonisotropicLastShellOrbitMap a ha).measurable
  have hdensity (xi : Xi) : Measurable (density xi) := by
    exact hphi.comp (horbit.comp (by fun_prop))
  symm
  rw [fullAdelicNonisotropicLastShellWeightedRawCosetSumBoundMeasure]
  rw [fullAdelicNonisotropicLastShellRawCosetSumKernel_eq_sum_thetaTransformed W a ha]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind (Kernel.sum kappa).aemeasurable hf.aemeasurable]
  simp_rw [Kernel.sum_apply]
  simp_rw [lintegral_sum_measure]
  rw [lintegral_tsum]
  · calc
      (∑' xi, ∫⁻ x, ∫⁻ z, f z ∂kappa xi x ∂muX.withDensity phi) =
          ∑' xi, ∫⁻ z, density xi z * f z ∂muG := by
        apply tsum_congr
        intro xi
        rw [← Measure.lintegral_bind (kappa xi).aemeasurable hf.aemeasurable]
        rw [show (muX.withDensity phi).bind (kappa xi) =
            muG.withDensity (density xi) by
          exact fullAdelicNonisotropicLastShellWeighted_bind_thetaTransformed W a ha phi hphi
            ((Quot.out xi :
              V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
              V.FullAdelicCliffordGeneralSpinGroup)]
        rw [lintegral_withDensity_eq_lintegral_mul muG (hdensity xi) hf]
        rfl
      _ = ∫⁻ z, (∑' xi, density xi z * f z) ∂muG := by
        rw [lintegral_tsum]
        intro xi
        exact ((hdensity xi).mul hf).aemeasurable
      _ = ∫⁻ z,
          W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi z * f z
          ∂muG := by
        apply lintegral_congr
        intro z
        rw [ENNReal.tsum_mul_right]
        congr 1
        unfold fullAdelicNonisotropicLastShellThetaOrbitSum density
        apply tsum_congr
        intro xi
        change phi (orbit (z⁻¹ *
            ((Quot.out xi :
              V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
              V.FullAdelicCliffordGeneralSpinGroup))) =
          phi (W.fullAdelicNonisotropicLastRationalShellCosetInvOrbit
            a ha z xi)
        congr 1
        have hm :=
          W.fullAdelicNonisotropicLastRationalShellCosetInvOrbit_mk
            a ha z (Quot.out xi)
        have hxi :
            (QuotientGroup.mk (Quot.out xi) : Xi) = xi :=
          Quot.out_eq xi
        simpa only [orbit, hxi] using hm.symm
      _ = ∫⁻ z, f z ∂muG.withDensity
          (W.fullAdelicNonisotropicLastShellThetaOrbitSum a ha phi) := by
        simpa only [Pi.mul_apply] using
          (lintegral_withDensity_eq_lintegral_mul muG htheta hf).symm
  · intro xi
    exact hf.lintegral_kernel.aemeasurable

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {r : ℕ}

noncomputable local instance horizontalThetaDensityLatticeTargetMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix
        |>.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance horizontalThetaDensityLatticeTargetBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix
        |>.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

/-- The independently constructed calibrated horizontal theta cutoff is the
crossed one-shell quotient measure.  Periodization injectivity makes this
identification literal after the common horizontal scalar comparison. -/
theorem fullAdelicNonisotropicLastCalibratedHorizontalThetaCutoffMeasure_eq_oneShellCutoffBoundMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (a : ℚ) (ha : a ≠ 0)
    (phi : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi) :
    let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv
    L.fullAdelicNonisotropicLastCalibratedHorizontalThetaCutoffMeasure
        hr inst hP hconv a ha phi =
      fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure
        L (by omega) a ha D
          (L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
            (by omega)) phi := by
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega : 3 ≤ r + 2) inst hP hconv
  let W := L.rationalQuadraticSpaceMatrix
  let X := W.nonisotropicLastQuadraticShell a ha RationalAdele
  have hphiDefault :
      @Measurable X ℝ≥0∞ Subtype.instMeasurableSpace
        ENNReal.measurableSpace phi := by
    rw [@BorelSpace.measurable_eq X _ Subtype.instMeasurableSpace _]
    exact hphi
  dsimp only
  apply
    L.fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure_eq_of_periodized_eq_horizontal_smul_weightedRawCosetSum
      hr inst hP hconv a ha phi hphi
  dsimp only
  rw [L.periodized_fullAdelicNonisotropicLastCalibratedHorizontalThetaCutoffMeasure
    hr inst hP hconv a ha phi hphiDefault]
  rw [W.fullAdelicNonisotropicLastShellHorizontal_withDensity_thetaOrbitSum_eq_weightedRawCosetSum a ha phi hphi]

/-- The target horizontal theta cutoff unfolds with exactly the shell test
integral, the common idèle-class cutoff, and the lower-rank Spin Tamagawa
number.  No additional local, rational-coset, or periodization coefficient
remains. -/
theorem lintegral_fullAdelicNonisotropicLastCalibratedHorizontalThetaCutoffMeasure_logCutoff_eq
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (a : ℚ) (ha : a ≠ 0)
    (phi : L.rationalQuadraticSpaceMatrix
      |>.nonisotropicLastQuadraticShell a ha RationalAdele → ℝ≥0∞)
    (hphi : Measurable phi)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv
    let W := L.rationalQuadraticSpaceMatrix
    let V := W.nonisotropicLastExtension a ha
    (∫⁻ z, f (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule z)
      ∂L.fullAdelicNonisotropicLastCalibratedHorizontalThetaCutoffMeasure
        hr inst hP hconv a ha phi) =
      (∫⁻ x, phi x ∂W.fullAdelicNonisotropicLastShellMeasure a ha) *
        rationalIdeleClassLogCutoffLIntegral f *
          D.spinTamagawaNumberENNReal := by
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega : 3 ≤ r + 2) inst hP hconv
  let W := L.rationalQuadraticSpaceMatrix
  let V := W.nonisotropicLastExtension a ha
  let hsurj :=
    L.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective_of_rankAtLeastThree
      (by omega : 3 ≤ r + 2)
  dsimp only
  rw [L.fullAdelicNonisotropicLastCalibratedHorizontalThetaCutoffMeasure_eq_oneShellCutoffBoundMeasure
    hr inst hP hconv a ha phi hphi]
  exact
    lintegral_fullAdelicNonisotropicLastShellOneShellCutoffBoundMeasure_logCutoff_eq
      L (by omega) a ha D hsurj phi hphi f hf

end PositiveDefiniteIntegralLattice

end

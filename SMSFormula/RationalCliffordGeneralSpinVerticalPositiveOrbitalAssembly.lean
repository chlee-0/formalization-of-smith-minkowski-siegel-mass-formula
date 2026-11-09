import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalPeriodization

/-!
# Assemble the positive-idele Spin orbital expansion

This file closes the section-free global Weil/Tonelli interface between the
periodized vertical quotient lift and the descended raw Spin orbital kernel.
It does not impose a carrier restriction or introduce a measurable choice of
an adelic `GSpin` representative.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 900000
set_option maxHeartbeats 3000000

local instance positiveOrbitalAssemblyDiagonalImageNormal
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    (L.rationalQuadraticSpaceMatrix
      |>.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin).Normal := by
  rw [L.rationalQuadraticSpaceMatrix
    |>.range_rationalCliffordSpinCandidateDiagonalToGeneralSpin_eq_ker]
  infer_instance

/-- The selected rational `GSpin` representative of a positive rational
idele coset has exactly that positive rational similitude. -/
theorem rationalCliffordGeneralSpinDiagonalRepresentativeOfPositiveIdele_similitude
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (eta : positiveRationalIdeleDiagonalSubgroup) :
    L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr
        (rationalCliffordGeneralSpinDiagonalRepresentativeOfPositiveIdele
          L (by omega) eta) = eta := by
  apply Subtype.ext
  change
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom
        (rationalCliffordGeneralSpinDiagonalRepresentativeOfPositiveIdele
          L (by omega) eta) = (eta : positiveRationalAdeleUnitsSubgroup)
  let gamma := rationalCliffordGeneralSpinDiagonalRepresentativeOfPositiveIdele
    L (by omega) eta
  rcases gamma.2 with ⟨q, hq⟩
  change L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom
      (gamma : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) = _
  rw [show (gamma : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) =
      L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinFullAdelicDiagonalHom q
    from hq.symm]
  rw [L.rationalQuadraticSpaceMatrix.rational_fullAdelic_diagonal_generalSpin_similitude]
  let H := L.rationalQuadraticSpaceMatrix
    |>.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin
  let e := rationalGeneralSpinDiagonalQuotientEquivPositiveRationalIdeleDiagonal
    L (by omega)
  have hcoset : QuotientGroup.mk' H gamma = e.symm eta := by
    exact QuotientGroup.out_eq' _
  have heta : e (QuotientGroup.mk' H gamma) = eta := by
    rw [hcoset, e.apply_symm_apply]
  unfold e rationalGeneralSpinDiagonalQuotientEquivPositiveRationalIdeleDiagonal
    rationalGeneralSpinDiagonalQuotientEquivPositiveRationalUnits at heta
  simp [rationalGeneralSpinDiagonalQuotientEquivSimilitudeRange,
    positiveRationalUnitsEquivPositiveRationalIdeleDiagonal,
    positiveRationalUnitFullAdelicDiagonalHom,
    rationalCliffordGeneralSpinDiagonalSimilitudeHom] at heta
  have hval := congrArg
    (fun z : positiveRationalIdeleDiagonalSubgroup =>
      ((z : positiveRationalAdeleUnitsSubgroup) : RationalAdeleˣ)) heta
  change rationalUnitFullAdelicDiagonalHom
      (L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinDiagonalSimilitudeHom
        gamma) = ((eta : positiveRationalAdeleUnitsSubgroup) : RationalAdeleˣ) at hval
  have hqgamma :
      L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinGroupEquivDiagonal q =
        gamma := by
    apply Subtype.ext
    exact hq
  have hinv :
      L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinGroupEquivDiagonal.symm
          gamma = q := by
    rw [← hqgamma,
      L.rationalQuadraticSpaceMatrix.rationalCliffordGeneralSpinGroupEquivDiagonal.symm_apply_apply]
  simpa [hinv,
    rationalCliffordGeneralSpinDiagonalSimilitudeHom] using hval

/-- After the already proved rational conjugation normalization, each inner
Spin integral is the descended ambient orbital measure through the translated
rational `GSpin` origin. -/
theorem CliffordSpinCandidateRawOnoTamagawaData.lintegral_verticalPositiveSpinWeilIntegrand_eq_orbital
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (eta : positiveRationalIdeleDiagonalSubgroup)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ y, verticalPositiveSpinWeilIntegrand L (by omega) eta g f y
        ∂D.spinData.adelicMeasure =
      ∫⁻ z, f z
        ∂D.positiveSpinOrbitalKernelAtAmbient
          ((rationalCliffordGeneralSpinDiagonalRepresentativeOfPositiveIdele
              L (by omega) eta :
            L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) * g) := by
  let V := L.rationalQuadraticSpaceMatrix
  let rho := rationalCliffordGeneralSpinDiagonalRepresentativeOfPositiveIdele
    L (by omega) eta
  let gamma : V.RationalCliffordGeneralSpinGroup :=
    V.rationalCliffordGeneralSpinGroupEquivDiagonal.symm rho
  let conj := V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
    (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)
  have hrho :
      V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma =
        (rho : V.FullAdelicCliffordGeneralSpinGroup) := by
    change
      V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
          (V.rationalCliffordGeneralSpinGroupEquivDiagonal.symm rho) = _
    exact congrArg Subtype.val
      (V.rationalCliffordGeneralSpinGroupEquivDiagonal.apply_symm_apply rho)
  have hconj : Measurable conj :=
    (V.continuous_cliffordSpinCandidateGeneralSpinConjugation RationalAdele
      (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)).measurable
  have hmap : Measure.map conj D.spinData.adelicMeasure = D.spinData.adelicMeasure :=
    map_spin_adelicMeasure_rationalGeneralSpinConjugation (V := V) D gamma
  rw [D.positiveSpinOrbitalKernelAtAmbient_apply]
  let orbit := fun y : V.FullAdelicCliffordSpinCandidateGroup =>
    V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y *
      ((rho : V.FullAdelicCliffordGeneralSpinGroup) * g)
  have horbit : Measurable orbit :=
    (V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom
      RationalAdele).mul continuous_const |>.measurable
  change (∫⁻ y, verticalPositiveSpinWeilIntegrand L (by omega) eta g f y
      ∂D.spinData.adelicMeasure) = ∫⁻ z, f z ∂Measure.map orbit D.spinData.adelicMeasure
  rw [lintegral_map' hf.aemeasurable horbit.aemeasurable]
  calc
    (∫⁻ y, verticalPositiveSpinWeilIntegrand L (by omega) eta g f y
        ∂D.spinData.adelicMeasure) =
        ∫⁻ y, verticalPositiveSpinWeilIntegrand L (by omega) eta g f y
          ∂Measure.map conj D.spinData.adelicMeasure := by rw [hmap]
    _ = ∫⁻ y, verticalPositiveSpinWeilIntegrand L (by omega) eta g f (conj y)
          ∂D.spinData.adelicMeasure := by
      rw [lintegral_map'
        (measurable_verticalPositiveSpinWeilIntegrand
          L (by omega) eta g hf).aemeasurable hconj.aemeasurable]
    _ = ∫⁻ y, f (orbit y) ∂D.spinData.adelicMeasure := by
      apply lintegral_congr
      intro y
      unfold verticalPositiveSpinWeilIntegrand conj orbit
      change f ((rho : V.FullAdelicCliffordGeneralSpinGroup) *
          (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele
            (V.cliffordSpinCandidateGeneralSpinConjugation RationalAdele
              (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma) y) * g)) =
        f (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele y *
          ((rho : V.FullAdelicCliffordGeneralSpinGroup) * g))
      rw [V.cliffordSpinCandidateToCliffordGeneralSpinHom_conjugation]
      rw [hrho]
      simp only [mul_assoc]
      congr 1
      group

/-- The translated rational branch projects to multiplication by its positive
rational-idèle similitude on the descended orbital base. -/
theorem CliffordSpinCandidateRawOnoTamagawaData.lintegral_verticalPositiveSpinWeilIntegrand_eq_descended
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (eta : positiveRationalIdeleDiagonalSubgroup)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ y, verticalPositiveSpinWeilIntegrand L (by omega) eta g f y
        ∂D.spinData.adelicMeasure =
      ∫⁻ z, f z ∂L.positiveSpinOrbitalKernel hr D
        ((eta : positiveRationalAdeleUnitsSubgroup) *
          L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g) := by
  rw [D.lintegral_verticalPositiveSpinWeilIntegrand_eq_orbital L hr eta g f hf]
  rw [← L.positiveSpinOrbitalKernel_projection hr D
    ((rationalCliffordGeneralSpinDiagonalRepresentativeOfPositiveIdele
      L (by omega) eta :
        L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) * g)]
  congr 1
  rw [map_mul,
    rationalCliffordGeneralSpinDiagonalRepresentativeOfPositiveIdele_similitude
      L hr eta]

/-- The positive rational-diagonal orbital periodization is independent of
the actual similitude representative chosen over a fixed idèle class. -/
theorem CliffordSpinCandidateRawOnoTamagawaData.tsum_positiveSpinOrbitalKernel_verticalRepresentative_eq
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      (L.rationalQuadraticSpaceMatrix
        |>.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass))
    (a : positiveRationalAdeleUnitsSubgroup)
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞) :
    let V := L.rationalQuadraticSpaceMatrix
    ∑' eta : positiveRationalIdeleDiagonalSubgroup,
        ∫⁻ z, f z ∂L.positiveSpinOrbitalKernel hr D
          ((eta : positiveRationalAdeleUnitsSubgroup) *
            L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr
              (V.verticalGeneralSpinRepresentative hsurj
                (positiveRationalIdeleToIdeleClassHom a))) =
      ∑' eta : positiveRationalIdeleDiagonalSubgroup,
        ∫⁻ z, f z ∂L.positiveSpinOrbitalKernel hr D
          ((eta : positiveRationalAdeleUnitsSubgroup) * a) := by
  let V := L.rationalQuadraticSpaceMatrix
  let b : positiveRationalAdeleUnitsSubgroup :=
    L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr
      (V.verticalGeneralSpinRepresentative hsurj
        (positiveRationalIdeleToIdeleClassHom a))
  let F := fun x : positiveRationalAdeleUnitsSubgroup =>
    ∫⁻ z, f z ∂L.positiveSpinOrbitalKernel hr D x
  have hclass : positiveRationalIdeleToIdeleClassHom b =
      positiveRationalIdeleToIdeleClassHom a := by
    have h := V.verticalGeneralSpinRepresentative_ideleClass hsurj
      (positiveRationalIdeleToIdeleClassHom a)
    exact h
  let delta : positiveRationalAdeleUnitsSubgroup := b * a⁻¹
  have hdeltaKer : delta ∈ positiveRationalIdeleToIdeleClassHom.ker := by
    change positiveRationalIdeleToIdeleClassHom (b * a⁻¹) = 1
    rw [map_mul, map_inv, hclass, mul_inv_cancel]
  have hdelta : delta ∈ positiveRationalIdeleDiagonalSubgroup := by
    rw [range_positiveRationalUnitFullAdelicDiagonalHom_eq_ker]
    exact hdeltaKer
  let delta' : positiveRationalIdeleDiagonalSubgroup := ⟨delta, hdelta⟩
  have hba : b = (delta' : positiveRationalAdeleUnitsSubgroup) * a := by
    simp [delta', delta, mul_assoc]
  change leftPreperiodize positiveRationalIdeleDiagonalSubgroup F b =
    leftPreperiodize positiveRationalIdeleDiagonalSubgroup F a
  rw [hba]
  exact leftPreperiodize_gamma_mul
    positiveRationalIdeleDiagonalSubgroup F delta' a

/-- The periodized vertical quotient lift is exactly the ambient positive-idèle
integral of the descended raw Spin orbital kernel.  The only coefficient is
the already certified idèle-class/differential-Weil conversion scalar. -/
theorem CliffordSpinCandidateRawOnoTamagawaData.lintegral_periodizedVerticalSpinFiberHaarBoundMeasure_eq_positiveSpinOrbital
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      (L.rationalQuadraticSpaceMatrix
        |>.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass))
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    ∫⁻ x, f x
        ∂V.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
          (D.verticalSpinFiberHaarBoundMeasure L (by omega) hsurj) =
      (rationalIdeleClassHaarToDifferentialWeilScalar : ℝ≥0∞) *
        ∫⁻ a : positiveRationalAdeleUnitsSubgroup,
          (∫⁻ z, f z ∂L.positiveSpinOrbitalKernel hr D a)
          ∂positiveRationalIdeleDifferentialHaarMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  dsimp only [V]
  rw [D.lintegral_periodizedVerticalSpinFiberHaarBoundMeasure_eq_positiveSpinWeil
    L (by omega) hsurj f hf]
  congr 1
  calc
    (∫⁻ a : positiveRationalAdeleUnitsSubgroup,
        ∑' eta : positiveRationalIdeleDiagonalSubgroup,
          ∫⁻ y : V.FullAdelicCliffordSpinCandidateGroup,
            verticalPositiveSpinWeilIntegrand L (by omega) eta
              (V.verticalGeneralSpinRepresentative hsurj
                (positiveRationalIdeleToIdeleClassHom a)) f y
            ∂D.spinData.adelicMeasure
        ∂(positiveRationalIdeleDifferentialHaarMeasure.restrict
          positiveRationalIdeleMeasurableFundamentalDomainSubtype)) =
      ∫⁻ a : positiveRationalAdeleUnitsSubgroup,
        ∑' eta : positiveRationalIdeleDiagonalSubgroup,
          ∫⁻ z, f z ∂L.positiveSpinOrbitalKernel hr D
            ((eta : positiveRationalAdeleUnitsSubgroup) * a)
        ∂(positiveRationalIdeleDifferentialHaarMeasure.restrict
          positiveRationalIdeleMeasurableFundamentalDomainSubtype) := by
      apply lintegral_congr
      intro a
      calc
        (∑' eta : positiveRationalIdeleDiagonalSubgroup,
            ∫⁻ y : V.FullAdelicCliffordSpinCandidateGroup,
              verticalPositiveSpinWeilIntegrand L (by omega) eta
                (V.verticalGeneralSpinRepresentative hsurj
                  (positiveRationalIdeleToIdeleClassHom a)) f y
              ∂D.spinData.adelicMeasure) =
          ∑' eta : positiveRationalIdeleDiagonalSubgroup,
            ∫⁻ z, f z ∂L.positiveSpinOrbitalKernel hr D
              ((eta : positiveRationalAdeleUnitsSubgroup) *
                L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr
                  (V.verticalGeneralSpinRepresentative hsurj
                    (positiveRationalIdeleToIdeleClassHom a))) := by
              apply tsum_congr
              intro eta
              exact D.lintegral_verticalPositiveSpinWeilIntegrand_eq_descended
                L hr eta _ f hf
        _ = _ := D.tsum_positiveSpinOrbitalKernel_verticalRepresentative_eq
          L hr hsurj a f
    _ = ∫⁻ a : positiveRationalAdeleUnitsSubgroup,
        (∫⁻ z, f z ∂L.positiveSpinOrbitalKernel hr D a)
        ∂positiveRationalIdeleDifferentialHaarMeasure :=
      L.lintegral_positiveSpinOrbitalKernel_tsum_diagonal_eq hr D f hf

end RationalQuadraticSpaceMatrix

end

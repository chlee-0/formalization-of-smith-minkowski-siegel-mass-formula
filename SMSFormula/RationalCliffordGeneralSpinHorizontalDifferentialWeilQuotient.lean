import SMSFormula.RationalCliffordGeneralSpinHorizontalDifferentialWeilFiber
import SMSFormula.RationalCliffordGeneralSpinHorizontalFundamentalDomainComparison

/-!
# The specialized differential-Weil quotient identity for horizontal GSpin

This file compares the iterated differential quotient along

`A^× / Q^× -> GSpin(Q)\GSpin(A) -> SO(Q)\SO(A)`

with the quotient induced directly from the calibrated ambient differential
central extension.  The first step is the rational-diagonal exact sequence
needed to reindex the two periodizations.  It is proved here as a step of the
global quotient identity, not as a general central-extension result.
-/

noncomputable section

open MeasureTheory Set
open PositiveDefiniteIntegralLattice
open scoped ENNReal ProbabilityTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 400000

private abbrev IdeleDiagonal := rationalIdeleDiagonalSubgroup
private abbrev GSpinDiagonal :=
  V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
private abbrev SODiagonal :=
  V.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup

private local instance ideleDiagonalCountable : Countable IdeleDiagonal :=
  rationalIdeleDiagonalSubgroup_countable

private local instance gspinDiagonalCountable : Countable V.GSpinDiagonal :=
  V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup_countable

/-! ## The exact rational diagonal sequence -/

/-- Projection of the rational adelic `GSpin` diagonal to the rational
adelic `SO` diagonal. -/
private def rationalGSpinDiagonalToSO :
    V.GSpinDiagonal →* V.SODiagonal where
  toFun gamma := by
    refine ⟨V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom gamma, ?_⟩
    rcases gamma.2 with ⟨g, hg⟩
    refine ⟨CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V ℚ g, ?_⟩
    calc
      V.rationalSpecialOrthogonalFullAdelicDiagonalHom
          (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V ℚ g) =
          V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
            (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom g) :=
        (V.rational_fullAdelic_diagonal_generalSpinToSpecialOrthogonal g).symm
      _ = V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom gamma := by
        rw [hg]
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

/-- The diagonal projection is surjective by rational fieldwise `GSpin -> SO`
surjectivity. -/
private theorem rationalGSpinDiagonalToSO_surjective :
    Function.Surjective V.rationalGSpinDiagonalToSO := by
  intro delta
  rcases delta.2 with ⟨h, hh⟩
  obtain ⟨g, hg⟩ :=
    CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom_surjective
      V ℚ h
  refine ⟨⟨V.rationalCliffordGeneralSpinFullAdelicDiagonalHom g,
    ⟨g, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
      (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom g) = delta
  rw [V.rational_fullAdelic_diagonal_generalSpinToSpecialOrthogonal, hg]
  exact hh

/-- Central inclusion from the rational idele diagonal to the rational
`GSpin` diagonal. -/
private def rationalIdeleDiagonalToGSpin :
    IdeleDiagonal →* V.GSpinDiagonal where
  toFun eta := by
    refine ⟨CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
      V RationalAdele eta, ?_⟩
    rcases eta.2 with ⟨q, hq⟩
    refine ⟨CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ q, ?_⟩
    calc
      V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ q) =
          CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele
            (rationalUnitFullAdelicDiagonalHom q) :=
        (V.rational_fullAdelic_diagonal_generalSpinScalar q).symm
      _ = CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele eta := congrArg
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele) hq
  map_one' := Subtype.ext
    (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele).map_one
  map_mul' x y := Subtype.ext
    ((CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele).map_mul x y)

private theorem rationalIdeleDiagonalToGSpin_injective :
    Function.Injective V.rationalIdeleDiagonalToGSpin := by
  intro a b hab
  apply Subtype.ext
  apply CliffordGeneralSpinIntrinsicPoint.scalarGroupHom_injective
    V RationalAdele
  exact congrArg Subtype.val hab

/-- Exactness of the literal rational diagonal sequence. -/
private theorem range_rationalIdeleDiagonalToGSpin_eq_ker :
    V.rationalIdeleDiagonalToGSpin.range =
      V.rationalGSpinDiagonalToSO.ker := by
  ext gamma
  constructor
  · rintro ⟨eta, rfl⟩
    change V.rationalGSpinDiagonalToSO
      (V.rationalIdeleDiagonalToGSpin eta) = 1
    apply Subtype.ext
    change V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
        (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele eta) = 1
    have heta : CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
        V RationalAdele eta ∈
          (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
            V RationalAdele).ker := by
      rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom
        V RationalAdele]
      exact ⟨eta, rfl⟩
    exact heta
  · intro hgamma
    rcases gamma.2 with ⟨g, hg⟩
    have hproj : CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
        V ℚ g = 1 := by
      apply V.rationalSpecialOrthogonalFullAdelicDiagonalHom_injective
      calc
        V.rationalSpecialOrthogonalFullAdelicDiagonalHom
            (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V ℚ g) =
            V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
              (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom g) :=
          (V.rational_fullAdelic_diagonal_generalSpinToSpecialOrthogonal g).symm
        _ = V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom gamma := by
          rw [hg]
        _ = 1 := congrArg Subtype.val hgamma
        _ = V.rationalSpecialOrthogonalFullAdelicDiagonalHom 1 := by simp
    have hgker : g ∈
        (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V ℚ).ker :=
      hproj
    rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom
      V ℚ] at hgker
    rcases hgker with ⟨q, hq⟩
    let eta : IdeleDiagonal :=
      ⟨rationalUnitFullAdelicDiagonalHom q, ⟨q, rfl⟩⟩
    refine ⟨eta, ?_⟩
    apply Subtype.ext
    change CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
        V RationalAdele (rationalUnitFullAdelicDiagonalHom q) = gamma
    calc
      CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele (rationalUnitFullAdelicDiagonalHom q) =
          V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ q) :=
        V.rational_fullAdelic_diagonal_generalSpinScalar q
      _ = V.rationalCliffordGeneralSpinFullAdelicDiagonalHom g := by rw [hq]
      _ = gamma := hg

/-- A definition-only rational diagonal lift of an `SO` diagonal point. -/
private def rationalSODiagonalLift (delta : V.SODiagonal) : V.GSpinDiagonal :=
  Classical.choose (V.rationalGSpinDiagonalToSO_surjective delta)

@[simp] private theorem rationalSODiagonalLift_spec (delta : V.SODiagonal) :
    V.rationalGSpinDiagonalToSO (V.rationalSODiagonalLift delta) = delta :=
  Classical.choose_spec (V.rationalGSpinDiagonalToSO_surjective delta)

/-- The unique central diagonal coordinate left after removing the chosen
`SO` lift. -/
private def rationalGSpinDiagonalCentralCoordinate
    (gamma : V.GSpinDiagonal) : IdeleDiagonal :=
  Classical.choose (by
    have hk : gamma * (V.rationalSODiagonalLift
        (V.rationalGSpinDiagonalToSO gamma))⁻¹ ∈
        V.rationalGSpinDiagonalToSO.ker := by
      change V.rationalGSpinDiagonalToSO
          (gamma * (V.rationalSODiagonalLift
            (V.rationalGSpinDiagonalToSO gamma))⁻¹) = 1
      rw [map_mul, map_inv, V.rationalSODiagonalLift_spec]
      simp
    rw [← V.range_rationalIdeleDiagonalToGSpin_eq_ker] at hk
    exact hk)

private theorem rationalGSpinDiagonalCentralCoordinate_spec
    (gamma : V.GSpinDiagonal) :
    V.rationalIdeleDiagonalToGSpin
        (V.rationalGSpinDiagonalCentralCoordinate gamma) =
      gamma * (V.rationalSODiagonalLift
        (V.rationalGSpinDiagonalToSO gamma))⁻¹ :=
  Classical.choose_spec (by
    have hk : gamma * (V.rationalSODiagonalLift
        (V.rationalGSpinDiagonalToSO gamma))⁻¹ ∈
        V.rationalGSpinDiagonalToSO.ker := by
      change V.rationalGSpinDiagonalToSO
          (gamma * (V.rationalSODiagonalLift
            (V.rationalGSpinDiagonalToSO gamma))⁻¹) = 1
      rw [map_mul, map_inv, V.rationalSODiagonalLift_spec]
      simp
    rw [← V.range_rationalIdeleDiagonalToGSpin_eq_ker] at hk
    exact hk)

/-- Noncanonical but exact decomposition of the rational `GSpin` diagonal
into its rational scalar kernel and rational `SO` image. -/
private def rationalGSpinDiagonalEquivIdeleDiagonalProdSO :
    V.GSpinDiagonal ≃ IdeleDiagonal × V.SODiagonal where
  toFun gamma :=
    (V.rationalGSpinDiagonalCentralCoordinate gamma,
      V.rationalGSpinDiagonalToSO gamma)
  invFun p :=
    V.rationalIdeleDiagonalToGSpin p.1 * V.rationalSODiagonalLift p.2
  left_inv gamma := by
    apply Subtype.ext
    have h := congrArg Subtype.val
      (V.rationalGSpinDiagonalCentralCoordinate_spec gamma)
    change
      (V.rationalIdeleDiagonalToGSpin
          (V.rationalGSpinDiagonalCentralCoordinate gamma) :
        V.FullAdelicCliffordGeneralSpinGroup) *
          V.rationalSODiagonalLift (V.rationalGSpinDiagonalToSO gamma) = gamma
    rw [h]
    simp [mul_assoc]
  right_inv p := by
    have hker : V.rationalGSpinDiagonalToSO
        (V.rationalIdeleDiagonalToGSpin p.1) = 1 := by
      change V.rationalIdeleDiagonalToGSpin p.1 ∈
        V.rationalGSpinDiagonalToSO.ker
      rw [← V.range_rationalIdeleDiagonalToGSpin_eq_ker]
      exact ⟨p.1, rfl⟩
    have hproj : V.rationalGSpinDiagonalToSO
        (V.rationalIdeleDiagonalToGSpin p.1 *
          V.rationalSODiagonalLift p.2) = p.2 := by
      rw [map_mul, hker, V.rationalSODiagonalLift_spec, one_mul]
    apply Prod.ext
    · apply V.rationalIdeleDiagonalToGSpin_injective
      rw [V.rationalGSpinDiagonalCentralCoordinate_spec]
      rw [hproj]
      simp
    · exact hproj

@[simp] private theorem rationalGSpinDiagonalEquivIdeleDiagonalProdSO_symm_coe
    (eta : IdeleDiagonal) (delta : V.SODiagonal) :
    ((V.rationalGSpinDiagonalEquivIdeleDiagonalProdSO).symm (eta, delta) :
        V.FullAdelicCliffordGeneralSpinGroup) =
      CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele eta *
        (V.rationalSODiagonalLift delta :
          V.FullAdelicCliffordGeneralSpinGroup) :=
  rfl

@[simp] private theorem rationalGSpinDiagonalEquivIdeleDiagonalProdSO_symm
    (eta : IdeleDiagonal) (delta : V.SODiagonal) :
    (V.rationalGSpinDiagonalEquivIdeleDiagonalProdSO).symm (eta, delta) =
      V.rationalIdeleDiagonalToGSpin eta *
        V.rationalSODiagonalLift delta :=
  rfl

/-- Reindexing the rational `GSpin` diagonal by the literal rational scalar
kernel and the rational `SO` image. -/
private theorem tsum_rationalGSpinDiagonal_eq_tsum_idele_so
    (F : V.GSpinDiagonal → ℝ≥0∞) :
    (∑' gamma : V.GSpinDiagonal, F gamma) =
      ∑' delta : V.SODiagonal, ∑' eta : IdeleDiagonal,
        F (V.rationalIdeleDiagonalToGSpin eta *
          V.rationalSODiagonalLift delta) := by
  calc
    (∑' gamma : V.GSpinDiagonal, F gamma) =
        ∑' p : IdeleDiagonal × V.SODiagonal,
          F ((V.rationalGSpinDiagonalEquivIdeleDiagonalProdSO).symm p) :=
      (V.rationalGSpinDiagonalEquivIdeleDiagonalProdSO.symm.tsum_eq F).symm
    _ = ∑' eta : IdeleDiagonal, ∑' delta : V.SODiagonal,
          F (V.rationalIdeleDiagonalToGSpin eta *
            V.rationalSODiagonalLift delta) := by
      rw [ENNReal.tsum_prod']
      simp
    _ = ∑' delta : V.SODiagonal, ∑' eta : IdeleDiagonal,
          F (V.rationalIdeleDiagonalToGSpin eta *
            V.rationalSODiagonalLift delta) := ENNReal.tsum_comm

/-! ## Unfolding the central rational diagonal -/

/-- The inner rational-scalar sum is exactly unfolded by the certified
differential idele fundamental domain. -/
private theorem lintegral_ideleDiagonal_periodization
    (delta : V.SODiagonal)
    (x : V.FullAdelicCliffordGeneralSpinGroup)
    (f : V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ a in rationalIdeleMeasurableFundamentalDomain,
        ∑' eta : IdeleDiagonal,
          f ((V.rationalSODiagonalLift delta :
                V.FullAdelicCliffordGeneralSpinGroup) *
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele
                (eta : RationalAdeleˣ) *
              (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele
                a * x)))
      ∂rationalIdeleDifferentialHaarMeasure =
      ∫⁻ a,
        f ((V.rationalSODiagonalLift delta :
              V.FullAdelicCliffordGeneralSpinGroup) *
          CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x)
        ∂rationalIdeleDifferentialHaarMeasure := by
  let phi : RationalAdeleˣ → ℝ≥0∞ := fun a ↦
    f ((V.rationalSODiagonalLift delta :
          V.FullAdelicCliffordGeneralSpinGroup) *
      CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x)
  have hphi : Measurable phi := by
    exact hf.comp
      (continuous_const.mul
        (V.continuous_fullAdelicCliffordGeneralSpinScalarGroupHom.comp
          continuous_id) |>.mul continuous_const).measurable
  have h :=
    lintegral_restrict_leftPeriodize_eq_lintegral_of_isFundamentalDomain
      (Gamma := IdeleDiagonal)
      (μG := rationalIdeleDifferentialHaarMeasure)
      (F := rationalIdeleMeasurableFundamentalDomain)
      hphi rationalIdeleDifferentialHaar_isFundamentalDomain
  change
    (∫⁻ a in rationalIdeleMeasurableFundamentalDomain,
      ∑' eta : IdeleDiagonal, phi ((eta : RationalAdeleˣ) * a)
      ∂rationalIdeleDifferentialHaarMeasure) =
      ∫⁻ a, phi a ∂rationalIdeleDifferentialHaarMeasure at h
  simpa only [phi, map_mul, mul_assoc] using h

/-- Integrating the rational `GSpin` periodization across the differential
idele transversal leaves exactly the rational `SO` periodization of the
ambient differential central-orbit integral. -/
private theorem lintegral_leftPreperiodize_over_ideleDomain
    (x : V.FullAdelicCliffordGeneralSpinGroup)
    (f : V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ a in rationalIdeleMeasurableFundamentalDomain,
        leftPreperiodize V.GSpinDiagonal f
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x)
        ∂rationalIdeleDifferentialHaarMeasure =
      ∑' delta : V.SODiagonal,
        ∫⁻ a,
          f ((V.rationalSODiagonalLift delta :
                V.FullAdelicCliffordGeneralSpinGroup) *
            CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x)
          ∂rationalIdeleDifferentialHaarMeasure := by
  have hterm : ∀ gamma : V.GSpinDiagonal,
      AEMeasurable (fun a : RationalAdeleˣ ↦
        f ((gamma : V.FullAdelicCliffordGeneralSpinGroup) *
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x)))
        (rationalIdeleDifferentialHaarMeasure.restrict
          rationalIdeleMeasurableFundamentalDomain) := by
    intro gamma
    exact (hf.comp
      (continuous_const.mul
        ((V.continuous_fullAdelicCliffordGeneralSpinScalarGroupHom.comp
          continuous_id).mul continuous_const)).measurable).aemeasurable
  calc
    ∫⁻ a in rationalIdeleMeasurableFundamentalDomain,
        leftPreperiodize V.GSpinDiagonal f
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x)
        ∂rationalIdeleDifferentialHaarMeasure =
      ∑' gamma : V.GSpinDiagonal,
        ∫⁻ a in rationalIdeleMeasurableFundamentalDomain,
          f ((gamma : V.FullAdelicCliffordGeneralSpinGroup) *
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x))
          ∂rationalIdeleDifferentialHaarMeasure := by
      change
        (∫⁻ a in rationalIdeleMeasurableFundamentalDomain,
          ∑' gamma : V.GSpinDiagonal,
            f ((gamma : V.FullAdelicCliffordGeneralSpinGroup) *
              (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
                V RationalAdele a * x))
          ∂rationalIdeleDifferentialHaarMeasure) = _
      rw [lintegral_tsum hterm]
    _ = ∑' delta : V.SODiagonal, ∑' eta : IdeleDiagonal,
        ∫⁻ a in rationalIdeleMeasurableFundamentalDomain,
          f ((V.rationalSODiagonalLift delta :
                V.FullAdelicCliffordGeneralSpinGroup) *
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele
                (eta : RationalAdeleˣ) *
              (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x)))
          ∂rationalIdeleDifferentialHaarMeasure := by
      rw [V.tsum_rationalGSpinDiagonal_eq_tsum_idele_so]
      apply tsum_congr
      intro delta
      apply tsum_congr
      intro eta
      apply lintegral_congr
      intro a
      congr 1
      calc
        ((V.rationalIdeleDiagonalToGSpin eta *
              V.rationalSODiagonalLift delta : V.GSpinDiagonal) :
            V.FullAdelicCliffordGeneralSpinGroup) *
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x) =
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele
              (eta : RationalAdeleˣ) *
            (V.rationalSODiagonalLift delta :
              V.FullAdelicCliffordGeneralSpinGroup)) *
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x) := rfl
        _ = (V.rationalSODiagonalLift delta :
              V.FullAdelicCliffordGeneralSpinGroup) *
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele
                (eta : RationalAdeleˣ) *
              (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x)) := by
          rw [V.cliffordGeneralSpin_scalar_commutes RationalAdele
            (eta : RationalAdeleˣ) (V.rationalSODiagonalLift delta)]
          simp only [mul_assoc]
    _ = ∑' delta : V.SODiagonal,
        ∫⁻ a,
          f ((V.rationalSODiagonalLift delta :
                V.FullAdelicCliffordGeneralSpinGroup) *
            CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x)
          ∂rationalIdeleDifferentialHaarMeasure := by
      apply tsum_congr
      intro delta
      rw [← lintegral_tsum]
      · exact V.lintegral_ideleDiagonal_periodization delta x f hf
      · intro eta
        exact (hf.comp
          (continuous_const.mul
            (continuous_const.mul
              ((V.continuous_fullAdelicCliffordGeneralSpinScalarGroupHom.comp
                continuous_id).mul continuous_const))).measurable).aemeasurable

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 400000

private theorem projection_rationalSODiagonalLift
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (delta : L.rationalQuadraticSpaceMatrix.SODiagonal) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
        (L.rationalQuadraticSpaceMatrix.rationalSODiagonalLift delta) =
      (delta :
        L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) := by
  exact congrArg Subtype.val
    (L.rationalQuadraticSpaceMatrix.rationalSODiagonalLift_spec delta)

/-- A rational `SO` translate of the ambient central fiber is the literal
differential scalar orbit through the corresponding rational `GSpin` lift. -/
private theorem lintegral_centralFiberAtSO_diagonal_mul_projection
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (delta : L.rationalQuadraticSpaceMatrix.SODiagonal)
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup →
      ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ y, f y
        ∂L.fullAdelicDifferentialCentralFiberKernelAtSO
          ((delta :
              L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) *
            L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
              x) =
      ∫⁻ a,
        f ((L.rationalQuadraticSpaceMatrix.rationalSODiagonalLift delta :
              L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) *
          CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            L.rationalQuadraticSpaceMatrix RationalAdele a * x)
        ∂rationalIdeleDifferentialHaarMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  let xdelta : V.FullAdelicCliffordGeneralSpinGroup :=
    (V.rationalSODiagonalLift delta :
      V.FullAdelicCliffordGeneralSpinGroup) * x
  have hproj :
      (delta : V.FullAdelicSpecialOrthogonalGroup) *
          V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x =
        V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom xdelta := by
    rw [map_mul, L.projection_rationalSODiagonalLift]
  rw [hproj, L.fullAdelicDifferentialCentralFiberKernelAtSO_comp_projection,
    V.fullAdelicDifferentialCentralFiberKernel_apply]
  have horbit : Measurable (fun a : RationalAdeleˣ ↦
      CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a *
        xdelta) :=
    ((V.continuous_fullAdelicCliffordGeneralSpinScalarGroupHom.comp
      continuous_id).mul continuous_const).measurable
  rw [lintegral_map' hf.aemeasurable horbit.aemeasurable]
  apply lintegral_congr
  intro a
  congr 1
  change
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a *
        ((V.rationalSODiagonalLift delta :
          V.FullAdelicCliffordGeneralSpinGroup) * x) =
      (V.rationalSODiagonalLift delta :
          V.FullAdelicCliffordGeneralSpinGroup) *
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x
  rw [← mul_assoc,
    V.cliffordGeneralSpin_scalar_commutes RationalAdele a
      (V.rationalSODiagonalLift delta), mul_assoc]

/-- The measurable ambient `SO` function obtained by integrating a fixed
test function over the descended differential central fiber. -/
private noncomputable def differentialCentralFiberLIntegral
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup →
      ℝ≥0∞) :
    L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup → ℝ≥0∞ :=
  fun h ↦ ∫⁻ x, f x ∂L.fullAdelicDifferentialCentralFiberKernelAtSO h

private theorem measurable_differentialCentralFiberLIntegral
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup →
      ℝ≥0∞)
    (hf : Measurable f) :
    Measurable (L.differentialCentralFiberLIntegral f) := by
  exact hf.lintegral_kernel

/-- Pointwise crossed-periodization identity on an ambient representative:
the differential idele quotient of the rational `GSpin` periodization is the
rational `SO` periodization of the descended central-fiber integral. -/
private theorem lintegral_horizontalDifferentialWeil_periodization_mk
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (x : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup)
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup →
      ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ z,
        leftPeriodize
          L.rationalQuadraticSpaceMatrix.GSpinDiagonal f z
        ∂L.horizontalDifferentialWeilFiberKernelAtSO inst
          (L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientMap
            (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
              x)) =
      leftPeriodize L.rationalQuadraticSpaceMatrix.SODiagonal
        (L.differentialCentralFiberLIntegral f)
        (L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalLeftQuotientMap
          (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
            x)) := by
  let V := L.rationalQuadraticSpaceMatrix
  letI : Countable V.GSpinDiagonal :=
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup_countable
  have hpre : Measurable (leftPreperiodize V.GSpinDiagonal f) :=
    leftPreperiodize_measurable_of_countable V.GSpinDiagonal hf
  have hperiod : Measurable (leftPeriodize V.GSpinDiagonal f) :=
    leftPeriodize_measurable_map_of_leftPreperiodize V.GSpinDiagonal hpre
  have hhorizontal :
      V.fullAdelicSpecialOrthogonalLeftQuotientMap
          (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x) =
        V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal
          (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x) := by
    exact (V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_mk x).symm
  rw [hhorizontal,
    L.horizontalDifferentialWeilFiberKernelAtSO_comp_horizontalMap]
  rw [V.lintegral_horizontalDifferentialWeilFiberMeasure_mk x _ hperiod]
  change
    (∫⁻ a in rationalIdeleMeasurableFundamentalDomain,
      leftPreperiodize V.GSpinDiagonal f
        (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele a * x)
      ∂rationalIdeleDifferentialHaarMeasure) = _
  rw [V.lintegral_leftPreperiodize_over_ideleDomain x f hf]
  change
    (∑' delta : V.SODiagonal,
      ∫⁻ a,
        f ((V.rationalSODiagonalLift delta :
              V.FullAdelicCliffordGeneralSpinGroup) *
          CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a * x)
        ∂rationalIdeleDifferentialHaarMeasure) =
      ∑' delta : V.SODiagonal,
        L.differentialCentralFiberLIntegral f
          ((delta : V.FullAdelicSpecialOrthogonalGroup) *
            V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x)
  apply tsum_congr
  intro delta
  exact (L.lintegral_centralFiberAtSO_diagonal_mul_projection
    delta x f hf).symm

/-- Quotient-valued form of the pointwise crossed-periodization identity. -/
private theorem lintegral_horizontalDifferentialWeil_periodization
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (q : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient)
    (f : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup →
      ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ z,
        leftPeriodize
          L.rationalQuadraticSpaceMatrix.GSpinDiagonal f z
        ∂L.horizontalDifferentialWeilFiberKernelAtSO inst q =
      leftPeriodize L.rationalQuadraticSpaceMatrix.SODiagonal
        (L.differentialCentralFiberLIntegral f) q := by
  induction q using Quot.inductionOn with
  | h h =>
      obtain ⟨x, hx⟩ :=
        L.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom_surjective h
      subst h
      exact L.lintegral_horizontalDifferentialWeil_periodization_mk
        inst x f hf

/-! ## The specialized iterated Weil identity -/

/-- The literal differential idele-class fibers bound over the raw lattice
`SO` quotient satisfy the measurable Weil formula for the actual lattice
ambient differential central-fiber bind. -/
theorem horizontalDifferentialWeilSOFiberBoundMeasure_isMeasurableWeil
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    IsLeftMeasurableWeilQuotientMeasure
      L.rationalQuadraticSpaceMatrix.GSpinDiagonal
      (L.fullAdelicDifferentialCentralFiberBoundMeasure P)
      (L.horizontalDifferentialWeilSOFiberBoundMeasure inst
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv).specialOrthogonalData.quotientMeasure) where
  lintegral_leftPeriodize_eq f hf := by
    let V := L.rationalQuadraticSpaceMatrix
    let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L hn inst hP hconv
    let k := L.differentialCentralFiberLIntegral f
    have hk : Measurable k :=
      L.measurable_differentialCentralFiberLIntegral f hf
    have hpre : Measurable (leftPreperiodize V.GSpinDiagonal f) := by
      letI : Countable V.GSpinDiagonal :=
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup_countable
      exact leftPreperiodize_measurable_of_countable V.GSpinDiagonal hf
    have hperiod : Measurable (leftPeriodize V.GSpinDiagonal f) :=
      leftPeriodize_measurable_map_of_leftPreperiodize V.GSpinDiagonal hpre
    calc
      ∫⁻ z, leftPeriodize V.GSpinDiagonal f z
          ∂L.horizontalDifferentialWeilSOFiberBoundMeasure inst
            D.specialOrthogonalData.quotientMeasure =
        ∫⁻ q, ∫⁻ z, leftPeriodize V.GSpinDiagonal f z
            ∂L.horizontalDifferentialWeilFiberKernelAtSO inst q
          ∂D.specialOrthogonalData.quotientMeasure := by
        rw [horizontalDifferentialWeilSOFiberBoundMeasure,
          Measure.lintegral_bind
            (L.horizontalDifferentialWeilFiberKernelAtSO inst).aemeasurable
            hperiod.aemeasurable]
      _ = ∫⁻ q, leftPeriodize V.SODiagonal k q
          ∂D.specialOrthogonalData.quotientMeasure := by
        apply lintegral_congr
        intro q
        exact L.lintegral_horizontalDifferentialWeil_periodization
          inst q f hf
      _ = ∫⁻ h, k h
          ∂D.specialOrthogonalData.adelicMeasure :=
        D.specialOrthogonalData.isMeasurableWeilQuotientMeasure
          |>.lintegral_leftPeriodize_eq k hk
      _ = ∫⁻ h, ∫⁻ x, f x
            ∂L.fullAdelicDifferentialCentralFiberKernelAtSO h
          ∂L.rationalQuadraticSpaceMatrixFullAdelicDifferentialMeasure P := by
        rfl
      _ = ∫⁻ x, f x
          ∂L.fullAdelicDifferentialCentralFiberBoundMeasure P :=
        (L.lintegral_fullAdelicDifferentialCentralFiberBoundMeasure
          P f hf).symm

/-- The specialized central-extension Weil identity: binding the actual
differential idele-class quotient fibers over the raw lattice `SO` quotient
is exactly the quotient measure induced from the lattice ambient differential
central-fiber bind on the rational `GSpin` quotient. -/
theorem horizontalDifferentialWeilSOFiberBoundMeasure_eq_ambientQuotient
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hn : 3 ≤ r + 2)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    L.horizontalDifferentialWeilSOFiberBoundMeasure inst
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv).specialOrthogonalData.quotientMeasure =
      (L.fullAdelicDifferentialCentralFiberMeasurableWeilData
        hP S).quotientMeasure := by
  let V := L.rationalQuadraticSpaceMatrix
  let Q : V.CliffordGeneralSpinMeasurableWeilMeasureData :=
    { adelicMeasure := L.fullAdelicDifferentialCentralFiberBoundMeasure P
      quotientMeasure :=
        L.horizontalDifferentialWeilSOFiberBoundMeasure inst
          (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
            L hn inst hP hconv).specialOrthogonalData.quotientMeasure
      isMeasurableWeilQuotientMeasure :=
        L.horizontalDifferentialWeilSOFiberBoundMeasure_isMeasurableWeil
          hn inst hP hconv }
  calc
    L.horizontalDifferentialWeilSOFiberBoundMeasure inst
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv).specialOrthogonalData.quotientMeasure =
      leftQuotientFundamentalDomainMeasure V.GSpinDiagonal
        (L.fullAdelicDifferentialCentralFiberBoundMeasure P)
        V.fullAdelicCliffordGeneralSpinMeasurableFundamentalDomain :=
      Q.quotientMeasure_eq_fundamentalDomain V
    _ = (L.fullAdelicDifferentialCentralFiberMeasurableWeilData
          hP S).quotientMeasure :=
      (L.fullAdelicDifferentialCentralFiberQuotientMeasure_eq_fundamentalDomain
        hP S).symm

end PositiveDefiniteIntegralLattice

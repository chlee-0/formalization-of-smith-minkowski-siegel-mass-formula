import SMSFormula.RationalCliffordGeneralSpinVerticalFiberQuotientPeriodized

/-!
# Rational-diagonal reindexing for the vertical Spin disintegration

The rational Spin diagonal embeds faithfully in the rational `GSpin`
diagonal.  Its image is packaged as a literal subgroup, and the standard
coset--subgroup equivalence reindexes every nonnegative sum over rational
`GSpin` points as a sum over Spin-diagonal cosets followed by a sum over the
rational Spin diagonal.

This is the algebraic reindexing required before applying the raw Spin Weil
identity to the periodized vertical Tonelli formula.  It does not identify the
coset carrier with rational ideles, choose an adelic representative, apply a
measure identity, or introduce a normalization coefficient.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

/-- The faithful inclusion of the literal rational Spin diagonal into the
literal rational `GSpin` diagonal. -/
def rationalCliffordSpinCandidateDiagonalToGeneralSpin :
    V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup →*
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup where
  toFun sigma := by
    refine ⟨V.fullAdelicCliffordSpinCandidateToGeneralSpinHom sigma, ?_⟩
    rcases sigma.2 with ⟨s, hs⟩
    refine ⟨V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ s, ?_⟩
    calc
      V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
          (V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ s) =
        V.fullAdelicCliffordSpinCandidateToGeneralSpinHom
          (V.rationalCliffordSpinCandidateFullAdelicDiagonalHom s) :=
        (V.rational_fullAdelic_diagonal_candidateToGeneralSpin s).symm
      _ = V.fullAdelicCliffordSpinCandidateToGeneralSpinHom sigma :=
        congrArg V.fullAdelicCliffordSpinCandidateToGeneralSpinHom hs
  map_one' := by
    apply Subtype.ext
    exact map_one V.fullAdelicCliffordSpinCandidateToGeneralSpinHom
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul V.fullAdelicCliffordSpinCandidateToGeneralSpinHom
      (x : V.FullAdelicCliffordSpinCandidateGroup) y

theorem rationalCliffordSpinCandidateDiagonalToGeneralSpin_injective :
    Function.Injective V.rationalCliffordSpinCandidateDiagonalToGeneralSpin := by
  intro x y hxy
  apply Subtype.ext
  exact V.cliffordSpinCandidateToCliffordGeneralSpinHom_injective RationalAdele
    (congrArg Subtype.val hxy)

/-- Scalar extension identifies rational Spin points with their literal
full-adelic diagonal subgroup. -/
def rationalCliffordSpinCandidateGroupEquivDiagonal :
    V.RationalCliffordSpinCandidateGroup ≃*
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup :=
  MulEquiv.ofBijective
    (V.rationalCliffordSpinCandidateFullAdelicDiagonalHom.codRestrict
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
      (fun s => ⟨s, rfl⟩))
    ⟨(fun _ _ h =>
        V.rationalCliffordSpinCandidateFullAdelicDiagonalHom_injective
          (congrArg Subtype.val h)), by
      intro sigma
      rcases sigma.2 with ⟨s, hs⟩
      exact ⟨s, Subtype.ext hs⟩⟩

/-- Scalar extension identifies rational `GSpin` points with their literal
full-adelic diagonal subgroup. -/
def rationalCliffordGeneralSpinGroupEquivDiagonal :
    V.RationalCliffordGeneralSpinGroup ≃*
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
  MulEquiv.ofBijective
    (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom.codRestrict
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
      (fun g => ⟨g, rfl⟩))
    ⟨(fun _ _ h =>
        V.rationalCliffordGeneralSpinFullAdelicDiagonalHom_injective
          (congrArg Subtype.val h)), by
      intro gamma
      rcases gamma.2 with ⟨g, hg⟩
      exact ⟨g, Subtype.ext hg⟩⟩

/-- The rational Spin-to-`GSpin` inclusion commutes with the two exact
diagonal equivalences. -/
theorem rationalSpinGeneralSpinGroupEquivDiagonal_commute
    (s : V.RationalCliffordSpinCandidateGroup) :
    V.rationalCliffordGeneralSpinGroupEquivDiagonal
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ s) =
      V.rationalCliffordSpinCandidateDiagonalToGeneralSpin
        (V.rationalCliffordSpinCandidateGroupEquivDiagonal s) := by
  apply Subtype.ext
  exact (V.rational_fullAdelic_diagonal_candidateToGeneralSpin s).symm

/-- The rational Spin diagonal viewed as its actual subgroup of the rational
`GSpin` diagonal. -/
def rationalCliffordSpinCandidateDiagonalImageInGeneralSpin :
    Subgroup V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
  V.rationalCliffordSpinCandidateDiagonalToGeneralSpin.range

/-- Rational similitude transported to the literal rational `GSpin`
diagonal. -/
def rationalCliffordGeneralSpinDiagonalSimilitudeHom :
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup →* ℚˣ :=
  (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ).comp
    V.rationalCliffordGeneralSpinGroupEquivDiagonal.symm.toMonoidHom

/-- On the rational diagonal, the represented Spin image is exactly the
kernel of rational similitude. -/
theorem range_rationalCliffordSpinCandidateDiagonalToGeneralSpin_eq_ker :
    V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin =
      V.rationalCliffordGeneralSpinDiagonalSimilitudeHom.ker := by
  ext gamma
  constructor
  · rintro ⟨sigma, rfl⟩
    let s := V.rationalCliffordSpinCandidateGroupEquivDiagonal.symm sigma
    have heq :
        V.rationalCliffordGeneralSpinGroupEquivDiagonal.symm
            (V.rationalCliffordSpinCandidateDiagonalToGeneralSpin sigma) =
          V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ s := by
      apply V.rationalCliffordGeneralSpinGroupEquivDiagonal.injective
      rw [V.rationalCliffordGeneralSpinGroupEquivDiagonal.apply_symm_apply]
      rw [V.rationalSpinGeneralSpinGroupEquivDiagonal_commute]
      simp only [s, MulEquiv.apply_symm_apply]
    change V.rationalCliffordGeneralSpinDiagonalSimilitudeHom
        (V.rationalCliffordSpinCandidateDiagonalToGeneralSpin sigma) = 1
    change CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ
        (V.rationalCliffordGeneralSpinGroupEquivDiagonal.symm
          (V.rationalCliffordSpinCandidateDiagonalToGeneralSpin sigma)) = 1
    rw [heq]
    simp [CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom,
      CliffordGeneralSpinIntrinsicPoint.similitudeMonoidHom]
  · intro hgamma
    change CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ
        (V.rationalCliffordGeneralSpinGroupEquivDiagonal.symm gamma) = 1 at hgamma
    have hker : V.rationalCliffordGeneralSpinGroupEquivDiagonal.symm gamma ∈
        (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ).ker :=
      hgamma
    rw [← V.range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker ℚ] at hker
    rcases hker with ⟨s, hs⟩
    refine ⟨V.rationalCliffordSpinCandidateGroupEquivDiagonal s, ?_⟩
    calc
      V.rationalCliffordSpinCandidateDiagonalToGeneralSpin
          (V.rationalCliffordSpinCandidateGroupEquivDiagonal s) =
        V.rationalCliffordGeneralSpinGroupEquivDiagonal
          (V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ s) :=
        (V.rationalSpinGeneralSpinGroupEquivDiagonal_commute s).symm
      _ = V.rationalCliffordGeneralSpinGroupEquivDiagonal
          (V.rationalCliffordGeneralSpinGroupEquivDiagonal.symm gamma) :=
        congrArg V.rationalCliffordGeneralSpinGroupEquivDiagonal hs
      _ = gamma := V.rationalCliffordGeneralSpinGroupEquivDiagonal.apply_symm_apply gamma

local instance rationalCliffordSpinCandidateDiagonalImageNormal :
    (V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin).Normal := by
  rw [V.range_rationalCliffordSpinCandidateDiagonalToGeneralSpin_eq_ker]
  infer_instance

/-- The remaining rational-diagonal coset coordinate is exactly the range of
rational `GSpin` similitude. -/
def rationalGeneralSpinDiagonalQuotientEquivSimilitudeRange :
    V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
        V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin ≃*
      V.rationalCliffordGeneralSpinDiagonalSimilitudeHom.range :=
  (QuotientGroup.quotientMulEquivOfEq
      V.range_rationalCliffordSpinCandidateDiagonalToGeneralSpin_eq_ker).trans
    (QuotientGroup.quotientKerEquivRange
      V.rationalCliffordGeneralSpinDiagonalSimilitudeHom)

/-- The rational Spin diagonal is equivalent to its literal image subgroup
inside the rational `GSpin` diagonal. -/
def rationalCliffordSpinCandidateDiagonalEquivImageInGeneralSpin :
    V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup ≃
      V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin :=
  Equiv.ofInjective V.rationalCliffordSpinCandidateDiagonalToGeneralSpin
    V.rationalCliffordSpinCandidateDiagonalToGeneralSpin_injective

/-- Reindex the rational `GSpin` diagonal first by left cosets of the rational
Spin image and then by the literal rational Spin diagonal. -/
theorem tsum_rationalCliffordGeneralSpinDiagonal_eq_coset_spin
    (F : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup → ℝ≥0∞) :
    (∑' gamma, F gamma) =
      ∑' xi :
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
            V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin,
        ∑' sigma : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
          F ((Subgroup.groupEquivQuotientProdSubgroup
                (s := V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin)).symm
              (xi,
                V.rationalCliffordSpinCandidateDiagonalEquivImageInGeneralSpin sigma)) := by
  let H := V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin
  let e : V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ≃
      (V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸ H) × H :=
    Subgroup.groupEquivQuotientProdSubgroup
  calc
    (∑' gamma, F gamma) = ∑' p, F (e.symm p) :=
      (e.symm.tsum_eq F).symm
    _ = ∑' xi, ∑' h : H, F (e.symm (xi, h)) := by
      rw [ENNReal.tsum_prod']
    _ = ∑' xi,
        ∑' sigma : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
          F (e.symm
            (xi, V.rationalCliffordSpinCandidateDiagonalEquivImageInGeneralSpin sigma)) := by
      apply tsum_congr
      intro xi
      exact
        (V.rationalCliffordSpinCandidateDiagonalEquivImageInGeneralSpin.tsum_eq
          (fun h : H => F (e.symm (xi, h)))).symm

/-- Ambient-function form of the exact rational-diagonal reindexing. -/
theorem leftPreperiodize_rationalCliffordGeneralSpinDiagonal_eq_coset_spin
    (f : V.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞)
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    leftPreperiodize
        V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f x =
      ∑' xi :
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
            V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin,
        ∑' sigma : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
          f (((Subgroup.groupEquivQuotientProdSubgroup
                  (s := V.rationalCliffordSpinCandidateDiagonalImageInGeneralSpin)).symm
                (xi,
                  V.rationalCliffordSpinCandidateDiagonalEquivImageInGeneralSpin sigma) :
              V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) * x) := by
  exact V.tsum_rationalCliffordGeneralSpinDiagonal_eq_coset_spin
    (fun gamma => f ((gamma : V.FullAdelicCliffordGeneralSpinGroup) * x))

end RationalQuadraticSpaceMatrix

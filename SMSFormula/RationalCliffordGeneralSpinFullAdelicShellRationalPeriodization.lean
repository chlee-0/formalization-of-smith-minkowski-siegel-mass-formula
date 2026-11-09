import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellRationalFiberKernel
import SMSFormula.RationalCliffordGeneralSpinVerticalFiberQuotientHaar
import SMSFormula.RationalCliffordGeneralSpinVerticalRationalDiagonalReindexing

/-!
# Rational periodization along the full-adelic GSpin shell

The block rational diagonal is reindexed by right cosets of the certified
complement diagonal.  This identifies periodization of the crossed complement
quotient measure with the lower vertical scalar times the countable sum of raw
shell fibers.  The complement is not assumed normal, and no rational shell
representative or new adelic carrier is selected.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace Subgroup

variable {G : Type*} [Group G]

noncomputable def nonnormalRightQuotientProdEquiv (S : Subgroup G) :
    (G ⧸ S) × S ≃ G := by
  let f : (G ⧸ S) × S → G := fun cs => Quot.out cs.1 * cs.2.1
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨c, s⟩ ⟨d, t⟩ h
    have hc : QuotientGroup.mk (f (c, s)) = c := by
      change QuotientGroup.mk (Quot.out c * s.1) = c
      rw [← Quot.out_eq c]
      apply QuotientGroup.eq.mpr
      simp [s.2]
    have hd : QuotientGroup.mk (f (d, t)) = d := by
      change QuotientGroup.mk (Quot.out d * t.1) = d
      rw [← Quot.out_eq d]
      apply QuotientGroup.eq.mpr
      simp [t.2]
    have hcd : c = d := hc.symm.trans ((congrArg QuotientGroup.mk h).trans hd)
    subst d
    have hst : s = t := by
      apply Subtype.ext
      exact mul_left_cancel h
    exact congrArg (fun u => (c, u)) hst
  · intro g
    let c : G ⧸ S := QuotientGroup.mk g
    let s : S := ⟨(Quot.out c)⁻¹ * g, by
      apply QuotientGroup.eq.mp
      exact (Quot.out_eq c).trans rfl⟩
    refine ⟨(c, s), ?_⟩
    change Quot.out c * ((Quot.out c)⁻¹ * g) = g
    simp

end Subgroup

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

def nonisotropicLastComplementGeneralSpinDiagonalHom
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup →*
      (W.nonisotropicLastExtension a ha
        |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :=
  (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinGroupEquivDiagonal).toMonoidHom.comp
    ((W.nonisotropicLastComplementGeneralSpinPointHom a ha ℚ).comp
      W.rationalCliffordGeneralSpinGroupEquivDiagonal.symm.toMonoidHom)

theorem nonisotropicLastComplementGeneralSpinDiagonalHom_injective
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Function.Injective (W.nonisotropicLastComplementGeneralSpinDiagonalHom a ha) := by
  intro x y hxy
  apply W.rationalCliffordGeneralSpinGroupEquivDiagonal.symm.injective
  apply W.nonisotropicLastComplementGeneralSpinPointHom_injective a ha ℚ
  apply (W.nonisotropicLastExtension a ha
    |>.rationalCliffordGeneralSpinGroupEquivDiagonal).injective
  exact hxy

def nonisotropicLastComplementGeneralSpinDiagonalImage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Subgroup ((W.nonisotropicLastExtension a ha)
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :=
  (W.nonisotropicLastComplementGeneralSpinDiagonalHom a ha).range

def nonisotropicLastComplementGeneralSpinDiagonalEquivImage
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ≃
      W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha :=
  Equiv.ofInjective (W.nonisotropicLastComplementGeneralSpinDiagonalHom a ha)
    (W.nonisotropicLastComplementGeneralSpinDiagonalHom_injective a ha)

theorem nonisotropicLastComplementGeneralSpinDiagonalHom_coe
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (delta : W.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
    ((W.nonisotropicLastComplementGeneralSpinDiagonalHom a ha delta :
        (W.nonisotropicLastExtension a ha)
          |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup) =
      W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele
        (delta : W.FullAdelicCliffordGeneralSpinGroup) := by
  let q := W.rationalCliffordGeneralSpinGroupEquivDiagonal.symm delta
  simp only [nonisotropicLastComplementGeneralSpinDiagonalHom, MonoidHom.coe_comp,
    MulEquiv.coe_toMonoidHom, Function.comp_apply]
  change
    (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalHom)
        (W.nonisotropicLastComplementGeneralSpinPoint a ha ℚ q) =
      W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele
        (delta : W.FullAdelicCliffordGeneralSpinGroup)
  rw [show delta = W.rationalCliffordGeneralSpinGroupEquivDiagonal q by
    simp [q]]
  change
    (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalHom)
        (W.nonisotropicLastComplementGeneralSpinPoint a ha ℚ q) =
      W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele
        (W.rationalCliffordGeneralSpinFullAdelicDiagonalHom q)
  exact W.nonisotropicLastComplementGeneralSpinPoint_naturality
    a ha (Algebra.ofId ℚ RationalAdele) q

theorem nonisotropicLastComplementGeneralSpinDiagonalEquivImage_coe
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (delta : W.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
    ((((W.nonisotropicLastComplementGeneralSpinDiagonalEquivImage a ha delta :
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha) :
      (W.nonisotropicLastExtension a ha
        |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
      (W.nonisotropicLastExtension a ha
        |>.FullAdelicCliffordGeneralSpinGroup))) =
      W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele
        (delta : W.FullAdelicCliffordGeneralSpinGroup) := by
  exact W.nonisotropicLastComplementGeneralSpinDiagonalHom_coe a ha delta

theorem tsum_rationalCliffordGeneralSpinDiagonal_eq_shellCoset_complement
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (F : (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) → ℝ≥0∞) :
    (∑' gamma, F gamma) =
      ∑' xi :
          (W.nonisotropicLastExtension a ha
            |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
              W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha,
        ∑' delta : W.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
          F ((W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha
              |>.nonnormalRightQuotientProdEquiv)
            (xi, W.nonisotropicLastComplementGeneralSpinDiagonalEquivImage a ha delta)) := by
  let S := W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha
  let e := S.nonnormalRightQuotientProdEquiv
  calc
    (∑' gamma, F gamma) = ∑' p, F (e p) :=
      (e.tsum_eq F).symm
    _ = ∑' xi, ∑' h : S, F (e (xi, h)) := by
      rw [ENNReal.tsum_prod']
    _ = ∑' xi,
        ∑' delta : W.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup,
          F (e (xi, W.nonisotropicLastComplementGeneralSpinDiagonalEquivImage a ha delta)) := by
      apply tsum_congr
      intro xi
      exact (W.nonisotropicLastComplementGeneralSpinDiagonalEquivImage a ha).tsum_eq
        (fun h : S => F (e (xi, h))) |>.symm

def fullAdelicNonisotropicLastShellCosetComplementIntegrand
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (xi :
      (W.nonisotropicLastExtension a ha
        |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
          W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha)
    (f : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup) → ℝ≥0∞) :
    W.FullAdelicCliffordGeneralSpinGroup → ℝ≥0∞ :=
  fun y => f
    (((Quot.out xi :
        (W.nonisotropicLastExtension a ha
          |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
        (W.nonisotropicLastExtension a ha
          |>.FullAdelicCliffordGeneralSpinGroup)) *
      W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele y)

theorem leftPeriodize_block_complementQuotient_eq_shellCoset_tsum
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (q : W.FullAdelicCliffordGeneralSpinLeftQuotient)
    (f : (W.nonisotropicLastExtension a ha
      |>.FullAdelicCliffordGeneralSpinGroup) → ℝ≥0∞) :
    leftPeriodize
        (W.nonisotropicLastExtension a ha
          |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) f
        (W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
          a ha q) =
      ∑' xi :
          (W.nonisotropicLastExtension a ha
            |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
              W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha,
        leftPeriodize
          W.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
          (W.fullAdelicNonisotropicLastShellCosetComplementIntegrand a ha xi f) q := by
  induction q using Quot.inductionOn with
  | _ y =>
      change
        (∑' gamma :
            (W.nonisotropicLastExtension a ha
              |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup),
          f ((gamma :
              (W.nonisotropicLastExtension a ha
                |>.FullAdelicCliffordGeneralSpinGroup)) *
            W.nonisotropicLastComplementGeneralSpinPoint
              a ha RationalAdele y)) = _
      rw [W.tsum_rationalCliffordGeneralSpinDiagonal_eq_shellCoset_complement a ha]
      apply tsum_congr
      intro xi
      apply tsum_congr
      intro delta
      change
        f ((((W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha
                |>.nonnormalRightQuotientProdEquiv)
              (xi, W.nonisotropicLastComplementGeneralSpinDiagonalEquivImage a ha delta) :
            (W.nonisotropicLastExtension a ha
              |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
            (W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup)) *
          W.nonisotropicLastComplementGeneralSpinPoint
            a ha RationalAdele y) = _
      rw [show
        (((W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha
              |>.nonnormalRightQuotientProdEquiv)
            (xi, W.nonisotropicLastComplementGeneralSpinDiagonalEquivImage a ha delta) :
          (W.nonisotropicLastExtension a ha
            |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
          (W.nonisotropicLastExtension a ha
            |>.FullAdelicCliffordGeneralSpinGroup)) =
            ((Quot.out xi :
                (W.nonisotropicLastExtension a ha
                  |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
              (W.nonisotropicLastExtension a ha
                |>.FullAdelicCliffordGeneralSpinGroup)) *
              W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele
                (delta : W.FullAdelicCliffordGeneralSpinGroup) by
          change
            (((Quot.out xi :
                (W.nonisotropicLastExtension a ha
                  |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) *
              W.nonisotropicLastComplementGeneralSpinDiagonalEquivImage a ha delta :
                (W.nonisotropicLastExtension a ha
                  |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
              (W.nonisotropicLastExtension a ha
                |>.FullAdelicCliffordGeneralSpinGroup)) = _
          rw [Subgroup.coe_mul,
            W.nonisotropicLastComplementGeneralSpinDiagonalEquivImage_coe a ha delta]]
      unfold fullAdelicNonisotropicLastShellCosetComplementIntegrand
      change
        f (((Quot.out xi :
              (W.nonisotropicLastExtension a ha
                |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
              (W.nonisotropicLastExtension a ha
                |>.FullAdelicCliffordGeneralSpinGroup)) *
            (W.nonisotropicLastComplementGeneralSpinPointHom
              a ha RationalAdele)
                (delta : W.FullAdelicCliffordGeneralSpinGroup) *
            (W.nonisotropicLastComplementGeneralSpinPointHom
              a ha RationalAdele) y) =
          f (((Quot.out xi :
              (W.nonisotropicLastExtension a ha
                |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
              (W.nonisotropicLastExtension a ha
                |>.FullAdelicCliffordGeneralSpinGroup)) *
            (W.nonisotropicLastComplementGeneralSpinPointHom
              a ha RationalAdele)
                ((delta : W.FullAdelicCliffordGeneralSpinGroup) * y))
      rw [(W.nonisotropicLastComplementGeneralSpinPointHom
        a ha RationalAdele).map_mul]
      simp only [mul_assoc]

def fullAdelicNonisotropicLastShellCosetComplementPeriodizedMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (μ : Measure W.FullAdelicCliffordGeneralSpinLeftQuotient) :
    Measure
      (W.nonisotropicLastExtension a ha
        |>.FullAdelicCliffordGeneralSpinGroup) :=
  Measure.sum fun xi :
      (W.nonisotropicLastExtension a ha
        |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
          W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha =>
    Measure.map
      (fun y =>
        (((Quot.out xi :
            (W.nonisotropicLastExtension a ha
              |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
            (W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup)) *
          W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele y))
      (W.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ)

def fullAdelicNonisotropicLastShellCosetComplementTranslateSumMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (ν : Measure W.FullAdelicCliffordGeneralSpinGroup) :
    Measure
      (W.nonisotropicLastExtension a ha
        |>.FullAdelicCliffordGeneralSpinGroup) :=
  Measure.sum fun xi :
      (W.nonisotropicLastExtension a ha
        |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
          W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha =>
    Measure.map
      (fun y =>
        (((Quot.out xi :
            (W.nonisotropicLastExtension a ha
              |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
            (W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup)) *
          W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele y)) ν

theorem fullAdelicNonisotropicLastShellCosetComplementPeriodizedMeasure_eq_smul_translateSum
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (μ : Measure W.FullAdelicCliffordGeneralSpinLeftQuotient)
    (ν : Measure W.FullAdelicCliffordGeneralSpinGroup) (c : ℝ≥0∞)
    (hμ : W.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ = c • ν) :
    W.fullAdelicNonisotropicLastShellCosetComplementPeriodizedMeasure a ha μ =
      c • W.fullAdelicNonisotropicLastShellCosetComplementTranslateSumMeasure a ha ν := by
  rw [fullAdelicNonisotropicLastShellCosetComplementPeriodizedMeasure,
    fullAdelicNonisotropicLastShellCosetComplementTranslateSumMeasure, hμ]
  apply Measure.ext
  intro s hs
  rw [Measure.sum_apply _ hs, Measure.smul_apply, Measure.sum_apply _ hs]
  simp_rw [Measure.map_smul, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_mul_left

/-- The raw orbit fiber descended to the rational shell right-coset type.
No representative occurs in the resulting measure-valued function. -/
noncomputable def fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    ((W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha) →
      Measure (W.nonisotropicLastExtension a ha
        |>.FullAdelicCliffordGeneralSpinGroup) :=
  Quotient.lift
    (fun gamma : (W.nonisotropicLastExtension a ha
        |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) =>
      W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel a ha
        (gamma : W.nonisotropicLastExtension a ha
          |>.FullAdelicCliffordGeneralSpinGroup)) (by
      intro gamma delta hrel
      change QuotientGroup.leftRel
        (W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha)
          gamma delta at hrel
      rw [QuotientGroup.leftRel_apply] at hrel
      let s : W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha :=
        ⟨gamma⁻¹ * delta, hrel⟩
      rcases s.2 with ⟨lower, hlower⟩
      let k : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha :=
        W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
          a ha RationalAdele
          (lower : W.FullAdelicCliffordGeneralSpinGroup)
      have hs :
          ((s.1 : (W.nonisotropicLastExtension a ha
              |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
            (W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup)) = k.1 := by
        rw [show s.1 =
            W.nonisotropicLastComplementGeneralSpinDiagonalHom a ha lower by
          exact hlower.symm]
        rw [W.nonisotropicLastComplementGeneralSpinDiagonalHom_coe a ha lower]
        rfl
      have hdelta :
          (delta : (W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup)) =
            (gamma : (W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup)) * k.1 := by
        rw [← hs]
        rw [show s.1 = gamma⁻¹ * delta by rfl]
        simp
      change
        W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel a ha
            (gamma : W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup) =
          W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel a ha
            (delta : W.nonisotropicLastExtension a ha
              |>.FullAdelicCliffordGeneralSpinGroup)
      rw [hdelta,
        W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel_mul a ha])

@[simp]
theorem fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure_mk
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (gamma : (W.nonisotropicLastExtension a ha
      |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
    W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure a ha
        (QuotientGroup.mk gamma) =
      W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel a ha
        (gamma : W.nonisotropicLastExtension a ha
          |>.FullAdelicCliffordGeneralSpinGroup) :=
  rfl

theorem fullAdelicNonisotropicLastShellCosetComplementTranslateSumMeasure_horizontal_eq_rawFibers
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.fullAdelicNonisotropicLastShellCosetComplementTranslateSumMeasure a ha
        W.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure =
      Measure.sum fun xi :
        (W.nonisotropicLastExtension a ha
          |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
            W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha =>
        W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure
          a ha xi := by
  unfold fullAdelicNonisotropicLastShellCosetComplementTranslateSumMeasure
  congr 1
  funext xi
  conv_rhs => rw [← Quot.out_eq xi]
  change _ =
    W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel a ha
      ((Quot.out xi :
        (W.nonisotropicLastExtension a ha
          |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
        (W.nonisotropicLastExtension a ha
          |>.FullAdelicCliffordGeneralSpinGroup))
  rw [W.fullAdelicNonisotropicLastShellAmbientOrbitFiberKernel_apply a ha]
  rw [W.fullAdelicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_eq_map_horizontal
    a ha]
  symm
  have houter : Measurable
      (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha =>
        ((Quot.out xi :
          (W.nonisotropicLastExtension a ha
            |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
          (W.nonisotropicLastExtension a ha
            |>.FullAdelicCliffordGeneralSpinGroup)) * h.1) :=
    ((measurable_const_mul
      ((Quot.out xi :
        (W.nonisotropicLastExtension a ha
          |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
        (W.nonisotropicLastExtension a ha
          |>.FullAdelicCliffordGeneralSpinGroup))).comp
      ((continuous_subtype_val : Continuous
        (fun h : W.FullAdelicNonisotropicLastComplementGeneralSpinStabilizer a ha =>
          h.1)).measurable))
  have hinner : Measurable
      (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
        a ha RationalAdele) :=
    (W.continuous_nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
      a ha RationalAdele).measurable
  have hdirect : Measurable
      (fun y : W.FullAdelicCliffordGeneralSpinGroup =>
        ((Quot.out xi :
          (W.nonisotropicLastExtension a ha
            |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
          (W.nonisotropicLastExtension a ha
            |>.FullAdelicCliffordGeneralSpinGroup)) *
          W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele y) :=
    (measurable_const_mul
      ((Quot.out xi :
        (W.nonisotropicLastExtension a ha
          |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup)) :
        (W.nonisotropicLastExtension a ha
          |>.FullAdelicCliffordGeneralSpinGroup))).comp
      (W.continuous_nonisotropicLastComplementGeneralSpinPoint
        a ha RationalAdele).measurable
  ext s hs
  rw [Measure.map_apply houter hs,
    Measure.map_apply hinner (hs.preimage houter),
    Measure.map_apply hdirect hs]
  rfl

theorem periodized_complementQuotientMeasure_eq_shellCoset_sum
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (μ : Measure W.FullAdelicCliffordGeneralSpinLeftQuotient) :
    (W.nonisotropicLastExtension a ha
      |>.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift)
        (Measure.map
          (W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
            a ha) μ) =
      W.fullAdelicNonisotropicLastShellCosetComplementPeriodizedMeasure a ha μ := by
  let E := W.nonisotropicLastExtension a ha
  let B := W.fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap a ha
  letI : Countable E.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup :=
    E.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup_countable
  letI : Countable
      (E.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha) :=
    Function.Surjective.countable
      (f := QuotientGroup.mk) Quotient.mk_surjective
  apply Measure.ext_of_lintegral
  intro f hf
  rw [E.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
    (Measure.map B μ) f hf]
  rw [lintegral_map'
    (E.measurable_fullAdelicCliffordGeneralSpinLeftPeriodize f hf).aemeasurable
    (W.continuous_fullAdelicNonisotropicLastComplementGeneralSpinLeftQuotientMap
      a ha).measurable.aemeasurable]
  rw [fullAdelicNonisotropicLastShellCosetComplementPeriodizedMeasure, lintegral_sum_measure]
  have htrans : ∀ xi :
      E.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha,
      Measurable
        (fun y : W.FullAdelicCliffordGeneralSpinGroup =>
          (((Quot.out xi :
              E.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
              E.FullAdelicCliffordGeneralSpinGroup) *
            W.nonisotropicLastComplementGeneralSpinPoint a ha RationalAdele y)) := by
    intro xi
    exact (measurable_const_mul
      ((Quot.out xi :
        E.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
        E.FullAdelicCliffordGeneralSpinGroup)).comp
      (W.continuous_nonisotropicLastComplementGeneralSpinPoint
        a ha RationalAdele).measurable
  have hmap : ∀ xi :
      E.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup ⧸
        W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha,
      Measurable (W.fullAdelicNonisotropicLastShellCosetComplementIntegrand a ha xi f) := by
    intro xi
    exact hf.comp (htrans xi)
  calc
    (∫⁻ q, leftPeriodize
        E.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup f (B q) ∂μ) =
        ∫⁻ q, ∑' xi,
          leftPeriodize
            W.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
            (W.fullAdelicNonisotropicLastShellCosetComplementIntegrand a ha xi f) q ∂μ := by
      apply lintegral_congr
      intro q
      exact W.leftPeriodize_block_complementQuotient_eq_shellCoset_tsum
        a ha q f
    _ = ∑' xi,
        ∫⁻ q, leftPeriodize
          W.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
          (W.fullAdelicNonisotropicLastShellCosetComplementIntegrand a ha xi f) q ∂μ := by
      rw [lintegral_tsum]
      intro xi
      exact
        (W.measurable_fullAdelicCliffordGeneralSpinLeftPeriodize
          (W.fullAdelicNonisotropicLastShellCosetComplementIntegrand a ha xi f)
          (hmap xi)).aemeasurable
    _ = ∑' xi,
        ∫⁻ y, W.fullAdelicNonisotropicLastShellCosetComplementIntegrand a ha xi f y
          ∂W.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ := by
      apply tsum_congr
      intro xi
      rw [W.lintegral_fullAdelicCliffordGeneralSpinPeriodizedQuotientLift_eq_leftPeriodize
        μ _ (hmap xi)]
    _ = ∑' xi,
        ∫⁻ y, f y ∂Measure.map
          (fun y : W.FullAdelicCliffordGeneralSpinGroup =>
            (((Quot.out xi :
                E.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) :
                E.FullAdelicCliffordGeneralSpinGroup) *
              W.nonisotropicLastComplementGeneralSpinPoint
                a ha RationalAdele y))
          (W.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift μ) := by
      apply tsum_congr
      intro xi
      rw [lintegral_map hf (htrans xi)]
      rfl

end RationalQuadraticSpaceMatrix

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ}

theorem periodized_nonisotropicLastComplementVerticalSpinFiberBoundMeasure_eq
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    let W := L.rationalQuadraticSpaceMatrix
    (W.nonisotropicLastExtension a ha
      |>.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift)
        (D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
          L hn a ha hsurj) =
      D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj •
        W.fullAdelicNonisotropicLastShellCosetComplementTranslateSumMeasure a ha
          W.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  let W := L.rationalQuadraticSpaceMatrix
  dsimp only
  rw [nonisotropicLastComplementVerticalSpinFiberBoundMeasure]
  rw [W.periodized_complementQuotientMeasure_eq_shellCoset_sum a ha]
  exact W.fullAdelicNonisotropicLastShellCosetComplementPeriodizedMeasure_eq_smul_translateSum
    a ha
    (D.verticalSpinFiberHaarBoundMeasure L hn hsurj)
    W.fullAdelicCliffordGeneralSpinHorizontalGroupMeasure
    (D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj)
    (D.periodizedVerticalSpinFiberHaarBoundMeasure_eq_smul_horizontal
      L hn hsurj)

theorem periodized_nonisotropicLastComplementVerticalSpinFiberBoundMeasure_eq_rawFibers
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (a : ℚ) (ha : a ≠ 0)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    let W := L.rationalQuadraticSpaceMatrix
    (W.nonisotropicLastExtension a ha
      |>.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift)
        (D.nonisotropicLastComplementVerticalSpinFiberBoundMeasure
          L hn a ha hsurj) =
      D.periodizedVerticalSpinFiberHaarBoundRightHaarScalar L hn hsurj •
        Measure.sum fun xi :
          (W.nonisotropicLastExtension a ha
            |>.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup) ⧸
              W.nonisotropicLastComplementGeneralSpinDiagonalImage a ha =>
          W.fullAdelicNonisotropicLastRationalShellCosetRawOrbitFiberMeasure
            a ha xi := by
  let W := L.rationalQuadraticSpaceMatrix
  dsimp only
  rw [D.periodized_nonisotropicLastComplementVerticalSpinFiberBoundMeasure_eq
    L hn a ha hsurj]
  rw [W.fullAdelicNonisotropicLastShellCosetComplementTranslateSumMeasure_horizontal_eq_rawFibers
    a ha]

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

import SMSFormula.RationalCliffordGeneralSpinPolarGaussianLatticeNonnegative
import SMSFormula.RationalCliffordGeneralSpinHorizontalFundamentalDomainComparison
import SMSFormula.RationalCliffordGeneralSpinLatticeFiniteSpinClassHorizontalConcrete
import Mathlib.Probability.ProductMeasure
import SMSFormula.RationalCliffordSpinCandidateLatticeGoodIntegralPointMapPushforward
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockSplit
import SMSFormula.RationalCliffordGeneralSpinLatticeIntegralSpinorRange
import SMSFormula.RationalCliffordSpinCandidateAlmostEverywhereIntegralLifting
import SMSFormula.RationalSquareClassFiniteLocalizationSurjectivity
import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.FieldSimp
import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteAdelicStabilizerCarrier
import SMSFormula.SpecialOrthogonalFiniteAdelicDifferentialSelectorMass
import SMSFormula.AdelicLeftCosets
import SMSFormula.RationalCliffordGeneralSpinLatticeFiniteAdelicSOSurjectivity
import SMSFormula.RationalCliffordGeneralSpinAdelicProduct
import SMSFormula.RationalCliffordGeneralSpinVerticalEquivalence
import SMSFormula.RationalCliffordGeneralSpinAdelicSpecialOrthogonalQuotient
import SMSFormula.RationalCliffordSpinCandidateLatticeProperDomainSelectorSourceMap
import SMSFormula.SpecialOrthogonalFullAdelicProperPieceDifferentialMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import SMSFormula.RationalCliffordGeneralSpinVerticalSpecialOrthogonalProjection
import SMSFormula.RationalCliffordSpinCandidateKernelMuTwo
import SMSFormula.RationalCliffordSpinCandidateAdelicLeftQuotientTopology
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorNormUnitValued
import SMSFormula.RationalCliffordSpinCandidatePlacewiseSpinorNormContinuity
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicRestrictedFamilyCarrier
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicRestrictedFamilyGroup
import SMSFormula.RationalSpecialOrthogonalAdelicSpinorNormDiagonal
import SMSFormula.RationalSpecialOrthogonalTamagawa
import SMSFormula.RationalAdeleAdditiveMeasure
import SMSFormula.RationalCliffordSpinCandidateTopologicalGroup
import SMSFormula.RationalCliffordSpinCandidateOnoRelativeTamagawaData

/-!
# Finiteness of the concrete polar theta cutoff

The polar Gaussian--lattice theta depends on a full-adelic special-orthogonal
point only through its rational left coset and its finite proper double coset.
Indeed the test is fixed on the right by the product of the real orthogonal
group and the integral finite stabilizer.  The proper-domain
factorization therefore bounds the theta by a finite sum of its values at the
proper representatives.

Combining this finite bound with the certified finite raw `SO` quotient mass
and the exact horizontal fiber cutoff proves finiteness of the ordinary theta
integral for the unit logarithmic cutoff.  The final passage to the
fixed horizontal quotient measure keeps and cancels its positive finite
periodization scalar; no scalar is set to one.
-/

noncomputable section

open Matrix MeasureTheory Set
open PositiveDefiniteIntegralLattice
open RationalQuadraticSpaceMatrix
open scoped ENNReal BigOperators

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Real projection commutes with an arbitrary full-adelic
special-orthogonal matrix action. -/
theorem rationalAdeleVectorRealPart_fullAdelicSpecialOrthogonal_mulVec
    (V : RationalQuadraticSpaceMatrix n)
    (h : V.FullAdelicSpecialOrthogonalGroup)
    (x : Fin n → RationalAdele) :
    rationalAdeleVectorRealPart n (h.1.1.1.mulVec x) =
      ((V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).1.1.1.1).mulVec
        (rationalAdeleVectorRealPart n x) := by
  funext i
  let proj : RationalAdele →+* ℝ :=
    rationalInfiniteAdeleRingEquivReal.toRingHom.comp
      (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)
  rw [V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_apply_real_matrix]
  change proj (∑ j, h.1.1.1 i j * x j) =
    ∑ j, proj (h.1.1.1 i j) * proj (x j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact map_mul proj (h.1.1.1 i j) (x j)

/-- Finite projection commutes with an arbitrary full-adelic
special-orthogonal matrix action. -/
theorem rationalAdeleVectorFinitePart_fullAdelicSpecialOrthogonal_mulVec
    (V : RationalQuadraticSpaceMatrix n)
    (h : V.FullAdelicSpecialOrthogonalGroup)
    (x : Fin n → RationalAdele) :
    rationalAdeleVectorFinitePart n (h.1.1.1.mulVec x) =
      ((V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2.1.1.1).mulVec
        (rationalAdeleVectorFinitePart n x) := by
  funext i
  let proj : RationalAdele →+* RationalFiniteAdele :=
    RingHom.snd RationalInfiniteAdele RationalFiniteAdele
  rw [V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_apply_finite_matrix]
  change proj (∑ j, h.1.1.1 i j * x j) =
    ∑ j, proj (h.1.1.1 i j) * proj (x j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact map_mul proj (h.1.1.1 i j) (x j)

private theorem specialOrthogonalMatrixGroupIsometryEquiv_apply
    (V : RationalQuadraticSpaceMatrix n)
    (d : V.RationalSpecialOrthogonalGroup) (x : Fin n → ℚ) :
    V.specialOrthogonalMatrixGroupIsometryEquiv ℚ d x = d.1.1.1.mulVec x := by
  change Matrix.toLin' d.1.1.1 x = _
  rfl

/-- The inverse special-orthogonal action on a rational diagonal vector. -/
def fullAdelicSpecialOrthogonalRationalVectorAction
    (V : RationalQuadraticSpaceMatrix n)
    (g : V.FullAdelicSpecialOrthogonalGroup) (x : Fin n → ℚ) :
    Fin n → RationalAdele :=
  (g⁻¹).1.1.1.mulVec (rationalAdeleVectorDiagonal n x)

set_option backward.isDefEq.respectTransparency false in
/-- Rational left multiplication reindexes the inverse orthogonal action by
the corresponding rational inverse isometry. -/
theorem fullAdelicSpecialOrthogonalRationalVectorAction_rationalDiagonal_mul
    (V : RationalQuadraticSpaceMatrix n)
    (d : V.RationalSpecialOrthogonalGroup)
    (g : V.FullAdelicSpecialOrthogonalGroup) (x : Fin n → ℚ) :
    V.fullAdelicSpecialOrthogonalRationalVectorAction
        (V.rationalSpecialOrthogonalFullAdelicDiagonalHom d * g) x =
      V.fullAdelicSpecialOrthogonalRationalVectorAction g
        (V.specialOrthogonalMatrixGroupIsometryEquiv ℚ (d⁻¹) x) := by
  unfold fullAdelicSpecialOrthogonalRationalVectorAction
  rw [_root_.mul_inv_rev]
  change
    ((g⁻¹).1.1.1 *
        ((V.rationalSpecialOrthogonalFullAdelicDiagonalHom d)⁻¹).1.1.1).mulVec
          (rationalAdeleVectorDiagonal n x) = _
  rw [← Matrix.mulVec_mulVec,
    specialOrthogonalMatrixGroupIsometryEquiv_apply,
    ← rationalAdeleVectorDiagonal_mulVec]
  have hd :
      ((V.rationalSpecialOrthogonalFullAdelicDiagonalHom d)⁻¹).1.1.1 =
        (d⁻¹).1.1.1.map (algebraMap ℚ RationalAdele) := by
    rw [← map_inv]
    exact V.specialOrthogonalMatrixGroupMap_apply_matrix
      (Algebra.ofId ℚ RationalAdele) (d⁻¹)
  rw [hd]

/-- Ordinary nonnegative theta attached directly to a full-adelic `SO`
point. -/
def fullAdelicSpecialOrthogonalTheta
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : V.FullAdelicSpecialOrthogonalGroup) : ℝ≥0∞ :=
  ∑' x : Fin n → ℚ,
    Phi (V.fullAdelicSpecialOrthogonalRationalVectorAction g x)

/-- The direct `SO` theta is invariant under the complete rational diagonal. -/
theorem fullAdelicSpecialOrthogonalTheta_rational_mul
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (delta : V.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
    (g : V.FullAdelicSpecialOrthogonalGroup) :
    V.fullAdelicSpecialOrthogonalTheta Phi
        ((delta : V.FullAdelicSpecialOrthogonalGroup) * g) =
      V.fullAdelicSpecialOrthogonalTheta Phi g := by
  rcases delta.2 with ⟨d, hd⟩
  have hdelta :
      (delta : V.FullAdelicSpecialOrthogonalGroup) =
        V.rationalSpecialOrthogonalFullAdelicDiagonalHom d := hd.symm
  rw [hdelta]
  unfold fullAdelicSpecialOrthogonalTheta
  simp_rw [V.fullAdelicSpecialOrthogonalRationalVectorAction_rationalDiagonal_mul]
  exact (V.specialOrthogonalMatrixGroupIsometryEquiv ℚ (d⁻¹)).toEquiv.tsum_eq
    (fun x ↦ Phi (V.fullAdelicSpecialOrthogonalRationalVectorAction g x))

/-- The direct `SO` theta on the existing rational left quotient. -/
def fullAdelicSpecialOrthogonalThetaOnLeftQuotient
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞) :
    V.FullAdelicSpecialOrthogonalLeftQuotient → ℝ≥0∞ :=
  Quot.lift (V.fullAdelicSpecialOrthogonalTheta Phi) (by
    intro g h hrel
    rcases hrel with ⟨delta, rfl⟩
    exact (V.fullAdelicSpecialOrthogonalTheta_rational_mul Phi delta g).symm)

@[simp]
theorem fullAdelicSpecialOrthogonalThetaOnLeftQuotient_mk
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : V.FullAdelicSpecialOrthogonalGroup) :
    V.fullAdelicSpecialOrthogonalThetaOnLeftQuotient Phi
        (V.fullAdelicSpecialOrthogonalLeftQuotientMap g) =
      V.fullAdelicSpecialOrthogonalTheta Phi g :=
  rfl

/-- The ordinary `GSpin` theta is exactly the direct `SO` theta at its
represented orthogonal matrix. -/
theorem fullAdelicCliffordGeneralSpinTheta_eq_specialOrthogonalTheta
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinTheta Phi g =
      V.fullAdelicSpecialOrthogonalTheta Phi
        (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom g) := by
  rfl

/-- Section-free factorization of ordinary theta through the horizontal
projection to the rational `SO` quotient. -/
theorem fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_eq_specialOrthogonalTheta
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (Z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi Z =
      V.fullAdelicSpecialOrthogonalThetaOnLeftQuotient Phi
        (V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal Z) := by
  induction Z using Quot.inductionOn with
  | _ g => rfl

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000

/-! ## Invariance of the concrete test under the real/integral stabilizer -/

/-- Real projection commutes with matrix multiplication by a concrete
full-adelic special-orthogonal point. -/
theorem rationalAdeleVectorRealPart_concreteFullAdelicSpecialOrthogonal_mulVec
    (L : PositiveDefiniteIntegralLattice n)
    (h : L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (x : Fin n → RationalAdele) :
    rationalAdeleVectorRealPart n (h.1.1.1.mulVec x) =
      ((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).1.1.1.1).mulVec
        (rationalAdeleVectorRealPart n x) := by
  let V := L.rationalQuadraticSpaceMatrix
  let hV := L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.symm h
  have hcomp :=
    L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_components hV
  rw [L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.apply_symm_apply]
    at hcomp
  have hreal := congrArg Prod.fst hcomp
  simpa only [V, hV,
    L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_symm_apply_matrix,
    hreal] using
      V.rationalAdeleVectorRealPart_fullAdelicSpecialOrthogonal_mulVec hV x

/-- Finite projection commutes with matrix multiplication by a concrete
full-adelic special-orthogonal point. -/
theorem rationalAdeleVectorFinitePart_concreteFullAdelicSpecialOrthogonal_mulVec
    (L : PositiveDefiniteIntegralLattice n)
    (h : L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (x : Fin n → RationalAdele) :
    rationalAdeleVectorFinitePart n (h.1.1.1.mulVec x) =
      ((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h).2.1.1.1).mulVec
        (rationalAdeleVectorFinitePart n x) := by
  let V := L.rationalQuadraticSpaceMatrix
  let hV := L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.symm h
  have hcomp :=
    L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_components hV
  rw [L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.apply_symm_apply]
    at hcomp
  have hfinite := congrArg Prod.snd hcomp
  simpa only [V, hV,
    L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_symm_apply_matrix,
    hfinite] using
      V.rationalAdeleVectorFinitePart_fullAdelicSpecialOrthogonal_mulVec hV x

/-- The concrete polar Gaussian--lattice test is fixed by a full-adelic
orthogonal element whose finite component stabilizes the standard lattice.
The real component is unrestricted inside the real special-orthogonal group. -/
theorem rationalAdeleVectorPolarGaussianLatticeTest_concreteStabilizer_mulVec
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup)
    (x : Fin n → RationalAdele) :
    rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)
        (h.1.1.1.1.mulVec x) =
      rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) x := by
  let hr := (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h.1).1
  let hf := (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv h.1).2
  have hhf : hf ∈ L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := by
    exact (L.mem_fullAdelicRealFiniteLatticeStabilizerSubgroup_iff h.1).mp h.2
  unfold rationalAdeleVectorPolarGaussianLatticeTest
  rw [L.rationalAdeleVectorRealPart_concreteFullAdelicSpecialOrthogonal_mulVec,
    L.rationalAdeleVectorFinitePart_concreteFullAdelicSpecialOrthogonal_mulVec]
  rw [RationalQuadraticSpaceMatrix.polarRealGaussian_realSpecialOrthogonal
    L (a : ℂ) hr]
  by_cases hx : rationalAdeleVectorFinitePart n x ∈ integralFiniteAdeleVectors n
  · have hmul : hf.1.1.1.mulVec (rationalAdeleVectorFinitePart n x) ∈
        integralFiniteAdeleVectors n :=
      (L.finiteLocalLatticeStabilizerSubgroup_mulVec_mem_iff hhf
        (rationalAdeleVectorFinitePart n x)).2 hx
    rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_mem hx,
      RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_mem hmul]
  · have hmul : hf.1.1.1.mulVec (rationalAdeleVectorFinitePart n x) ∉
        integralFiniteAdeleVectors n := by
      intro h
      exact hx ((L.finiteLocalLatticeStabilizerSubgroup_mulVec_mem_iff hhf
        (rationalAdeleVectorFinitePart n x)).1 h)
    rw [RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx,
      RationalQuadraticSpaceMatrix.rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hmul]

/-- The literal nonnegative concrete test has the same stabilizer invariance. -/
theorem rationalAdeleVectorPolarGaussianLatticeTestENNReal_concreteStabilizer_mulVec
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup)
    (x : Fin n → RationalAdele) :
    rationalAdeleVectorPolarGaussianLatticeTestENNReal L a
        (h.1.1.1.1.mulVec x) =
      rationalAdeleVectorPolarGaussianLatticeTestENNReal L a x := by
  unfold rationalAdeleVectorPolarGaussianLatticeTestENNReal
  rw [L.rationalAdeleVectorPolarGaussianLatticeTest_concreteStabilizer_mulVec]

/-! ## The ordinary theta on the concrete adelic `SO` quotient -/

/-- The ordinary nonnegative polar theta attached directly to the
concrete full-adelic special-orthogonal carrier. -/
def concreteFullAdelicSpecialOrthogonalPolarTheta
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) : ℝ≥0∞ :=
  ∑' x : Fin n → ℚ,
    rationalAdeleVectorPolarGaussianLatticeTestENNReal L a
      ((g⁻¹).1.1.1.mulVec (rationalAdeleVectorDiagonal n x))

/-- The concrete theta is exactly the intrinsic direct `SO` theta
after the canonical carrier identification. -/
theorem concreteFullAdelicSpecialOrthogonalPolarTheta_eq_intrinsic
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.concreteFullAdelicSpecialOrthogonalPolarTheta a g =
      L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalTheta
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.symm g) := by
  unfold concreteFullAdelicSpecialOrthogonalPolarTheta
  unfold RationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalTheta
  unfold RationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalRationalVectorAction
  rw [← map_inv]
  rw [L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_symm_apply_matrix]

/-- Right multiplication by the real/integral stabilizer preserves the
concrete polar theta pointwise. -/
theorem concreteFullAdelicSpecialOrthogonalPolarTheta_mul_stabilizer
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup) :
    L.concreteFullAdelicSpecialOrthogonalPolarTheta a (g * h.1) =
      L.concreteFullAdelicSpecialOrthogonalPolarTheta a g := by
  unfold concreteFullAdelicSpecialOrthogonalPolarTheta
  have hmulVec (x : Fin n → ℚ) :
      (((g * h.1)⁻¹).1.1.1).mulVec (rationalAdeleVectorDiagonal n x) =
        (h⁻¹).1.1.1.1.mulVec
          ((g⁻¹).1.1.1.mulVec (rationalAdeleVectorDiagonal n x)) := by
    rw [_root_.mul_inv_rev]
    change
      (((h⁻¹).1.1.1.1 * (g⁻¹).1.1.1).mulVec
          (rationalAdeleVectorDiagonal n x)) = _
    rw [Matrix.mulVec_mulVec]
  apply tsum_congr
  intro x
  rw [hmulVec]
  exact L.rationalAdeleVectorPolarGaussianLatticeTestENNReal_concreteStabilizer_mulVec
    a h⁻¹ ((g⁻¹).1.1.1.mulVec (rationalAdeleVectorDiagonal n x))

/-- The concrete theta descends to the literal rational `SO` left quotient. -/
def concreteFullAdelicSpecialOrthogonalPolarThetaOnLeftQuotient
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ) :
    L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient → ℝ≥0∞ :=
  L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalThetaOnLeftQuotient
      (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) ∘
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv.symm

@[simp]
theorem concreteFullAdelicSpecialOrthogonalPolarThetaOnLeftQuotient_mk
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.concreteFullAdelicSpecialOrthogonalPolarThetaOnLeftQuotient a
        (L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap g) =
      L.concreteFullAdelicSpecialOrthogonalPolarTheta a g :=
  by
    rw [concreteFullAdelicSpecialOrthogonalPolarThetaOnLeftQuotient,
      Function.comp_apply,
      L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv_symm_mk,
      L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalThetaOnLeftQuotient_mk]
    exact (L.concreteFullAdelicSpecialOrthogonalPolarTheta_eq_intrinsic a g).symm

/-- The direct `SO` quotient theta is finite for the concrete positive polar
Gaussian--lattice test.  Surjectivity is used only propositionally to compare
with the already summable intrinsic `GSpin` theta. -/
theorem fullAdelicSpecialOrthogonalPolarThetaOnLeftQuotient_ne_top
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a)
    (q : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient) :
    L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalThetaOnLeftQuotient
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) q ≠ ⊤ := by
  let V := L.rationalQuadraticSpaceMatrix
  obtain ⟨Z, hZ⟩ :=
    L.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective_of_rankAtLeastThree
      hn q
  rw [← hZ,
    ← V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_eq_specialOrthogonalTheta]
  induction Z using Quot.inductionOn with
  | _ g =>
      exact L.fullAdelicCliffordGeneralSpinPolarGaussianLatticeTheta_ne_top ha g

/-- Every concrete special-orthogonal theta value is finite. -/
theorem concreteFullAdelicSpecialOrthogonalPolarTheta_ne_top
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.concreteFullAdelicSpecialOrthogonalPolarTheta a g ≠ ⊤ := by
  rw [L.concreteFullAdelicSpecialOrthogonalPolarTheta_eq_intrinsic,
    ← L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalThetaOnLeftQuotient_mk]
  exact L.fullAdelicSpecialOrthogonalPolarThetaOnLeftQuotient_ne_top hn ha _

/-! ## Reduction to the finite proper double-coset set -/

/-- On the literal proper domain, the concrete polar theta is exactly its
value at the proper representative of the finite class label. -/
theorem concreteFullAdelicSpecialOrthogonalPolarTheta_properDomain
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (a : ℝ)
    (z : {g : L.ConcreteFullAdelicSpecialOrthogonalGroup //
      g ∈ L.concreteFullAdelicProperTransversal}) :
    L.concreteFullAdelicSpecialOrthogonalPolarTheta a z.1 =
      L.concreteFullAdelicSpecialOrthogonalPolarTheta a
        (L.concreteFullAdelicProperTransversalRepresentative
          (L.concreteFullAdelicProperDomainPieceLabel z)) := by
  let h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup :=
    L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv
      ((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv z.1).1,
        L.concreteFullAdelicProperDomainSelectorElement z)
  have hz : z.1 =
      L.concreteFullAdelicProperTransversalRepresentative
          (L.concreteFullAdelicProperDomainPieceLabel z) * h.1 := by
    exact L.concreteFullAdelicProperDomainSelectorElement_factor z
  rw [hz, L.concreteFullAdelicSpecialOrthogonalPolarTheta_mul_stabilizer]

/-- Finite sum of the theta values at the literal proper representatives. -/
noncomputable def concreteFullAdelicSpecialOrthogonalPolarThetaProperBound
    (L : PositiveDefiniteIntegralLattice n) (a : ℝ)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) : ℝ≥0∞ :=
  @Finset.sum L.ConcreteProperRationalDoubleCosetSet ℝ≥0∞ _
    (@Finset.univ L.ConcreteProperRationalDoubleCosetSet inst)
    (fun C ↦ L.concreteFullAdelicSpecialOrthogonalPolarTheta a
      (L.concreteFullAdelicProperTransversalRepresentative C))

/-- The proper representative sum bounds the concrete theta at every rational
`SO` quotient point. -/
theorem concreteFullAdelicSpecialOrthogonalPolarThetaOnLeftQuotient_le_properBound
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (a : ℝ)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (q : L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient) :
    L.concreteFullAdelicSpecialOrthogonalPolarThetaOnLeftQuotient a q ≤
      L.concreteFullAdelicSpecialOrthogonalPolarThetaProperBound a inst := by
  let z := L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDomain q
  let C := L.concreteFullAdelicProperDomainPieceLabel z
  have hq : L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap z.1 = q := by
    exact L.concreteFullAdelicSpecialOrthogonalLeftQuotientProperDomainEquiv.left_inv q
  have htheta :
      L.concreteFullAdelicSpecialOrthogonalPolarThetaOnLeftQuotient a q =
        L.concreteFullAdelicSpecialOrthogonalPolarTheta a
          (L.concreteFullAdelicProperTransversalRepresentative C) := by
    rw [← hq,
      L.concreteFullAdelicSpecialOrthogonalPolarThetaOnLeftQuotient_mk]
    exact L.concreteFullAdelicSpecialOrthogonalPolarTheta_properDomain a z
  rw [htheta]
  exact Finset.single_le_sum
    (fun C' _hC' ↦ (show (0 : ℝ≥0∞) ≤
      L.concreteFullAdelicSpecialOrthogonalPolarTheta a
        (L.concreteFullAdelicProperTransversalRepresentative C') from zero_le))
    (Finset.mem_univ C)

/-- The finite proper representative bound is finite. -/
theorem concreteFullAdelicSpecialOrthogonalPolarThetaProperBound_ne_top
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    L.concreteFullAdelicSpecialOrthogonalPolarThetaProperBound a inst ≠ ⊤ := by
  unfold concreteFullAdelicSpecialOrthogonalPolarThetaProperBound
  exact ENNReal.sum_ne_top.2 fun C _hC ↦
    L.concreteFullAdelicSpecialOrthogonalPolarTheta_ne_top hn ha
      (L.concreteFullAdelicProperTransversalRepresentative C)

/-- The same finite proper-representative sum bounds the ordinary polar theta
on every point of the intrinsic `GSpin` quotient. -/
theorem fullAdelicCliffordGeneralSpinPolarGaussianLatticeThetaOnLeftQuotient_le_properBound
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (a : ℝ)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (Z : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a) Z ≤
      L.concreteFullAdelicSpecialOrthogonalPolarThetaProperBound a inst := by
  let V := L.rationalQuadraticSpaceMatrix
  let q := V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal Z
  let qConcrete := L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv q
  have hbound :=
    L.concreteFullAdelicSpecialOrthogonalPolarThetaOnLeftQuotient_le_properBound
      a inst qConcrete
  rw [concreteFullAdelicSpecialOrthogonalPolarThetaOnLeftQuotient,
    Function.comp_apply, Equiv.symm_apply_apply] at hbound
  rw [V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_eq_specialOrthogonalTheta]
  exact hbound

/-! ## Finiteness on the existing horizontally normalized quotient -/

/-- The bare exact unit logarithmic cutoff has finite integral against the
existing horizontal quotient measure.  This is extracted from the proved
zero-shell calibration; the positive finite horizontal periodization scalar
is retained on its left-hand side. -/
theorem lintegral_horizontalQuotient_unitLogCutoff_ne_top
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P) :
    (∫⁻ Z,
      rationalIdeleClassUnitLogCutoff
        (L.rationalQuadraticSpaceMatrix
          |>.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
      ∂(L.rationalQuadraticSpaceMatrix
        |>.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
        |>.quotientMeasure)) ≠ ⊤ := by
  let V := L.rationalQuadraticSpaceMatrix
  let D := cliffordSpinCandidateRawOnoTamagawaDataOfLattice
    L (by omega : 3 ≤ r + 2) inst hP hconv
  let c := L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar
    (by omega : 3 ≤ r + 2) inst hP hconv
  let I : ℝ≥0∞ := ∫⁻ Z,
    rationalIdeleClassUnitLogCutoff
      (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
    ∂(V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData
      |>.quotientMeasure)
  have hcalibration :=
    L.horizontalScalar_mul_lintegral_logCutoff_eq_cutoffMass_mul_spinTamagawa
      hr inst hP hconv rationalIdeleClassUnitLogCutoff
        measurable_rationalIdeleClassUnitLogCutoff
  have hrelative : D.IsOnoRelativeTamagawaComparison := by
    simpa only [D] using
      L.cliffordSpinCandidateRawOnoTamagawaDataOfLattice_isOnoRelativeComparison
        (by omega) inst hP hconv
  have hspin : D.spinTamagawaNumberENNReal ≠ ⊤ :=
    D.spinTamagawaNumberENNReal_ne_top_of_onoRelativeComparison hrelative
  have hrhs :
      rationalIdeleClassLogCutoffLIntegral rationalIdeleClassUnitLogCutoff *
          D.spinTamagawaNumberENNReal ≠ ⊤ :=
    ENNReal.mul_ne_top
      rationalIdeleClassLogCutoffLIntegral_unit_ne_top hspin
  have hproduct : c * I ≠ ⊤ := by
    rw [show c * I =
        rationalIdeleClassLogCutoffLIntegral rationalIdeleClassUnitLogCutoff *
          D.spinTamagawaNumberENNReal by
      simpa only [V, D, c, I] using hcalibration]
    exact hrhs
  change I ≠ ⊤
  intro hI
  apply hproduct
  rw [hI, ENNReal.mul_top]
  exact L.periodizedHorizontalRawSOFiberHaarBoundRightHaarScalar_ne_zero
    (by omega) inst hP hconv

/-- The ordinary nonnegative theta logarithmic-cutoff integral is finite for
the literal polar Gaussian--lattice test and the exact authorized unit
cutoff. -/
theorem fullAdelicCliffordGeneralSpinPolarGaussianLatticeThetaLogCutoffIntegral_ne_top
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a) :
    L.fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral
        (rationalAdeleVectorPolarGaussianLatticeTestENNReal L a)
        rationalIdeleClassUnitLogCutoff ≠ ⊤ := by
  let V := L.rationalQuadraticSpaceMatrix
  let Phi := rationalAdeleVectorPolarGaussianLatticeTestENNReal L a
  let theta := V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi
  let cutoff : V.FullAdelicCliffordGeneralSpinLeftQuotient → ℝ≥0∞ := fun Z ↦
    rationalIdeleClassUnitLogCutoff
      (V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule Z)
  let mu :=
    V.fullAdelicCliffordGeneralSpinHorizontalMeasurableWeilData.quotientMeasure
  let B := L.concreteFullAdelicSpecialOrthogonalPolarThetaProperBound a inst
  have hPhi : Measurable Phi :=
    L.measurable_rationalAdeleVectorPolarGaussianLatticeTestENNReal a
  have htheta : Measurable theta :=
    V.measurable_fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi hPhi
  have hcutoff : Measurable cutoff :=
    measurable_rationalIdeleClassUnitLogCutoff.comp
      V.fullAdelicCliffordGeneralSpinLeftQuotientLogModule_measurable
  have hpoint (Z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
      theta Z * cutoff Z ≤ B * cutoff Z :=
    by
      exact mul_le_mul
        (L.fullAdelicCliffordGeneralSpinPolarGaussianLatticeThetaOnLeftQuotient_le_properBound
          a inst Z) le_rfl zero_le zero_le
  have hbare : (∫⁻ Z, cutoff Z ∂mu) ≠ ⊤ := by
    simpa only [V, cutoff, mu] using
      L.lintegral_horizontalQuotient_unitLogCutoff_ne_top hr inst hP hconv
  have hB : B ≠ ⊤ := by
    exact L.concreteFullAdelicSpecialOrthogonalPolarThetaProperBound_ne_top
      (by omega) ha inst
  have hmajorant : B * (∫⁻ Z, cutoff Z ∂mu) ≠ ⊤ :=
    ENNReal.mul_ne_top hB hbare
  have hle : (∫⁻ Z, theta Z * cutoff Z ∂mu) ≤
      B * (∫⁻ Z, cutoff Z ∂mu) := by
    calc
      (∫⁻ Z, theta Z * cutoff Z ∂mu) ≤
          ∫⁻ Z, B * cutoff Z ∂mu := lintegral_mono hpoint
      _ = B * (∫⁻ Z, cutoff Z ∂mu) := by
        rw [lintegral_const_mul B hcutoff]
  unfold fullAdelicCliffordGeneralSpinThetaLogCutoffIntegral
  dsimp only
  rw [lintegral_withDensity_eq_lintegral_mul mu htheta hcutoff]
  exact ne_top_of_le_ne_top hmajorant hle

end PositiveDefiniteIntegralLattice

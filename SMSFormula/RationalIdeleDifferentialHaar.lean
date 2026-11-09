import SMSFormula.RationalIdeleClassNormOneCompactness
import SMSFormula.RationalIdeleClassReferenceWeilQuotient
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Differential Haar measure on rational ideles

The compact-open subgroup of everywhere integral finite ideles fixes the
finite restricted-product multiplicative Haar scale by volume one.  Its
product with the literal Mathlib Haar measure on real units is transported
through the existing real--finite idele equivalence to full rational ideles.

The resulting full measure is compared with the arbitrary reference ambient
Haar by an explicit positive scalar.  Restricting it to the already certified
exact rational-diagonal fundamental domain gives the corresponding Weil
quotient, with the same scalar against the reference quotient.  No local
cylinder factorization, square-map modulus, or comparison with the separately
chosen idele-class Haar measure is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

local instance rationalIdeleDifferentialRealUnitsMeasurableSpace :
    MeasurableSpace ℝˣ :=
  borel ℝˣ

local instance rationalIdeleDifferentialRealUnitsBorelSpace :
    BorelSpace ℝˣ :=
  ⟨rfl⟩

local instance rationalIdeleDifferentialRealUnitsSecondCountableTopology :
    SecondCountableTopology ℝˣ :=
  Units.isEmbedding_embedProduct.secondCountableTopology

local instance rationalIdeleDifferentialFiniteUnitsMeasurableSpace :
    MeasurableSpace RationalFiniteAdeleˣ :=
  borel RationalFiniteAdeleˣ

local instance rationalIdeleDifferentialFiniteUnitsBorelSpace :
    BorelSpace RationalFiniteAdeleˣ :=
  ⟨rfl⟩

local instance rationalIdeleDifferentialFiniteUnitsSecondCountableTopology :
    SecondCountableTopology RationalFiniteAdeleˣ := by
  letI : SecondCountableTopology RationalFiniteAdeleᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology
      (RationalFiniteAdele × RationalFiniteAdeleᵐᵒᵖ) :=
    inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

local instance : MulAction RationalAdeleˣ RationalAdeleˣ :=
  Monoid.toMulAction RationalAdeleˣ

local instance : MulAction rationalIdeleDiagonalSubgroup RationalAdeleˣ :=
  Subgroup.instMulAction

local instance rationalIdeleDifferentialDiagonalCountable :
    Countable rationalIdeleDiagonalSubgroup :=
  rationalIdeleDiagonalSubgroup_countable

local instance rationalIdeleDifferentialDiagonalOpCountable :
    Countable rationalIdeleDiagonalSubgroup.op := by
  let unopEquiv : rationalIdeleDiagonalSubgroup.op →
      rationalIdeleDiagonalSubgroup := fun gamma ↦
    ⟨MulOpposite.unop (gamma : RationalAdeleˣᵐᵒᵖ), gamma.2⟩
  apply Function.Injective.countable (f := unopEquiv)
  intro gamma delta h
  apply Subtype.ext
  exact MulOpposite.unop_injective (congrArg Subtype.val h)

/-! ## The normalized finite restricted-product factor -/

/-- The compact-open subgroup of everywhere integral finite ideles, packaged
as the positive compact that fixes the restricted-product Haar scale. -/
noncomputable def rationalFiniteIdeleIntegralPositiveCompacts :
    PositiveCompacts RationalFiniteAdeleˣ where
  carrier := integralFiniteIdeleUnits
  isCompact' := isCompact_integralFiniteIdeleUnits
  interior_nonempty' := by
    rw [isOpen_integralFiniteIdeleUnits.interior_eq]
    exact ⟨1, one_mem_integralFiniteIdeleUnits⟩

/-- Multiplicative Haar on finite rational ideles normalized so that the
everywhere integral compact-open subgroup has volume one. -/
noncomputable def rationalFiniteIdeleDifferentialHaarMeasure :
    Measure RationalFiniteAdeleˣ :=
  Measure.haarMeasure rationalFiniteIdeleIntegralPositiveCompacts

@[simp]
theorem rationalFiniteIdeleDifferentialHaarMeasure_integralUnits :
    rationalFiniteIdeleDifferentialHaarMeasure integralFiniteIdeleUnits = 1 := by
  exact Measure.haarMeasure_self

noncomputable instance rationalFiniteIdeleDifferentialHaarMeasure_isHaarMeasure :
    Measure.IsHaarMeasure rationalFiniteIdeleDifferentialHaarMeasure := by
  unfold rationalFiniteIdeleDifferentialHaarMeasure
  infer_instance

/-! ## Real--finite product and full ideles -/

/-- The literal real multiplicative Haar factor times the normalized finite
restricted-product factor. -/
noncomputable def rationalIdeleRealFiniteDifferentialHaarMeasure :
    Measure (ℝˣ × RationalFiniteAdeleˣ) :=
  (Measure.haar : Measure ℝˣ).prod rationalFiniteIdeleDifferentialHaarMeasure

theorem rationalIdeleRealFiniteDifferentialHaarMeasure_isHaarMeasure :
    Measure.IsHaarMeasure rationalIdeleRealFiniteDifferentialHaarMeasure := by
  letI : Measure.IsHaarMeasure (Measure.haar : Measure ℝˣ) := inferInstance
  letI : Measure.IsHaarMeasure rationalFiniteIdeleDifferentialHaarMeasure :=
    rationalFiniteIdeleDifferentialHaarMeasure_isHaarMeasure
  letI : SigmaFinite (Measure.haar : Measure ℝˣ) := by
    unfold Measure.haar
    infer_instance
  letI : SigmaFinite rationalFiniteIdeleDifferentialHaarMeasure := by
    unfold rationalFiniteIdeleDifferentialHaarMeasure
    infer_instance
  letI : SFinite (Measure.haar : Measure ℝˣ) := by infer_instance
  letI : SFinite rationalFiniteIdeleDifferentialHaarMeasure := by infer_instance
  unfold rationalIdeleRealFiniteDifferentialHaarMeasure
  exact Measure.prod.instIsHaarMeasure
    (Measure.haar : Measure ℝˣ) rationalFiniteIdeleDifferentialHaarMeasure

/-- Full rational-idele differential Haar, transported from the exact
real--finite product normalization. -/
noncomputable def rationalIdeleDifferentialHaarMeasure :
    Measure RationalAdeleˣ :=
  Measure.map rationalAdeleUnitsRealFiniteContinuousEquiv.symm.toHomeomorph
    rationalIdeleRealFiniteDifferentialHaarMeasure

/-- Splitting the full differential measure recovers its defining real and
finite factors literally. -/
theorem map_rationalIdeleDifferentialHaarMeasure_realFinite :
    Measure.map rationalAdeleUnitsRealFiniteContinuousEquiv.toHomeomorph
        rationalIdeleDifferentialHaarMeasure =
      (Measure.haar : Measure ℝˣ).prod
        rationalFiniteIdeleDifferentialHaarMeasure := by
  rw [rationalIdeleDifferentialHaarMeasure]
  exact MeasurableEquiv.map_map_symm
    rationalAdeleUnitsRealFiniteContinuousEquiv.toMeasurableEquiv

/-- The transported full rational-idele differential measure is Haar at the
fixed real factor and finite integral-volume-one scale. -/
noncomputable instance rationalIdeleDifferentialHaarMeasure_isHaarMeasure :
    Measure.IsHaarMeasure rationalIdeleDifferentialHaarMeasure := by
  letI : Measure.IsHaarMeasure rationalIdeleRealFiniteDifferentialHaarMeasure :=
    rationalIdeleRealFiniteDifferentialHaarMeasure_isHaarMeasure
  unfold rationalIdeleDifferentialHaarMeasure
  exact
    rationalAdeleUnitsRealFiniteContinuousEquiv.symm.toMulEquiv.isHaarMeasure_map
      rationalIdeleRealFiniteDifferentialHaarMeasure
      rationalAdeleUnitsRealFiniteContinuousEquiv.symm.continuous
      rationalAdeleUnitsRealFiniteContinuousEquiv.continuous

noncomputable instance rationalIdeleDifferentialHaarMeasure_sigmaFinite :
    SigmaFinite rationalIdeleDifferentialHaarMeasure := by
  letI : Measure.IsHaarMeasure rationalIdeleDifferentialHaarMeasure :=
    rationalIdeleDifferentialHaarMeasure_isHaarMeasure
  infer_instance

noncomputable instance rationalIdeleDifferentialHaarMeasure_isRightInvariant :
    Measure.IsMulRightInvariant rationalIdeleDifferentialHaarMeasure := by
  infer_instance

/-! ## Exact comparison with the certified reference ambient scale -/

/-- The positive finite scalar carrying reference idele Haar to the fixed
differential restricted-product normalization. -/
noncomputable def rationalIdeleDifferentialToReferenceHaarScalar : ℝ≥0 := by
  letI : Measure.IsHaarMeasure rationalIdeleDifferentialHaarMeasure :=
    rationalIdeleDifferentialHaarMeasure_isHaarMeasure
  exact Measure.haarScalarFactor rationalIdeleDifferentialHaarMeasure
    rationalIdeleReferenceHaarMeasure

theorem rationalIdeleDifferentialToReferenceHaarScalar_pos :
    0 < rationalIdeleDifferentialToReferenceHaarScalar := by
  letI : Measure.IsHaarMeasure rationalIdeleDifferentialHaarMeasure :=
    rationalIdeleDifferentialHaarMeasure_isHaarMeasure
  unfold rationalIdeleDifferentialToReferenceHaarScalar
  exact Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

/-- Haar uniqueness records the exact ambient conversion scalar. -/
theorem rationalIdeleDifferentialHaarMeasure_eq_smul_referenceHaar :
    rationalIdeleDifferentialHaarMeasure =
      rationalIdeleDifferentialToReferenceHaarScalar •
        rationalIdeleReferenceHaarMeasure := by
  letI : Measure.IsHaarMeasure rationalIdeleDifferentialHaarMeasure :=
    rationalIdeleDifferentialHaarMeasure_isHaarMeasure
  letI : IsFiniteMeasureOnCompacts rationalIdeleDifferentialHaarMeasure := by
    infer_instance
  letI : Measure.IsMulLeftInvariant rationalIdeleDifferentialHaarMeasure := by
    infer_instance
  exact Measure.isMulLeftInvariant_eq_smul
    rationalIdeleDifferentialHaarMeasure rationalIdeleReferenceHaarMeasure

/-! ## The induced differential Weil quotient -/

/-- The exact rational-diagonal transversal is also a fundamental domain for
the differential ambient normalization. -/
theorem rationalIdeleDifferentialHaar_isFundamentalDomain :
    IsFundamentalDomain rationalIdeleDiagonalSubgroup
      rationalIdeleMeasurableFundamentalDomain
      rationalIdeleDifferentialHaarMeasure :=
  IsFundamentalDomain.mk'
    measurableSet_rationalIdeleMeasurableFundamentalDomain.nullMeasurableSet
    (by
      intro x
      change ∃! gamma : rationalIdeleDiagonalSubgroup,
        (gamma : RationalAdeleˣ) * x ∈ rationalIdeleMeasurableFundamentalDomain
      exact existsUnique_rationalIdeleDiagonal_mul_mem_measurableFundamentalDomain x)

/-- The same differential fundamental domain in the opposite-action
orientation required by Mathlib's quotient-Weil package. -/
theorem rationalIdeleDifferentialHaar_isFundamentalDomain_op :
    IsFundamentalDomain rationalIdeleDiagonalSubgroup.op
      rationalIdeleMeasurableFundamentalDomain
      rationalIdeleDifferentialHaarMeasure :=
  IsFundamentalDomain.mk'
    measurableSet_rationalIdeleMeasurableFundamentalDomain.nullMeasurableSet
    (by
      intro x
      rcases existsUnique_rationalIdeleDiagonal_mul_mem_measurableFundamentalDomain x with
        ⟨gamma, hgamma, hunique⟩
      let gammaOp : rationalIdeleDiagonalSubgroup.op :=
        ⟨MulOpposite.op (gamma : RationalAdeleˣ), gamma.2⟩
      refine ⟨gammaOp, ?_, ?_⟩
      · simpa [gammaOp, mul_comm] using hgamma
      · intro delta hdelta
        let deltaUnop : rationalIdeleDiagonalSubgroup :=
          ⟨MulOpposite.unop (delta : RationalAdeleˣᵐᵒᵖ), delta.2⟩
        have hdu :
            (deltaUnop : RationalAdeleˣ) * x ∈
              rationalIdeleMeasurableFundamentalDomain := by
          simpa [deltaUnop, mul_comm] using hdelta
        have heq : deltaUnop = gamma := hunique deltaUnop hdu
        apply Subtype.ext
        exact congrArg (fun z : rationalIdeleDiagonalSubgroup ↦
          MulOpposite.op (z : RationalAdeleˣ)) heq)

/-- The idele-class Weil quotient induced from the exact differential ambient
measure and exact rational-diagonal transversal. -/
noncomputable def rationalIdeleClassDifferentialWeilQuotientMeasure :
    Measure RationalIdeleClassGroup :=
  Measure.map rationalIdeleClassQuotientMap
    (rationalIdeleDifferentialHaarMeasure.restrict
      rationalIdeleMeasurableFundamentalDomain)

noncomputable instance rationalIdeleClassDifferentialHasFundamentalDomain :
    HasFundamentalDomain rationalIdeleDiagonalSubgroup.op RationalAdeleˣ
      rationalIdeleDifferentialHaarMeasure :=
  ⟨⟨rationalIdeleMeasurableFundamentalDomain,
    rationalIdeleDifferentialHaar_isFundamentalDomain_op⟩⟩

noncomputable instance
    rationalIdeleClassDifferentialWeilQuotientMeasure_eq_preimage :
    QuotientMeasureEqMeasurePreimage rationalIdeleDifferentialHaarMeasure
      rationalIdeleClassDifferentialWeilQuotientMeasure := by
  unfold rationalIdeleClassDifferentialWeilQuotientMeasure
  exact
    rationalIdeleDifferentialHaar_isFundamentalDomain_op
      |>.quotientMeasureEqMeasurePreimage_quotientMeasure

/-- Restriction of differential idele Haar to the exact transversal maps
measure-preservingly onto its induced Weil quotient. -/
theorem measurePreserving_rationalIdeleClassQuotientMap_differentialDomain :
    MeasurePreserving rationalIdeleClassQuotientMap
      (rationalIdeleDifferentialHaarMeasure.restrict
        rationalIdeleMeasurableFundamentalDomain)
      rationalIdeleClassDifferentialWeilQuotientMeasure :=
  measurePreserving_quotientGroup_mk_of_QuotientMeasureEqMeasurePreimage
    rationalIdeleDifferentialHaarMeasure
    rationalIdeleDifferentialHaar_isFundamentalDomain_op
    rationalIdeleClassDifferentialWeilQuotientMeasure

/-- The differential quotient carries exactly the same scalar as its ambient
measure relative to the certified reference Weil quotient. -/
theorem rationalIdeleClassDifferentialWeilQuotientMeasure_eq_smul_reference :
    rationalIdeleClassDifferentialWeilQuotientMeasure =
      rationalIdeleDifferentialToReferenceHaarScalar •
        rationalIdeleClassReferenceWeilQuotientMeasure := by
  unfold rationalIdeleClassDifferentialWeilQuotientMeasure
    rationalIdeleClassReferenceWeilQuotientMeasure
  rw [rationalIdeleDifferentialHaarMeasure_eq_smul_referenceHaar,
    Measure.restrict_smul, Measure.map_smul]

end RationalQuadraticSpaceMatrix

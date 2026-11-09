import Mathlib.MeasureTheory.Measure.Haar.Quotient
import SMSFormula.CoveringMapBorel
import SMSFormula.RationalIdeleClassMeasurableFundamentalDomain

/-!
# A reference-Haar Weil quotient on rational idele classes

The exact measurable transversal is promoted to Mathlib's fundamental-domain
structure for the rational diagonal.  Restricting arbitrary ambient idele
Haar to this domain and pushing it to the literal quotient gives a certified
quotient measure satisfying the quotient-preimage Weil identity.  The domain
is not asserted to have finite mass, and this file does not identify the
resulting scale with the independently selected idele-class Haar measure.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Set

namespace RationalQuadraticSpaceMatrix

local instance : MulAction RationalAdeleˣ RationalAdeleˣ :=
  Monoid.toMulAction RationalAdeleˣ

local instance : MulAction rationalIdeleDiagonalSubgroup RationalAdeleˣ :=
  Subgroup.instMulAction

local instance rationalIdeleDiagonalSubgroupCountable :
    Countable rationalIdeleDiagonalSubgroup :=
  rationalIdeleDiagonalSubgroup_countable

local instance rationalIdeleDiagonalSubgroupOpCountable :
    Countable rationalIdeleDiagonalSubgroup.op := by
  let unopEquiv : rationalIdeleDiagonalSubgroup.op →
      rationalIdeleDiagonalSubgroup := fun gamma ↦
    ⟨MulOpposite.unop (gamma : RationalAdeleˣᵐᵒᵖ), gamma.2⟩
  apply Function.Injective.countable (f := unopEquiv)
  intro gamma delta h
  apply Subtype.ext
  exact MulOpposite.unop_injective (congrArg Subtype.val h)

/-- Arbitrary reference Haar on the literal rational idele group.  Its scale
will later be replaced by the restricted-product differential scale. -/
noncomputable def rationalIdeleReferenceHaarMeasure : Measure RationalAdeleˣ :=
  Measure.haar

noncomputable instance rationalIdeleReferenceHaarMeasureIsHaar :
    Measure.IsHaarMeasure rationalIdeleReferenceHaarMeasure := by
  unfold rationalIdeleReferenceHaarMeasure
  infer_instance

noncomputable instance rationalIdeleReferenceHaarMeasureIsRightInvariant :
    Measure.IsMulRightInvariant rationalIdeleReferenceHaarMeasure := by
  infer_instance

noncomputable instance rationalIdeleReferenceHaarMeasureSigmaFinite :
    SigmaFinite rationalIdeleReferenceHaarMeasure := by
  unfold rationalIdeleReferenceHaarMeasure Measure.haar
  infer_instance

/-- Every idele has exactly one rational-diagonal translate in the chosen
measurable fundamental domain. -/
theorem existsUnique_rationalIdeleDiagonal_mul_mem_measurableFundamentalDomain
    (x : RationalAdeleˣ) :
    ∃! gamma : rationalIdeleDiagonalSubgroup,
      (gamma : RationalAdeleˣ) * x ∈ rationalIdeleMeasurableFundamentalDomain := by
  rcases existsUnique_rationalIdeleFundamentalDomainRepresentative x with
    ⟨z, hz, hunique⟩
  let gamma : rationalIdeleDiagonalSubgroup :=
    ⟨z * x⁻¹, (QuotientGroup.eq_iff_div_mem.mp hz.2)⟩
  have hgamma :
      (gamma : RationalAdeleˣ) * x ∈ rationalIdeleMeasurableFundamentalDomain := by
    simpa [gamma, mul_assoc] using hz.1
  refine ⟨gamma, hgamma, ?_⟩
  intro delta hdelta
  have hmul :
      (delta : RationalAdeleˣ) * x = (gamma : RationalAdeleˣ) * x :=
    rationalIdeleClassQuotientMap_injOn_fundamentalDomain hdelta hgamma (by
      unfold rationalIdeleClassQuotientMap
      change
        QuotientGroup.mk' rationalIdeleDiagonalSubgroup
            ((delta : RationalAdeleˣ) * x) =
          QuotientGroup.mk' rationalIdeleDiagonalSubgroup
            ((gamma : RationalAdeleˣ) * x)
      rw [map_mul, map_mul]
      have hdelta_one :
          QuotientGroup.mk' rationalIdeleDiagonalSubgroup
              (delta : RationalAdeleˣ) = 1 :=
        QuotientGroup.eq_one_iff _ |>.mpr delta.2
      have hgamma_one :
          QuotientGroup.mk' rationalIdeleDiagonalSubgroup
              (gamma : RationalAdeleˣ) = 1 :=
        QuotientGroup.eq_one_iff _ |>.mpr gamma.2
      rw [hdelta_one, hgamma_one])
  exact Subtype.ext (mul_right_cancel hmul)

/-- The chosen transversal is a fundamental domain for multiplication by the
rational diagonal. -/
theorem rationalIdeleReferenceHaar_isFundamentalDomain :
    IsFundamentalDomain rationalIdeleDiagonalSubgroup
      rationalIdeleMeasurableFundamentalDomain rationalIdeleReferenceHaarMeasure :=
  IsFundamentalDomain.mk'
    measurableSet_rationalIdeleMeasurableFundamentalDomain.nullMeasurableSet
    (by
      intro x
      change ∃! gamma : rationalIdeleDiagonalSubgroup,
        (gamma : RationalAdeleˣ) * x ∈ rationalIdeleMeasurableFundamentalDomain
      exact existsUnique_rationalIdeleDiagonal_mul_mem_measurableFundamentalDomain x)

/-- The same exact domain for the opposite subgroup action used by Mathlib's
normal-quotient Haar theory. -/
theorem rationalIdeleReferenceHaar_isFundamentalDomain_op :
    IsFundamentalDomain rationalIdeleDiagonalSubgroup.op
      rationalIdeleMeasurableFundamentalDomain rationalIdeleReferenceHaarMeasure :=
  IsFundamentalDomain.mk'
    measurableSet_rationalIdeleMeasurableFundamentalDomain.nullMeasurableSet
    (by
      intro x
      rcases
          existsUnique_rationalIdeleDiagonal_mul_mem_measurableFundamentalDomain x with
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

/-- The idele-class quotient measure induced from reference ambient Haar and
the exact measurable transversal. -/
noncomputable def rationalIdeleClassReferenceWeilQuotientMeasure :
    Measure RationalIdeleClassGroup :=
  Measure.map rationalIdeleClassQuotientMap
    (rationalIdeleReferenceHaarMeasure.restrict
      rationalIdeleMeasurableFundamentalDomain)

noncomputable instance rationalIdeleClassReferenceHasFundamentalDomain :
    HasFundamentalDomain rationalIdeleDiagonalSubgroup.op RationalAdeleˣ
      rationalIdeleReferenceHaarMeasure :=
  ⟨⟨rationalIdeleMeasurableFundamentalDomain,
    rationalIdeleReferenceHaar_isFundamentalDomain_op⟩⟩

/-- The reference quotient satisfies the exact quotient-preimage Weil
normalization against ambient reference Haar. -/
noncomputable instance rationalIdeleClassReferenceWeilQuotientMeasure_eq_preimage :
    QuotientMeasureEqMeasurePreimage rationalIdeleReferenceHaarMeasure
      rationalIdeleClassReferenceWeilQuotientMeasure := by
  unfold rationalIdeleClassReferenceWeilQuotientMeasure
  exact
    rationalIdeleReferenceHaar_isFundamentalDomain_op
      |>.quotientMeasureEqMeasurePreimage_quotientMeasure

/-- Restriction of ambient reference Haar to the exact domain maps
measure-preservingly onto the certified reference quotient. -/
theorem measurePreserving_rationalIdeleClassQuotientMap_referenceDomain :
    MeasurePreserving rationalIdeleClassQuotientMap
      (rationalIdeleReferenceHaarMeasure.restrict
        rationalIdeleMeasurableFundamentalDomain)
      rationalIdeleClassReferenceWeilQuotientMeasure :=
  measurePreserving_quotientGroup_mk_of_QuotientMeasureEqMeasurePreimage
    rationalIdeleReferenceHaarMeasure
    rationalIdeleReferenceHaar_isFundamentalDomain_op
    rationalIdeleClassReferenceWeilQuotientMeasure

end RationalQuadraticSpaceMatrix

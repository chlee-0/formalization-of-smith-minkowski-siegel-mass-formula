import SMSFormula.RationalSpecialOrthogonalFiniteAdelicDifferentialMeasureNormalization
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Regularity of the general finite-adelic differential measure

The everywhere-integral local factors are compact.  Their direct product is
therefore compact, and the direct block and genuine-block
homeomorphisms identify it with the open empty principal block in the genuine
finite-adelic special-orthogonal group.  This compact-open identity
neighborhood supplies local compactness of the full group.  Together with an
explicit second-countability instance and local finiteness, this proves regularity of the general finite invariant-
differential measure.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 400000

/-! ## Compactness of the empty principal block -/

/-- Every carrier-independent integral local factor is a compact space. -/
noncomputable instance heightOnePadicSpecialOrthogonalIntegralGroupCompactSpace
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    CompactSpace (V.HeightOnePadicSpecialOrthogonalIntegralGroup v) :=
  isCompact_iff_compactSpace.mp
    (V.isCompact_heightOnePadicSpecialOrthogonalIntegralSubgroup v)

/-- The product of the integral local factors away from a finite set is
compact in its direct product topology. -/
noncomputable instance finiteAdelicSpecialOrthogonalIntegralTailCompactSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    CompactSpace (V.FiniteAdelicSpecialOrthogonalIntegralTail S) := by
  infer_instance

private noncomputable instance
    finiteAdelicSpecialOrthogonalExceptionalProductEmptyCompactSpace
    (V : RationalQuadraticSpaceMatrix n) :
    CompactSpace (V.FiniteAdelicSpecialOrthogonalExceptionalProduct ∅) := by
  infer_instance

/-- The direct mixed empty principal block is compact. -/
noncomputable instance
    finiteAdelicSpecialOrthogonalMixedPrincipalBlockEmptyCompactSpace
    (V : RationalQuadraticSpaceMatrix n) :
    CompactSpace
      (V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock ∅) := by
  exact
    (V.finiteAdelicSpecialOrthogonalExceptionalTailMixedHomeomorph ∅).compactSpace

/-- The genuine empty principal block is compact for its actual finite-adele
subtype topology. -/
noncomputable instance
    finiteAdelicSpecialOrthogonalGenuinePrincipalBlockEmptyCompactSpace
    (V : RationalQuadraticSpaceMatrix n) :
    CompactSpace
      (V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock ∅) := by
  exact
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph ∅).symm.compactSpace

/-- The open everywhere-integral principal subgroup is compact in the genuine
finite-adelic special-orthogonal group. -/
theorem isCompact_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup_empty
    (V : RationalQuadraticSpaceMatrix n) :
    IsCompact
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup ∅ :
        Set V.FiniteAdelicSpecialOrthogonalGroup) := by
  have hrange :
      Set.range
          (fun a : V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock ∅ =>
            (a : V.FiniteAdelicSpecialOrthogonalGroup)) =
        (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup ∅ :
          Set V.FiniteAdelicSpecialOrthogonalGroup) := by
    ext a
    simp
  rw [← hrange]
  simpa only [Set.image_univ] using
    (CompactSpace.isCompact_univ.image
      (continuous_subtype_val : Continuous
        (fun a : V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock ∅ =>
          (a : V.FiniteAdelicSpecialOrthogonalGroup))))

/-! ## Local compactness and regularity -/

/-- The compact-open empty principal block, bundled as a positive compact
identity neighborhood. -/
def finiteAdelicSpecialOrthogonalEmptyBlockPositiveCompacts
    (V : RationalQuadraticSpaceMatrix n) :
    TopologicalSpace.PositiveCompacts
      V.FiniteAdelicSpecialOrthogonalGroup where
  carrier :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup ∅
  isCompact' :=
    V.isCompact_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup_empty
  interior_nonempty' := by
    rw [(V.isOpen_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup
      ∅).interior_eq]
    exact ⟨1, Subgroup.one_mem _⟩

/-- The general finite-adelic special-orthogonal group is locally compact,
directly from its compact-open integral block. -/
noncomputable instance finiteAdelicSpecialOrthogonalGroupLocallyCompactSpace
    (V : RationalQuadraticSpaceMatrix n) :
    LocallyCompactSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  V.finiteAdelicSpecialOrthogonalEmptyBlockPositiveCompacts
    |>.locallyCompactSpace_of_group

local instance finiteAdelicDifferentialRegularityMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  borel _

local instance finiteAdelicDifferentialRegularityBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

/-- The general finite-adelic invariant-differential measure is Haar at its
literal mass-one compact-open integral normalization. -/
theorem finiteAdelicInvariantDifferentialGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsHaarMeasure
      V.finiteAdelicInvariantDifferentialGroupMeasure := by
  let K : Set V.FiniteAdelicSpecialOrthogonalGroup :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup ∅
  apply Measure.isHaarMeasure_of_isCompact_nonempty_interior
    V.finiteAdelicInvariantDifferentialGroupMeasure K
  · exact
      V.isCompact_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup_empty
  · rw [(V.isOpen_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup
      ∅).interior_eq]
    exact ⟨1, Subgroup.one_mem _⟩
  · rw [V.finiteAdelicInvariantDifferentialGroupMeasure_emptyBlock]
    exact one_ne_zero
  · rw [V.finiteAdelicInvariantDifferentialGroupMeasure_emptyBlock]
    exact ENNReal.one_ne_top

/-- The general finite-adelic invariant-differential measure is regular. -/
theorem finiteAdelicInvariantDifferentialGroupMeasure_regular
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.Regular V.finiteAdelicInvariantDifferentialGroupMeasure := by
  letI : RegularSpace V.FiniteAdelicSpecialOrthogonalGroup :=
    IsTopologicalGroup.regularSpace V.FiniteAdelicSpecialOrthogonalGroup
  letI : TopologicalSpace.PseudoMetrizableSpace
      V.FiniteAdelicSpecialOrthogonalGroup :=
    TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTopology
      V.FiniteAdelicSpecialOrthogonalGroup
  exact
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure
      V.finiteAdelicInvariantDifferentialGroupMeasure

end RationalQuadraticSpaceMatrix

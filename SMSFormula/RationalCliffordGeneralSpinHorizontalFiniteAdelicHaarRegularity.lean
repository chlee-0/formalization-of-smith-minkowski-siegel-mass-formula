import SMSFormula.RationalCliffordGeneralSpinHorizontalBlockHaar

/-!
# Haar regularity of the horizontal finite-adelic general Spin measure

Exact recovery on the open genuine Haar blocks makes the directed horizontal
finite-adelic measure locally finite and positive on every nonempty open set.
Together with its established global left invariance, this packages the
measure as Haar at its explicit coherent cylinder scale.
-/

noncomputable section

open MeasureTheory
open Topology
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 2000000

local instance horizontalFiniteHaarMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance horizontalFiniteHaarBorelSpace
    (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

local instance horizontalFiniteHaarBlockBorelSpace
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
  Subtype.borelSpace _

/-- The finite-adelic intrinsic `GSpin` carrier is second countable through
its finite coordinate embedding. -/
noncomputable instance finiteAdelicCliffordGeneralSpinGroupSecondCountableTopology_horizontal
    (V : RationalQuadraticSpaceMatrix n) :
    SecondCountableTopology V.FiniteAdelicCliffordGeneralSpinGroup := by
  let hClifford : SecondCountableTopology
      (Finset (Fin n) → RationalFiniteAdele) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology RationalFiniteAdeleᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology
      (RationalFiniteAdele × RationalFiniteAdeleᵐᵒᵖ) :=
    inferInstance
  let hUnits : SecondCountableTopology RationalFiniteAdeleˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  let hMatrix : SecondCountableTopology
      (Matrix (Fin n) (Fin n) RationalFiniteAdele) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI := hClifford
  letI := hUnits
  letI := hMatrix
  let hTarget : SecondCountableTopology
      (((Finset (Fin n) → RationalFiniteAdele) × RationalFiniteAdeleˣ) ×
        (Matrix (Fin n) (Fin n) RationalFiniteAdele ×
          Matrix (Fin n) (Fin n) RationalFiniteAdele)) :=
    @TopologicalSpace.instSecondCountableTopologyProd _ _ _ _
      (@TopologicalSpace.instSecondCountableTopologyProd _ _ _ _
        hClifford hUnits)
      (@TopologicalSpace.instSecondCountableTopologyProd _ _ _ _
        hMatrix hMatrix)
  letI := hTarget
  exact (V.cliffordGeneralSpinPointCoordinateMap_isEmbedding RationalFiniteAdele)
    |>.secondCountableTopology

/-- Exact recovery on the open Haar blocks makes the directed finite-adelic
horizontal measure locally finite. -/
instance finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isLocallyFinite
    (V : RationalQuadraticSpaceMatrix n) :
    IsLocallyFiniteMeasure
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  constructor
  intro x
  obtain ⟨S, hxS⟩ :=
    V.exists_mem_cliffordGeneralSpinHorizontalGenuinePrincipalBlock x
  let iS :=
    V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S
  let xS : V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S := ⟨x, hxS⟩
  let μS := V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S
  letI : LocallyCompactSpace
      (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
    (V.isOpen_cliffordGeneralSpinHorizontalGenuinePrincipalBlock S)
      |>.locallyCompactSpace
  letI : Measure.IsHaarMeasure μS :=
    V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_isHaarMeasure S
  letI : IsLocallyFiniteMeasure μS := by infer_instance
  obtain ⟨U, hxU, hUopen, hUfinite⟩ := μS.exists_isOpen_measure_lt_top xS
  refine ⟨iS '' U, ?_, ?_⟩
  · have hiSOpen : IsOpenEmbedding iS :=
      (V.isOpen_cliffordGeneralSpinHorizontalGenuinePrincipalBlock S)
        |>.isOpenEmbedding_subtypeVal
    exact (hiSOpen.isOpenMap U hUopen).mem_nhds ⟨xS, hxU, rfl⟩
  · rw [←
      (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
        S).comap_apply,
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_comap_genuineBlock]
    exact hUfinite

/-- The directed finite-adelic horizontal measure is positive on every
nonempty open set. -/
theorem finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isOpenPosMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsOpenPosMeasure
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  constructor
  intro U hU hUne
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨S, hxS⟩ :=
    V.exists_mem_cliffordGeneralSpinHorizontalGenuinePrincipalBlock x
  let iS :=
    V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion S
  let μS := V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure S
  letI : Measure.IsHaarMeasure μS :=
    V.cliffordGeneralSpinHorizontalCoherentGenuinePrincipalBlockMeasure_isHaarMeasure S
  let W : Set (V.CliffordGeneralSpinHorizontalGenuinePrincipalBlock S) :=
    iS ⁻¹' U
  have hWopen : IsOpen W := hU.preimage continuous_subtype_val
  have hWne : W.Nonempty := ⟨⟨x, hxS⟩, hxU⟩
  have hWsub : iS '' W ⊆ U := Set.image_preimage_subset iS U
  exact ne_of_gt <| calc
    0 < μS W := hWopen.measure_pos μS hWne
    _ = V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure (iS '' W) := by
      rw [←
        (V.cliffordGeneralSpinHorizontalGenuinePrincipalBlockAmbientInclusion_measurableEmbedding
          S).comap_apply,
        V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_comap_genuineBlock]
    _ ≤ V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure U :=
      measure_mono hWsub

/-- The directed finite-adelic horizontal measure is Haar at its explicit
coherent block scale. -/
theorem finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isHaarMeasure
    (V : RationalQuadraticSpaceMatrix n) :
    Measure.IsHaarMeasure
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure := by
  letI : IsLocallyFiniteMeasure
      V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
    V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isLocallyFinite
  refine
    { toIsMulLeftInvariant :=
        V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isMulLeftInvariant
      toIsOpenPosMeasure :=
        V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isOpenPosMeasure
      lt_top_of_isCompact := fun _K hK ↦
        hK.measure_lt_top_of_nhdsWithin fun _ _ ↦
          V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure.finiteAt_nhdsWithin
            _ _ }

instance finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure_isSigmaFinite
    (V : RationalQuadraticSpaceMatrix n) :
    SigmaFinite V.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure :=
  sigmaFinite_of_locallyFinite

end RationalQuadraticSpaceMatrix

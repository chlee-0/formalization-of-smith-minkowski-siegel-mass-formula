import SMSFormula.RationalCliffordGeneralSpinHorizontalFiberHaarKernel
import SMSFormula.RationalCliffordGeneralSpinLatticeFullAdelicSOSurjectivity
import SMSFormula.SpecialOrthogonalFullAdelicProperQuotientMeasurableEquiv
import SMSFormula.SpecialOrthogonalFullAdelicRealFiniteCosetTransport
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measurable descent of the horizontal fiber-Haar kernel

This module completes measurable descent of the horizontal fiber-Haar kernel.
For a lattice form, the rational adelic `SO` quotient is countably separated
through its exact measurable proper-domain model.  Full adelic intrinsic
`GSpin` is Polish through its right uniformity, local compactness, and the
existing finite-coordinate second-countability theorem.  The composite from
that standard-Borel group through the rational `GSpin` quotient to the `SO`
quotient is a measurable surjection, so Mathlib's measurable-surjection
theorem descends the existing measurable pullback.

The resulting genuine `SO`-indexed kernel pulls back exactly to the original
section-free horizontal fiber-Haar kernel.  No measurable lift or topological-
quotient assertion is used.
-/

noncomputable section

open MeasureTheory
open MeasurableSpace
open Filter
open PositiveDefiniteIntegralLattice
open scoped ProbabilityTheory Uniformity

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Full adelic intrinsic `GSpin` is Polish for its existing finite-coordinate
topology.  The right uniformity is complete by local compactness, while the
existing adelic Borel comparison supplies second countability. -/
noncomputable def
    fullAdelicCliffordGeneralSpinGroupPolishSpaceForMeasurableDescent :
    PolishSpace V.FullAdelicCliffordGeneralSpinGroup := by
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalAdele := by
    change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
    infer_instance
  letI : SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology
  letI : UniformSpace V.FullAdelicCliffordGeneralSpinGroup :=
    IsTopologicalGroup.rightUniformSpace _
  letI : IsRightUniformGroup V.FullAdelicCliffordGeneralSpinGroup := ⟨rfl⟩
  letI : FirstCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  letI : CompleteSpace V.FullAdelicCliffordGeneralSpinGroup :=
    IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace
  haveI : (𝓤 V.FullAdelicCliffordGeneralSpinGroup).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_one'
      V.FullAdelicCliffordGeneralSpinGroup]
    exact Filter.comap.isCountablyGenerated _ _
  letI : T1Space V.FullAdelicCliffordGeneralSpinGroup := T2Space.t1Space
  letI : T0Space V.FullAdelicCliffordGeneralSpinGroup := T1Space.t0Space
  letI : TopologicalSpace.IsCompletelyMetrizableSpace
      V.FullAdelicCliffordGeneralSpinGroup :=
    TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
  exact {}

/-- The existing Borel measurable structure on full adelic intrinsic `GSpin`
is standard Borel. -/
noncomputable def
    fullAdelicCliffordGeneralSpinGroupStandardBorelSpaceForMeasurableDescent :
    StandardBorelSpace V.FullAdelicCliffordGeneralSpinGroup := by
  letI : PolishSpace V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupPolishSpaceForMeasurableDescent
  infer_instance

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1800000

private theorem countablySeparated_of_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) [CountablySeparated β] : CountablySeparated α := by
  refine ⟨?_⟩
  rcases (inferInstance : CountablySeparated β).countably_separated.1 with
    ⟨S, hScount, hSmeas, hSsep⟩
  refine ⟨⟨(fun s : Set β => e ⁻¹' s) '' S, hScount.image _, ?_, ?_⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact e.measurable (hSmeas s hs)
  · intro x _ y _ hxy
    apply e.injective
    apply hSsep (e x) (Set.mem_univ _) (e y) (Set.mem_univ _)
    intro s hs
    simpa only [Set.mem_preimage] using hxy (e ⁻¹' s) ⟨s, hs, rfl⟩

private theorem countablySeparated_subtype
    {α : Type*} [MeasurableSpace α] [CountablySeparated α]
    (s : Set α) : CountablySeparated s := by
  refine ⟨?_⟩
  rcases (inferInstance : CountablySeparated α).countably_separated.1 with
    ⟨S, hScount, hSmeas, hSsep⟩
  refine ⟨⟨(fun t : Set α => Subtype.val ⁻¹' t) '' S,
    hScount.image _, ?_, ?_⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact measurable_subtype_coe (hSmeas t ht)
  · intro x _ y _ hxy
    apply Subtype.ext
    apply hSsep x.1 (Set.mem_univ _) y.1 (Set.mem_univ _)
    intro t ht
    simpa only [Set.mem_preimage] using hxy (Subtype.val ⁻¹' t) ⟨t, ht, rfl⟩

/-- The rational adelic `SO` quotient of a lattice form is countably
separated through its exact measurable proper-domain model. -/
theorem fullAdelicSpecialOrthogonalLeftQuotient_countablySeparated
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    CountablySeparated
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient := by
  let e :=
    (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientMeasurableEquiv).trans
      (L.concreteFullAdelicSpecialOrthogonalLeftQuotientProperDomainMeasurableEquiv
        inst)
  letI : SecondCountableTopology
      L.ConcreteFullAdelicSpecialOrthogonalGroup :=
    L.concreteFullAdelicSpecialOrthogonalGroupSecondCountableTopology
  letI : T2Space L.ConcreteRealSpecialOrthogonalGroup := by
    infer_instance
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space (Matrix (Fin (r + 2)) (Fin (r + 2)) RationalFiniteAdele) :=
    inferInstance
  letI : T2Space
      (Matrix (Fin (r + 2)) (Fin (r + 2)) RationalFiniteAdele)ˣ :=
    Units.isEmbedding_embedProduct.t2Space
  letI : T2Space L.ConcreteFiniteAdelicOrthogonalGroup :=
    L.isClosed_finiteAdelicOrthogonalMatrixSubgroup
      |>.isClosedEmbedding_subtypeVal.isEmbedding.t2Space
  letI : T2Space L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
    L.isClosed_finiteAdelicSpecialOrthogonalMatrixSubgroup
      |>.isClosedEmbedding_subtypeVal.isEmbedding.t2Space
  letI : T2Space
      (L.ConcreteRealSpecialOrthogonalGroup ×
        L.ConcreteFiniteAdelicSpecialOrthogonalGroup) := by
    infer_instance
  letI : T2Space L.ConcreteFullAdelicSpecialOrthogonalGroup :=
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm
      |>.toHomeomorph.t2Space
  letI : T1Space L.ConcreteFullAdelicSpecialOrthogonalGroup :=
    T2Space.t1Space
  letI : CountablyGenerated L.ConcreteFullAdelicSpecialOrthogonalGroup :=
    BorelSpace.countablyGenerated
  letI : SeparatesPoints L.ConcreteFullAdelicSpecialOrthogonalGroup := by
    constructor
    intro x y hxy
    by_contra hne
    have hmeas : MeasurableSet ({y}ᶜ :
        Set L.ConcreteFullAdelicSpecialOrthogonalGroup) :=
      (isClosed_singleton : IsClosed ({y} :
        Set L.ConcreteFullAdelicSpecialOrthogonalGroup)).isOpen_compl.measurableSet
    have hx : x ∈ ({y}ᶜ :
        Set L.ConcreteFullAdelicSpecialOrthogonalGroup) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne
    exact (hxy _ hmeas hx) (by simp)
  letI : CountablySeparated L.ConcreteFullAdelicSpecialOrthogonalGroup :=
    countablySeparated_of_separatesPoints
  letI : CountablySeparated
      {z : L.ConcreteFullAdelicSpecialOrthogonalGroup //
        z ∈ L.concreteFullAdelicProperTransversal} := by
    exact countablySeparated_subtype
      L.concreteFullAdelicProperTransversal
  exact countablySeparated_of_measurableEquiv e

/-- The representative-independent horizontal fiber-Haar family is measurable
on the lattice rational adelic `SO` quotient.  The standard-Borel source is
the full adelic `GSpin` group itself, mapped surjectively through its rational
left quotient and then the horizontal map. -/
theorem measurable_horizontalFiberHaarMeasureAtSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    Measurable
      (L.rationalQuadraticSpaceMatrix.horizontalFiberHaarMeasureAtSO
        (fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective
          L)) := by
  let V := L.rationalQuadraticSpaceMatrix
  let hsurj :=
    fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective L
  let f : V.FullAdelicCliffordGeneralSpinGroup →
      V.FullAdelicSpecialOrthogonalLeftQuotient :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal ∘
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap
  letI : StandardBorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupStandardBorelSpaceForMeasurableDescent
  letI : CountablySeparated
      V.FullAdelicSpecialOrthogonalLeftQuotient :=
    L.fullAdelicSpecialOrthogonalLeftQuotient_countablySeparated inst
  have hf : Measurable f :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_measurable.comp
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap_measurable
  have hqsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap := by
    intro q
    induction q using Quot.inductionOn with
    | _ x => exact ⟨x, rfl⟩
  have hfsurj : Function.Surjective f := hsurj.comp hqsurj
  apply (hf.measurable_comp_iff_of_surjective hfsurj).mp
  simpa only [f, Function.comp_def] using
    (V.measurable_horizontalFiberHaarMeasureAtSO_comp_horizontalMap hsurj).comp
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap_measurable

/-- The genuine measurable horizontal fiber-Haar kernel indexed by the
lattice rational adelic `SO` quotient. -/
noncomputable def horizontalFiberHaarKernelAtSO
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) :
    ProbabilityTheory.Kernel
      L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient :=
  ⟨L.rationalQuadraticSpaceMatrix.horizontalFiberHaarMeasureAtSO
      (fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective
        L),
    L.measurable_horizontalFiberHaarMeasureAtSO inst⟩

@[simp]
theorem horizontalFiberHaarKernelAtSO_apply
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (q : L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalLeftQuotient) :
    L.horizontalFiberHaarKernelAtSO inst q =
      L.rationalQuadraticSpaceMatrix.horizontalFiberHaarMeasureAtSO
        (fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective
          L) q :=
  rfl

/-- Pulling the descended kernel back along the horizontal map recovers the
original section-free measurable kernel exactly. -/
theorem horizontalFiberHaarKernelAtSO_comp_horizontalMap
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (z : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient) :
    L.horizontalFiberHaarKernelAtSO inst
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal
          z) =
      L.rationalQuadraticSpaceMatrix.horizontalFiberHaarKernel z := by
  rw [L.horizontalFiberHaarKernelAtSO_apply,
    L.rationalQuadraticSpaceMatrix.horizontalFiberHaarKernel_apply]
  exact
    L.rationalQuadraticSpaceMatrix.horizontalFiberHaarMeasureAtSO_image
      (fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_surjective
        L) z

end PositiveDefiniteIntegralLattice

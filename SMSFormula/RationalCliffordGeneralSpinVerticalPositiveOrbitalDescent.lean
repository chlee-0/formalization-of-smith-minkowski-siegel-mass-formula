import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveSpinWeil
import SMSFormula.RationalCliffordGeneralSpinLatticeFullAdelicSimilitude
import SMSFormula.RationalCliffordGeneralSpinHorizontalMeasurableDescent

/-!
# Descending raw Spin orbital measures to positive ideles

After rational Spin periodization has been removed, the remaining inner
integral is the raw adelic Spin orbital integral on `GSpin(A)`.  This file
packages those orbital measures as a measurable s-finite kernel and descends
it through the actual similitude map onto the positive-idèle image.

The descent uses only exactness of `Spin -> GSpin -> G_m`, raw Spin right-Haar
invariance, and the proved description of the full-adelic similitude image.
The definition-only lift used to name the descended values is not asserted to
be measurable; measurability is proved from the surjective similitude map.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open MeasureTheory
open MeasurableSpace
open scoped ENNReal ProbabilityTheory

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

/-- The actual full-adelic `GSpin` similitude, with codomain restricted to its
positive-idèle image. -/
def fullAdelicCliffordGeneralSpinPositiveSimilitudeHom
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r) :
    L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup →*
      RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup where
  toFun g := ⟨
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom g,
    by
      rw [← L.range_fullAdelicCliffordGeneralSpinSimilitudeHom_eq_positive hr]
      exact ⟨g, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom x y

/-- The positive similitude map is continuous. -/
theorem continuous_fullAdelicCliffordGeneralSpinPositiveSimilitudeHom
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r) :
    Continuous (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr) := by
  exact
    (L.rationalQuadraticSpaceMatrix
      |>.continuous_fullAdelicCliffordGeneralSpinSimilitudeHom).subtype_mk _

/-- Every positive idèle is an actual full-adelic `GSpin` similitude. -/
theorem fullAdelicCliffordGeneralSpinPositiveSimilitudeHom_surjective
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r) :
    Function.Surjective
      (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr) := by
  intro a
  let V := L.rationalQuadraticSpaceMatrix
  have ha : (a : RationalAdeleˣ) ∈
      V.fullAdelicCliffordGeneralSpinSimilitudeHom.range := by
    rw [L.range_fullAdelicCliffordGeneralSpinSimilitudeHom_eq_positive hr]
    exact a.2
  rcases ha with ⟨g, hg⟩
  exact ⟨g, Subtype.ext hg⟩

/-- A definition-only ambient lift of a positive idèle.  Its measurability is
neither claimed nor used. -/
def positiveIdeleGeneralSpinLift
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (a : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup) :
    L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  Classical.choose
    (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom_surjective hr a)

@[simp]
theorem positiveIdeleGeneralSpinLift_similitude
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (a : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup) :
    L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr
        (L.positiveIdeleGeneralSpinLift hr a) = a :=
  Classical.choose_spec
    (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom_surjective hr a)

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance verticalPositiveOrbitalFullGSpinSecondCountableTopology :
    SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
  V.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

/-- Joint left Spin orbit in the ambient full-adelic `GSpin` group. -/
def fullAdelicCliffordGeneralSpinPositiveOrbitalMap :
    V.FullAdelicCliffordGeneralSpinGroup ×
        V.FullAdelicCliffordSpinCandidateGroup →
      V.FullAdelicCliffordGeneralSpinGroup :=
  fun p => V.fullAdelicCliffordSpinCandidateToGeneralSpinHom p.2 * p.1

/-- The joint ambient Spin orbit is continuous. -/
theorem continuous_fullAdelicCliffordGeneralSpinPositiveOrbitalMap :
    Continuous V.fullAdelicCliffordGeneralSpinPositiveOrbitalMap := by
  exact
    (V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom
      RationalAdele).comp continuous_snd |>.mul continuous_fst

end RationalQuadraticSpaceMatrix

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ} {V : RationalQuadraticSpaceMatrix n}

local instance verticalPositiveOrbitalDataFullGSpinSecondCountableTopology :
    SecondCountableTopology V.FullAdelicCliffordGeneralSpinGroup :=
  V.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

/-- Raw adelic Spin Haar is s-finite, without requiring finite total Spin
volume. -/
instance positiveSpinOrbitalAdelicMeasure_sFinite
    (D : V.CliffordSpinCandidateRawOnoTamagawaData) :
    SFinite D.spinData.adelicMeasure := by
  rw [D.spinRaw.adelicMeasure_eq]
  unfold fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure
  letI : SigmaFinite V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure :=
    V.fullAdelicCliffordSpinCandidateCoherentGroupMeasure_sigmaFinite
  infer_instance

/-- Raw adelic Spin Haar, left-multiplied into `GSpin(A)` at every ambient
origin. -/
def positiveSpinOrbitalKernelAtAmbient
    (D : V.CliffordSpinCandidateRawOnoTamagawaData) :
    ProbabilityTheory.Kernel
      V.FullAdelicCliffordGeneralSpinGroup
      V.FullAdelicCliffordGeneralSpinGroup :=
  ProbabilityTheory.Kernel.map
    (ProbabilityTheory.Kernel.id ×ₖ
      ProbabilityTheory.Kernel.const
        V.FullAdelicCliffordGeneralSpinGroup D.spinData.adelicMeasure)
    V.fullAdelicCliffordGeneralSpinPositiveOrbitalMap

instance positiveSpinOrbitalKernelAtAmbient_isSFinite
    (D : V.CliffordSpinCandidateRawOnoTamagawaData) :
    ProbabilityTheory.IsSFiniteKernel
      (D.positiveSpinOrbitalKernelAtAmbient (V := V)) := by
  unfold positiveSpinOrbitalKernelAtAmbient
  infer_instance

/-- The ambient orbital kernel is the literal pushforward of raw Spin Haar. -/
theorem positiveSpinOrbitalKernelAtAmbient_apply
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    D.positiveSpinOrbitalKernelAtAmbient (V := V) g =
      Measure.map
        (fun y : V.FullAdelicCliffordSpinCandidateGroup =>
          V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g)
        D.spinData.adelicMeasure := by
  ext A hA
  rw [positiveSpinOrbitalKernelAtAmbient,
    ProbabilityTheory.Kernel.map_apply'
      _ V.continuous_fullAdelicCliffordGeneralSpinPositiveOrbitalMap.measurable
      _ hA,
    ProbabilityTheory.Kernel.id_prod_apply' _ g
      (V.continuous_fullAdelicCliffordGeneralSpinPositiveOrbitalMap.measurable hA),
    ProbabilityTheory.Kernel.const_apply]
  exact (Measure.map_apply
    ((V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom
      RationalAdele).mul continuous_const |>.measurable) hA).symm

/-- Left multiplication of an ambient origin by an embedded Spin point does
not change its raw Spin orbital measure. -/
theorem positiveSpinOrbitalKernelAtAmbient_spin_mul
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    (s : V.FullAdelicCliffordSpinCandidateGroup)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    D.positiveSpinOrbitalKernelAtAmbient (V := V)
        (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s * g) =
      D.positiveSpinOrbitalKernelAtAmbient (V := V) g := by
  letI : Measure.IsInvInvariant D.spinData.adelicMeasure :=
    D.spinRaw.adelicMeasure_isInvInvariant
  letI : Measure.IsHaarMeasure D.spinData.adelicMeasure := by
    rw [D.spinRaw.adelicMeasure_eq]
    exact V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_isHaarMeasure
      D.spinFiniteScale D.spinRaw.volumeProductCertificate
  letI : Measure.IsMulLeftInvariant D.spinData.adelicMeasure := by
    infer_instance
  letI : Measure.IsMulRightInvariant D.spinData.adelicMeasure :=
    Measure.isMulRightInvariant_of_isInvInvariant D.spinData.adelicMeasure
  rw [D.positiveSpinOrbitalKernelAtAmbient_apply,
    D.positiveSpinOrbitalKernelAtAmbient_apply]
  let orbit := fun y : V.FullAdelicCliffordSpinCandidateGroup =>
    V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g
  let right := fun y : V.FullAdelicCliffordSpinCandidateGroup => y * s
  have horbit : Measurable orbit :=
    (V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom
      RationalAdele).mul continuous_const |>.measurable
  have hright : Measurable right := (continuous_mul_right s).measurable
  calc
    Measure.map
        (fun y : V.FullAdelicCliffordSpinCandidateGroup =>
          V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y *
            (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s * g))
        D.spinData.adelicMeasure =
      Measure.map orbit (Measure.map right D.spinData.adelicMeasure) := by
        rw [Measure.map_map horbit hright]
        congr 1
        funext y
        simp [orbit, right, map_mul, mul_assoc]
    _ = Measure.map orbit D.spinData.adelicMeasure := by
      rw [MeasureTheory.map_mul_right_eq_self]

/-- Exactness of `Spin -> GSpin -> G_m`: equal ambient similitudes give the
same raw Spin orbital measure. -/
theorem positiveSpinOrbitalKernelAtAmbient_eq_of_same_similitude
    (D : V.CliffordSpinCandidateRawOnoTamagawaData)
    {x y : V.FullAdelicCliffordGeneralSpinGroup}
    (hxy : V.fullAdelicCliffordGeneralSpinSimilitudeHom y =
      V.fullAdelicCliffordGeneralSpinSimilitudeHom x) :
    D.positiveSpinOrbitalKernelAtAmbient (V := V) y =
      D.positiveSpinOrbitalKernelAtAmbient (V := V) x := by
  have hker : y * x⁻¹ ∈
      (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
        V RationalAdele).ker := by
    change V.fullAdelicCliffordGeneralSpinSimilitudeHom (y * x⁻¹) = 1
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  rw [← V.range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker
    RationalAdele] at hker
  rcases hker with ⟨s, hs⟩
  change V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s = y * x⁻¹ at hs
  have hy : y = V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s * x := by
    calc
      y = (y * x⁻¹) * x := by simp [mul_assoc]
      _ = V.fullAdelicCliffordSpinCandidateToGeneralSpinHom s * x := by rw [← hs]
  rw [hy]
  exact D.positiveSpinOrbitalKernelAtAmbient_spin_mul s x

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

set_option synthInstance.maxHeartbeats 900000
set_option maxHeartbeats 3000000

/-- The raw Spin orbital measure indexed by a positive idèle.  The chosen
ambient lift is definition-only; representative independence is proved below. -/
def positiveSpinOrbitalMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (a : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup) :
    Measure L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  D.positiveSpinOrbitalKernelAtAmbient
    (L.positiveIdeleGeneralSpinLift hr a)

/-- Pullback along the actual positive similitude recovers the ambient raw
Spin orbital kernel. -/
theorem positiveSpinOrbitalMeasure_projection
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    L.positiveSpinOrbitalMeasure hr D
        (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g) =
      D.positiveSpinOrbitalKernelAtAmbient g := by
  unfold positiveSpinOrbitalMeasure
  apply D.positiveSpinOrbitalKernelAtAmbient_eq_of_same_similitude
  exact congrArg Subtype.val
    (L.positiveIdeleGeneralSpinLift_similitude hr
      (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g))

/-- The descended positive-idèle orbital family is measurable, proved by
descent along the measurable surjective similitude map. -/
theorem measurable_positiveSpinOrbitalMeasure
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData) :
    Measurable (L.positiveSpinOrbitalMeasure hr D) := by
  let V := L.rationalQuadraticSpaceMatrix
  let f := L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr
  letI : StandardBorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
    V.fullAdelicCliffordGeneralSpinGroupStandardBorelSpaceForMeasurableDescent
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalAdele := by
    change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
    infer_instance
  letI : SecondCountableTopology RationalAdeleᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology RationalAdeleˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology
      RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup := by
    exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
  letI : T1Space
      RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup := by
    infer_instance
  letI : CountablyGenerated
      RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup :=
    BorelSpace.countablyGenerated
  letI : SeparatesPoints
      RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup := by
    constructor
    intro x y hxy
    by_contra hne
    have hmeas : MeasurableSet ({y}ᶜ : Set
        RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup) :=
      (isClosed_singleton : IsClosed ({y} : Set
        RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup))
        |>.isOpen_compl.measurableSet
    have hx : x ∈ ({y}ᶜ : Set
        RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne
    exact (hxy _ hmeas hx) (by simp)
  letI : CountablySeparated
      RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup :=
    countablySeparated_of_separatesPoints
  have hf : Measurable f :=
    (L.continuous_fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr).measurable
  have hfsurj : Function.Surjective f :=
    L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom_surjective hr
  apply (hf.measurable_comp_iff_of_surjective hfsurj).mp
  change Measurable (fun g =>
    L.positiveSpinOrbitalMeasure hr D
      (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g))
  rw [show
    (fun g => L.positiveSpinOrbitalMeasure hr D
      (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g)) =
        D.positiveSpinOrbitalKernelAtAmbient by
      funext g
      exact L.positiveSpinOrbitalMeasure_projection hr D g]
  exact D.positiveSpinOrbitalKernelAtAmbient.measurable

/-- The section-free measurable s-finite raw Spin orbital kernel on positive
idèles. -/
def positiveSpinOrbitalKernel
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData) :
    ProbabilityTheory.Kernel
      RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup
      L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup :=
  ⟨L.positiveSpinOrbitalMeasure hr D,
    L.measurable_positiveSpinOrbitalMeasure hr D⟩

instance positiveSpinOrbitalKernel_apply_sFinite
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData) :
    ∀ a, SFinite (L.positiveSpinOrbitalKernel hr D a) := by
  intro a
  change SFinite
    (D.positiveSpinOrbitalKernelAtAmbient
      (L.positiveIdeleGeneralSpinLift hr a))
  infer_instance

@[simp]
theorem positiveSpinOrbitalKernel_apply
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (a : RationalQuadraticSpaceMatrix.positiveRationalAdeleUnitsSubgroup) :
    L.positiveSpinOrbitalKernel hr D a =
      L.positiveSpinOrbitalMeasure hr D a :=
  rfl

/-- Pullback of the descended kernel along actual similitude is literal. -/
theorem positiveSpinOrbitalKernel_projection
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (g : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup) :
    L.positiveSpinOrbitalKernel hr D
        (L.fullAdelicCliffordGeneralSpinPositiveSimilitudeHom hr g) =
      D.positiveSpinOrbitalKernelAtAmbient g :=
  L.positiveSpinOrbitalMeasure_projection hr D g

end PositiveDefiniteIntegralLattice

end

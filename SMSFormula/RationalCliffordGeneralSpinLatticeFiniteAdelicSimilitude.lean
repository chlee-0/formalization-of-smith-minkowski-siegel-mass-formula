import SMSFormula.RationalCliffordGeneralSpinLatticeIntegralSimilitude
import SMSFormula.RationalCliffordGeneralSpinLatticePadicSimilitude

/-!
# Finite-adelic similitudes of the lattice intrinsic general-Spin group

Every finite-adelic unit is lifted componentwise.  At cofinitely many places
the prescribed unit is integral and the rational Clifford structure constants
are integral, so the good-place integral lifting theorem supplies a restricted
family.  The existing coefficientwise restricted-family equivalence then
assembles the local lifts into the literal finite-adelic intrinsic `GSpin`
carrier.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance finiteAdelicGeneralSpinSimilitudePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The height-one component of a finite-adelic unit. -/
def finiteAdelicUnitHeightOneComponentHom
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    RationalFiniteAdeleˣ →* ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ :=
  Units.map (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v).toMonoidHom

/-- A finite-adelic unit and its inverse are integral at cofinitely many
height-one places. -/
theorem eventually_finiteAdelicUnitHeightOneComponent_mem_padicIntegralUnitsSubgroup
    (a : RationalFiniteAdeleˣ) :
    ∀ᶠ v in Filter.cofinite,
      finiteAdelicUnitHeightOneComponentHom v a ∈
        padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  have ha : ∀ᶠ v in Filter.cofinite,
      (a : RationalFiniteAdele) v ∈ v.adicCompletionIntegers ℚ := a.1.2
  have hai : ∀ᶠ v in Filter.cofinite,
      ((a⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele) v ∈
        v.adicCompletionIntegers ℚ := a⁻¹.1.2
  filter_upwards [ha, hai] with v hv hvi
  rw [mem_padicIntegralUnitsSubgroup_iff]
  constructor
  · change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
      (a : RationalFiniteAdele) ∈ PadicInt.subring _
    exact (mem_adicCompletionIntegers_iff_padic v _).1 hv
  · change finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
      ((a⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele) ∈ PadicInt.subring _
    exact (mem_adicCompletionIntegers_iff_padic v _).1 hvi

@[simp]
theorem finiteAdelicCliffordGeneralSpinHeightOneComponent_similitude
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (x : V.FiniteAdelicCliffordGeneralSpinGroup) :
    (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v x).similitude =
      finiteAdelicUnitHeightOneComponentHom v x.similitude :=
  rfl

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance finiteAdelicGeneralSpinLatticeSimilitudePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Every finite-adelic unit is the similitude of a literal finite-adelic
intrinsic general-Spin point attached to a positive-definite lattice of rank
at least three. -/
theorem finiteAdelicCliffordGeneralSpinSimilitudeHom_surjective
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r) :
    Function.Surjective
      L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinSimilitudeHom := by
  classical
  let V := L.rationalQuadraticSpaceMatrix
  intro a
  let av : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ := fun v ↦
    RationalQuadraticSpaceMatrix.finiteAdelicUnitHeightOneComponentHom v a
  have havIntegral : ∀ᶠ v in Filter.cofinite,
      av v ∈ RationalQuadraticSpaceMatrix.padicIntegralUnitsSubgroup
        (Rat.HeightOneSpectrum.primesEquiv v).1 := by
    exact RationalQuadraticSpaceMatrix.eventually_finiteAdelicUnitHeightOneComponent_mem_padicIntegralUnitsSubgroup a
  have hlocal : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      ∃ x : V.HeightOnePadicCliffordGeneralSpinGroup v,
        x.similitude = av v ∧
          (v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅ →
            v ∉ V.cliffordSpinCandidateOddUnimodularBadPlaces →
            V.CliffordGeneralSpinIntegralStructureAt v →
            av v ∈ RationalQuadraticSpaceMatrix.padicIntegralUnitsSubgroup
              (Rat.HeightOneSpectrum.primesEquiv v).1 →
            V.PadicCliffordGeneralSpinIsIntegral
              (Rat.HeightOneSpectrum.primesEquiv v).1 x) := by
    intro v
    by_cases hgood :
        v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅ ∧
          v ∉ V.cliffordSpinCandidateOddUnimodularBadPlaces ∧
          V.CliffordGeneralSpinIntegralStructureAt v ∧
          av v ∈ RationalQuadraticSpaceMatrix.padicIntegralUnitsSubgroup
            (Rat.HeightOneSpectrum.primesEquiv v).1
    · let w : V.CliffordSpinCandidateAdmissibleIntegralPlace ∅ :=
        ⟨v, hgood.1⟩
      obtain ⟨x, hxIntegral, hx⟩ :=
        exists_integral_padicCliffordGeneralSpin_similitude_eq
          L w hgood.2.1 hgood.2.2.1 (av v) hgood.2.2.2
      refine ⟨x, hx, ?_⟩
      intro _ _ _ _
      exact hxIntegral
    · obtain ⟨x, hx⟩ :=
        RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.padicCliffordGeneralSpinSimilitudeHom_surjective
          L (by omega) _ (av v)
      refine ⟨x, hx, ?_⟩
      intro hvAdmissible hvOdd hvStructure hvIntegral
      exact False.elim (hgood ⟨hvAdmissible, hvOdd, hvStructure, hvIntegral⟩)
  let localLift : V.HeightOnePadicCliffordGeneralSpinGroupProduct :=
    fun v ↦ Classical.choose (hlocal v)
  have hlocalNu : ∀ v, (localLift v).similitude = av v := fun v ↦
    (Classical.choose_spec (hlocal v)).1
  have hrestricted :
      V.IsFiniteAdelicCliffordGeneralSpinRestrictedFamily localLift := by
    filter_upwards
      [(V.cliffordSpinCandidateAdmissibleExceptionalPlaces ∅).eventually_cofinite_notMem,
        V.cliffordSpinCandidateOddUnimodularBadPlaces.eventually_cofinite_notMem,
        V.eventually_cliffordGeneralSpinIntegralStructureAt,
        havIntegral]
      with v hvAdmissible hvOdd hvStructure hvIntegral
    exact (Classical.choose_spec (hlocal v)).2
      hvAdmissible hvOdd hvStructure hvIntegral
  let g : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily :=
    ⟨localLift, hrestricted⟩
  let x : V.FiniteAdelicCliffordGeneralSpinGroup :=
    V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly g
  refine ⟨x, ?_⟩
  apply Units.ext
  ext v
  apply (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
  have hcomponents := congrFun
    (V.finiteAdelicCliffordGeneralSpinHeightOneComponents_assembly g) v
  have hnu := congrArg
    (fun y : V.HeightOnePadicCliffordGeneralSpinGroup v ↦
      (y.similitude : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) hcomponents
  change RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
      (x.similitude : RationalFiniteAdele) =
    RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
      (a : RationalFiniteAdele)
  calc
    RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
        (x.similitude : RationalFiniteAdele) =
        ((V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom x v).similitude :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := rfl
    _ = ((localLift v).similitude :
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
      simpa [x] using hnu
    _ = (av v : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :=
      congrArg Units.val (hlocalNu v)
    _ = RationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
        (a : RationalFiniteAdele) := rfl

/-- The finite-adelic intrinsic general-Spin similitude image is the whole
finite-idelic unit group. -/
theorem range_finiteAdelicCliffordGeneralSpinSimilitudeHom_eq_top
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordGeneralSpinSimilitudeHom.range =
      ⊤ :=
  MonoidHom.range_eq_top.mpr
    (finiteAdelicCliffordGeneralSpinSimilitudeHom_surjective L hr)

end PositiveDefiniteIntegralLattice

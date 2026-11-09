import SMSFormula.RationalCliffordGeneralSpinBlockFieldShell
import SMSFormula.RationalCliffordGeneralSpinIntegralShellLift
import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicRestrictedFamily
import SMSFormula.RationalCliffordGeneralSpinLatticeFiniteAdelicSimilitude

/-!
# Finite-adelic intrinsic GSpin block shells

The field-valued block-shell orbit is assembled here over the rational finite
adeles.  At cofinitely many places the target vector has integral coordinates,
the rational shell value is a p-adic unit, and the rational Clifford data are
integral.  The certified local integral shell lift is used precisely there;
arbitrary field lifts are used only at the remaining finite set.  The resulting
restricted family is then assembled through the existing intrinsic finite-
adelic carrier.

No unrestricted componentwise product, cutoff, measure, or Fourier statement
occurs here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance finiteAdelicBlockShellPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

/-- At one certified good place, an integral local coordinate of a finite-
adelic block-shell point has an integral intrinsic GSpin lift. -/
theorem exists_integral_heightOne_nonisotropicLastShellOrbitMap_eq
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvOdd : v ∉
      (W.nonisotropicLastExtension a ha).cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvStructure :
      (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntegralStructureAt v)
    (y : W.nonisotropicLastQuadraticShell a ha RationalFiniteAdele)
    (hyIntegral : ∀ i,
      finiteAdelicCliffordGeneralSpinHeightOneAlgHom v (y.1 i) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (haIntegral :
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 a ha)) ∈
        padicIntegralUnitsSubgroup
          (Rat.HeightOneSpectrum.primesEquiv v).1) :
    ∃ z : (W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v,
      (W.nonisotropicLastExtension a ha).PadicCliffordGeneralSpinIsIntegral
          (Rat.HeightOneSpectrum.primesEquiv v).1 z ∧
        CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z =
          W.nonisotropicLastQuadraticShellMap a ha
            (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y := by
  let V := W.nonisotropicLastExtension a ha
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let P := V.cliffordSpinCandidateIntegralSpinorRangeGoodPlace_of_not_mem_badPlaces
    (by omega : 2 ≤ n + 1) v hvOdd
  let yv := W.nonisotropicLastQuadraticShellMap a ha
    (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y
  let xInt : Fin (n + 1) → ℤ_[p] := lastCoordinateVector
  let yInt : Fin (n + 1) → ℤ_[p] := fun i =>
    ⟨yv.1 i, (PadicInt.mem_subring_iff p).mp (hyIntegral i)⟩
  have hxCast : (fun i => (xInt i : ℚ_[p])) =
      (lastCoordinateVector : Fin (n + 1) → ℚ_[p]) := by
    funext i
    cases i using Fin.lastCases <;> simp [xInt, lastCoordinateVector]
  have hyCast : (fun i => (yInt i : ℚ_[p])) = yv.1 := by
    rfl
  have hxy : P.unimodularForm.quadraticForm yInt =
      P.unimodularForm.quadraticForm xInt := by
    apply PadicInt.ext
    rw [P.coe_unimodularForm_quadraticForm,
      P.coe_unimodularForm_quadraticForm, hyCast, hxCast]
    exact yv.2.trans
      (W.lastCoordinateVector_mem_nonisotropicLastQuadraticShell a ha ℚ_[p]).symm
  let au : ℤ_[p]ˣ :=
    PositiveDefiniteIntegralLattice.padicIntUnitOfPadicIntegralUnit p
      (finiteAdelicUnitHeightOneComponentHom v
        (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
          (Units.mk0 a ha))) haIntegral
  have hxUnit : IsUnit (P.unimodularForm.quadraticForm xInt) := by
    have hxa : P.unimodularForm.quadraticForm xInt = (au : ℤ_[p]) := by
      apply PadicInt.ext
      rw [P.coe_unimodularForm_quadraticForm, hxCast]
      rw [show V.commutativeScalarExtensionQuadraticForm ℚ_[p]
          (lastCoordinateVector : Fin (n + 1) → ℚ_[p]) =
            algebraMap ℚ ℚ_[p] a from
        W.lastCoordinateVector_mem_nonisotropicLastQuadraticShell a ha ℚ_[p]]
      change algebraMap ℚ ℚ_[p] a = _
      rw [PositiveDefiniteIntegralLattice.coe_padicIntUnitOfPadicIntegralUnit]
      exact (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v).commutes a |>.symm
    rw [hxa]
    exact Units.isUnit au
  letI : NeZero (P.unimodularForm.orthogonalUnimodularForm xInt hxUnit).rank :=
    ⟨by
      have hr := P.unimodularForm.orthogonalUnimodularForm_rank_add_one
        xInt hxUnit
      change (P.unimodularForm.orthogonalUnimodularForm xInt hxUnit).rank + 1 =
        n + 1 at hr
      omega⟩
  obtain ⟨z, hzIntegral, hz⟩ :=
    P.exists_integral_padicCliffordGeneralSpin_mulVec_eq_of_unit_shell
      hvStructure xInt yInt hxy hxUnit
  refine ⟨z, hzIntegral, Subtype.ext ?_⟩
  dsimp only [CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap]
  simpa only [hxCast, hyCast] using hz

/-- The existing intrinsic finite-adelic GSpin group is transitive on the
nonisotropic block shell.  The lift is assembled from an actual cofinally
integral local family. -/
theorem CliffordGeneralSpinIntrinsicPoint.finiteAdelic_nonisotropicLastShellOrbitMap_surjective
    (W : RationalQuadraticSpaceMatrix n) [NeZero n]
    (a : ℚ) (ha : a ≠ 0) :
    Function.Surjective
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalFiniteAdele) := by
  classical
  let V := W.nonisotropicLastExtension a ha
  let aFinite : RationalFiniteAdeleˣ :=
    Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom (Units.mk0 a ha)
  intro y
  have hyIntegral : ∀ᶠ v in Filter.cofinite, ∀ i,
      finiteAdelicCliffordGeneralSpinHeightOneAlgHom v (y.1 i) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [(y.1 i).2] with v hv
    exact (mem_adicCompletionIntegers_iff_padic v _).1 hv
  have haIntegral : ∀ᶠ v in Filter.cofinite,
      finiteAdelicUnitHeightOneComponentHom v aFinite ∈
        padicIntegralUnitsSubgroup
          (Rat.HeightOneSpectrum.primesEquiv v).1 :=
    eventually_finiteAdelicUnitHeightOneComponent_mem_padicIntegralUnitsSubgroup
      aFinite
  have hlocal : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      ∃ z : V.HeightOnePadicCliffordGeneralSpinGroup v,
        CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z =
          W.nonisotropicLastQuadraticShellMap a ha
            (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y ∧
        (v ∉ V.cliffordSpinCandidateOddUnimodularBadPlaces →
          V.CliffordGeneralSpinIntegralStructureAt v →
          (∀ i, finiteAdelicCliffordGeneralSpinHeightOneAlgHom v (y.1 i) ∈
            PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) →
          finiteAdelicUnitHeightOneComponentHom v aFinite ∈
            padicIntegralUnitsSubgroup
              (Rat.HeightOneSpectrum.primesEquiv v).1 →
          V.PadicCliffordGeneralSpinIsIntegral
            (Rat.HeightOneSpectrum.primesEquiv v).1 z) := by
    intro v
    by_cases hgood :
        v ∉ V.cliffordSpinCandidateOddUnimodularBadPlaces ∧
          V.CliffordGeneralSpinIntegralStructureAt v ∧
          (∀ i, finiteAdelicCliffordGeneralSpinHeightOneAlgHom v (y.1 i) ∈
            PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
          finiteAdelicUnitHeightOneComponentHom v aFinite ∈
            padicIntegralUnitsSubgroup
              (Rat.HeightOneSpectrum.primesEquiv v).1
    · obtain ⟨z, hzIntegral, hz⟩ :=
        W.exists_integral_heightOne_nonisotropicLastShellOrbitMap_eq
          a ha v hgood.1 hgood.2.1 y hgood.2.2.1 hgood.2.2.2
      exact ⟨z, hz, fun _ _ _ _ => hzIntegral⟩
    · obtain ⟨z, hz⟩ :=
        CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_surjective
          W a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (W.nonisotropicLastQuadraticShellMap a ha
            (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y)
      exact ⟨z, hz, fun hOdd hStructure hy haInt =>
        False.elim (hgood ⟨hOdd, hStructure, hy, haInt⟩)⟩
  let localLift : V.HeightOnePadicCliffordGeneralSpinGroupProduct :=
    fun v => Classical.choose (hlocal v)
  have hlocalOrbit : ∀ v,
      CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] (localLift v) =
        W.nonisotropicLastQuadraticShellMap a ha
          (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v) y :=
    fun v => (Classical.choose_spec (hlocal v)).1
  have hrestricted : V.IsFiniteAdelicCliffordGeneralSpinRestrictedFamily
      localLift := by
    filter_upwards [
      V.cliffordSpinCandidateOddUnimodularBadPlaces.eventually_cofinite_notMem,
      V.eventually_cliffordGeneralSpinIntegralStructureAt,
      hyIntegral, haIntegral] with v hOdd hStructure hy haInt
    exact (Classical.choose_spec (hlocal v)).2 hOdd hStructure hy haInt
  let x : V.FiniteAdelicCliffordGeneralSpinRestrictedFamily :=
    ⟨localLift, hrestricted⟩
  let z := V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly x
  refine ⟨z, Subtype.ext ?_⟩
  funext i
  ext v
  apply (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
  let f := finiteAdelicCliffordGeneralSpinHeightOneAlgHom v
  have hzComponent := congrFun
    (V.finiteAdelicCliffordGeneralSpinHeightOneComponents_assembly x) v
  have hzLocal :
      V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v z =
        localLift v := by
    simpa only [z, x] using hzComponent
  have hnaturality := congrArg Subtype.val
    (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_naturality
      W a ha f z)
  have horbit := congrArg Subtype.val (hlocalOrbit v)
  change f
      ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalFiniteAdele z).1 i) = f (y.1 i)
  calc
    f ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha RationalFiniteAdele z).1 i) =
        (W.nonisotropicLastQuadraticShellMap a ha f
          (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha RationalFiniteAdele z)).1 i := rfl
    _ = (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v z)).1 i :=
      congrFun hnaturality i
    _ = (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          W a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          (localLift v)).1 i := by rw [hzLocal]
    _ = (W.nonisotropicLastQuadraticShellMap a ha f y).1 i :=
      congrFun horbit i
    _ = f (y.1 i) := rfl

end RationalQuadraticSpaceMatrix

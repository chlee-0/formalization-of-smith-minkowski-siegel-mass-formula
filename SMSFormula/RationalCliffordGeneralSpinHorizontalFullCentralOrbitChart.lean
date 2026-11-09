import SMSFormula.RationalCliffordGeneralSpinHorizontalFiniteCentralOrbitChart

/-!
# Full-adelic central-orbit intersection with the horizontal identity chart

The finite intrinsic carrier equality is adjoined to the real local equality
and transported through the exact multiplicative real--finite equivalences.
The resulting theorem is an equality on the actual full rational-idele and
intrinsic full-adelic `GSpin` carriers.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance horizontalFullCentralOrbitDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

/-- The full `GSpin` real--finite equivalence carries a central scalar to the
pair of the corresponding real and finite central scalars. -/
theorem fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_scalarGroupHom
    (a : RationalAdeleˣ) :
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
        (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a) =
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ
          (rationalAdeleUnitsRealFiniteContinuousEquiv a).1,
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalFiniteAdele
          (rationalAdeleUnitsRealFiniteContinuousEquiv a).2) := by
  apply Prod.ext <;>
    apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit <;>
    apply Units.ext <;>
    rfl

/-- Fixed full-adelic point obtained by adjoining a real Spin-chart point to
the already assembled finite identity-chart point. -/
def cliffordGeneralSpinHorizontalFullCentralOrbitOrigin
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (sReal : V.RealCliffordSpinCandidateGroup)
    (sFinite : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    V.FullAdelicCliffordGeneralSpinGroup :=
  V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
    (V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ sReal,
      V.cliffordGeneralSpinHorizontalFiniteCentralOrbitOrigin S sFinite g)

/-- Central translation through the fixed intrinsic full-adelic chart point. -/
def cliffordGeneralSpinHorizontalFullCentralOrbit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (sReal : V.RealCliffordSpinCandidateGroup)
    (sFinite : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    RationalAdeleˣ → V.FullAdelicCliffordGeneralSpinGroup :=
  fun a ↦
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele a *
      V.cliffordGeneralSpinHorizontalFullCentralOrbitOrigin
        S sReal sFinite g

/-- Splitting the full orbit recovers exactly the real orbit and the already
certified intrinsic finite orbit. -/
theorem fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_fullCentralOrbit
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (sReal : V.RealCliffordSpinCandidateGroup)
    (sFinite : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S)
    (a : RationalAdeleˣ) :
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
        (V.cliffordGeneralSpinHorizontalFullCentralOrbit
          S sReal sFinite g a) =
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ
          (rationalAdeleUnitsRealFiniteContinuousEquiv a).1 *
          V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ sReal,
        V.cliffordGeneralSpinHorizontalFiniteCentralOrbit S sFinite g
          (rationalAdeleUnitsRealFiniteContinuousEquiv a).2) := by
  unfold cliffordGeneralSpinHorizontalFullCentralOrbit
    cliffordGeneralSpinHorizontalFullCentralOrbitOrigin
  rw [map_mul,
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_scalarGroupHom,
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.apply_symm_apply]
  rfl

/-- Exact full-adelic orbit/chart intersection on the genuine rational-idele
and intrinsic `GSpin` carriers. -/
theorem preimage_cliffordGeneralSpinHorizontalFullCentralOrbit_identityChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (sReal : V.RealCliffordSpinCandidateGroup)
    (hsReal : sReal ∈ V.realCliffordSpinCandidateIdentityChart.source)
    (sFinite : V.CliffordGeneralSpinHorizontalExceptionalSOChartSource
      (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (g : V.CliffordGeneralSpinHorizontalIntegralTail S) :
    V.cliffordGeneralSpinHorizontalFullCentralOrbit S sReal sFinite g ⁻¹'
        V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier S =
      rationalIdeleDifferentialFullSquareChartCarrier
        (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) := by
  ext a
  let B := S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let ae := rationalAdeleUnitsRealFiniteContinuousEquiv
  let ge := V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
  constructor
  · rintro ⟨x, hx, hxa⟩
    have hsplit := congrArg ge hxa.symm
    rw [ge.apply_symm_apply] at hsplit
    rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_fullCentralOrbit]
      at hsplit
    have hrealOrbit :
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ (ae a).1 *
            V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ sReal ∈
          V.realCliffordGeneralSpinCentralFiberIdentityChart.source := by
      rw [show
          CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ (ae a).1 *
              V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ sReal = x.1 by
        simpa [ae, ge] using congrArg Prod.fst hsplit]
      exact hx.1
    have hreal : (ae a).1 ∈ (Rat.unitSquareIdentityChart ℝ).source :=
      (Set.ext_iff.mp
        (V.preimage_realCliffordGeneralSpinCentralOrbit_identityChart
          sReal hsReal) (ae a).1).mp hrealOrbit
    have hfiniteOrbit :
        V.cliffordGeneralSpinHorizontalFiniteCentralOrbit
            S sFinite g (ae a).2 ∈
          V.cliffordGeneralSpinHorizontalIdentityChartFiniteAdelicCarrier S := by
      rw [show
          V.cliffordGeneralSpinHorizontalFiniteCentralOrbit
              S sFinite g (ae a).2 = x.2 by
        simpa [ae, ge] using congrArg Prod.snd hsplit]
      exact hx.2
    have hfinite : (ae a).2 ∈
        rationalFiniteIdeleDifferentialSquareChartCarrier B :=
      V.finiteCentralOrbit_mem_squareChart_of_mem_identityChart
        S sFinite g (ae a).2 hfiniteOrbit
    rcases hfinite with ⟨q, hq⟩
    refine ⟨(⟨(ae a).1, hreal⟩, q), ?_⟩
    change ae.symm ((ae a).1,
      rationalFiniteIdeleDifferentialSquareChartToAmbient B q) = a
    rw [hq]
    exact ae.symm_apply_apply a
  · rintro ⟨q, hqa⟩
    have hasplit :
        ae a = ((q.1.1 : ℝˣ),
          rationalFiniteIdeleDifferentialSquareChartToAmbient B q.2) := by
      calc
        ae a = ae (rationalIdeleDifferentialFullSquareChartToAmbient B q) :=
          congrArg ae hqa.symm
        _ = ((q.1.1 : ℝˣ),
            rationalFiniteIdeleDifferentialSquareChartToAmbient B q.2) := by
          exact ae.apply_symm_apply _
    have hrealOrbit :
        CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ (ae a).1 *
            V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ sReal ∈
          V.realCliffordGeneralSpinCentralFiberIdentityChart.source := by
      have hreal : (ae a).1 ∈ (Rat.unitSquareIdentityChart ℝ).source := by
        rw [congrArg Prod.fst hasplit]
        exact q.1.2
      exact (Set.ext_iff.mp
        (V.preimage_realCliffordGeneralSpinCentralOrbit_identityChart
          sReal hsReal) (ae a).1).mpr hreal
    have hfinite : (ae a).2 ∈
        rationalFiniteIdeleDifferentialSquareChartCarrier B := by
      refine ⟨q.2, ?_⟩
      exact (congrArg Prod.snd hasplit).symm
    have hfiniteOrbit :=
      V.finiteCentralOrbit_mem_identityChart_of_mem_squareChart
        S sFinite g (ae a).2 hfinite
    let x := ge
      (V.cliffordGeneralSpinHorizontalFullCentralOrbit S sReal sFinite g a)
    refine ⟨x, ⟨?_, ?_⟩, ?_⟩
    · change
        (ge (V.cliffordGeneralSpinHorizontalFullCentralOrbit
          S sReal sFinite g a)).1 ∈ _
      rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_fullCentralOrbit]
      exact hrealOrbit
    · change
        (ge (V.cliffordGeneralSpinHorizontalFullCentralOrbit
          S sReal sFinite g a)).2 ∈ _
      rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_fullCentralOrbit]
      exact hfiniteOrbit
    · exact ge.symm_apply_apply _

end RationalQuadraticSpaceMatrix

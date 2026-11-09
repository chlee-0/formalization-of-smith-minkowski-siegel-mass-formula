import SMSFormula.RationalCliffordSpinCandidateGeneralSpinEmbedding
import SMSFormula.RationalCliffordGeneralSpinAdelicIdeleClassMap
import SMSFormula.RationalCliffordSpinCandidateAdelicLeftQuotientTopology

/-!
# Exactness of the Spin--general-Spin adelic quotient row

The represented intrinsic Spin inclusion descends to rational adelic left
quotients.  For the positive-definite lattice forms in rank at least three,
its image is exactly the neutral fiber of the general-Spin quotient map to
rational idele classes.  This is the vertical quotient exactness needed by
the crossed integral; no measure or Tamagawa assertion appears here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The represented Spin inclusion on full adelic points. -/
def fullAdelicCliffordSpinCandidateToGeneralSpinHom :
    V.FullAdelicCliffordSpinCandidateGroup →*
      V.FullAdelicCliffordGeneralSpinGroup :=
  V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele

/-- Rational diagonal scalar extension commutes with the represented Spin
inclusion into intrinsic general Spin. -/
theorem rational_fullAdelic_diagonal_candidateToGeneralSpin
    (x : V.RationalCliffordSpinCandidateGroup) :
    V.fullAdelicCliffordSpinCandidateToGeneralSpinHom
        (V.rationalCliffordSpinCandidateFullAdelicDiagonalHom x) =
      V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ x) := by
  exact (V.cliffordSpinCandidateToCliffordGeneralSpinHom_naturality ℚ
    (Algebra.ofId ℚ RationalAdele) x).symm

/-- The represented Spin map on rational full-adelic left quotients. -/
def fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin :
    V.FullAdelicCliffordSpinCandidateLeftQuotient →
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  Quot.lift
    (fun x => V.fullAdelicCliffordGeneralSpinLeftQuotientMap
      (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x)) (by
        intro x y hxy
        rcases hxy with ⟨gamma, rfl⟩
        rcases gamma.2 with ⟨q, hq⟩
        have hgamma :
            (gamma : V.FullAdelicCliffordSpinCandidateGroup) =
              V.rationalCliffordSpinCandidateFullAdelicDiagonalHom q :=
          hq.symm
        change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
            (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x) =
          V.fullAdelicCliffordGeneralSpinLeftQuotientMap
            (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom
              ((gamma : V.FullAdelicCliffordSpinCandidateGroup) * x))
        rw [map_mul, hgamma,
          V.rational_fullAdelic_diagonal_candidateToGeneralSpin]
        exact (leftCosetMap_gamma_mul
          V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
          ⟨V.rationalCliffordGeneralSpinFullAdelicDiagonalHom
              (V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ q),
            ⟨V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ q, rfl⟩⟩
          (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x)).symm)

@[simp]
theorem fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_mk
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
        (V.fullAdelicCliffordSpinCandidateLeftQuotientMap x) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap
        (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x) :=
  rfl

/-- The represented Spin quotient maps to the neutral rational idele class. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_neutral
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
        (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
          (V.fullAdelicCliffordSpinCandidateLeftQuotientMap x)) = 1 := by
  rw [V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_mk,
    V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_mk]
  change QuotientGroup.mk' rationalIdeleDiagonalSubgroup 1 = 1
  exact map_one _

/-- The represented Spin inclusion is continuous on the existing rational
adelic left quotients. -/
theorem continuous_fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin :
    Continuous V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin := by
  apply Continuous.quotient_lift
  exact V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap.continuous.comp
    (V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele)

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000

/-- For a positive-definite lattice form in rank at least three, the image
of the represented Spin quotient inside the intrinsic general-Spin quotient
is exactly the neutral idele-class fiber. -/
theorem mem_range_fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_iff
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (c : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient) :
    c ∈ Set.range
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin ↔
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass c = 1 := by
  let V := L.rationalQuadraticSpaceMatrix
  constructor
  · rintro ⟨z, rfl⟩
    induction z using Quot.inductionOn with
    | _ x => exact V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_neutral x
  · intro hc
    let x : V.FullAdelicCliffordGeneralSpinGroup := Quot.out c
    have hxout : V.fullAdelicCliffordGeneralSpinLeftQuotientMap x = c :=
      Quot.out_eq c
    have hclass := hc
    rw [← hxout,
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_mk] at hclass
    have hnu_mem : V.fullAdelicCliffordGeneralSpinSimilitudeHom x ∈
        RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup :=
      (QuotientGroup.eq_one_iff _).mp hclass
    rcases hnu_mem with ⟨q, hq⟩
    have hdiag_range :
        RationalQuadraticSpaceMatrix.rationalUnitFullAdelicDiagonalHom q ∈
          V.fullAdelicCliffordGeneralSpinSimilitudeHom.range := by
      exact ⟨x, hq.symm⟩
    have hq_range :=
      (L.rationalUnitDiagonal_mem_fullAdelicGeneralSpinSimilitudeRange_iff
        hr q).mp hdiag_range
    rcases hq_range with ⟨gamma, hgamma⟩
    let y : V.FullAdelicCliffordGeneralSpinGroup :=
      (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)⁻¹ * x
    have hyker : y ∈
        (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
          V RationalAdele).ker := by
      change V.fullAdelicCliffordGeneralSpinSimilitudeHom y = 1
      dsimp [y]
      rw [map_mul, map_inv,
        V.rational_fullAdelic_diagonal_generalSpin_similitude]
      change gamma.similitude = q at hgamma
      rw [hgamma, hq]
      simp
    rw [← V.range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker
      RationalAdele] at hyker
    rcases hyker with ⟨s, hs⟩
    refine ⟨V.fullAdelicCliffordSpinCandidateLeftQuotientMap s, ?_⟩
    rw [V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_mk]
    change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
      (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele s) = c
    rw [hs, ← hxout]
    exact leftCosetMap_gamma_mul
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
      ⟨(V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma)⁻¹,
        ⟨gamma⁻¹, by simp⟩⟩ x

end PositiveDefiniteIntegralLattice

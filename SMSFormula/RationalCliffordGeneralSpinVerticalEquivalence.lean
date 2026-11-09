import SMSFormula.RationalCliffordGeneralSpinVerticalParametrization
import SMSFormula.RationalCliffordGeneralSpinAdelicHorizontalTorsor

/-!
# Bijectivity of the vertical general-Spin parametrization

The represented Spin inclusion is faithful before and after passage to the
rational adelic left quotients.  Consequently the
idele-class/Spin parametrization of the general-Spin quotient is bijective.
This gives the exact carrier multiplicity needed for the
finite-cutoff measured map; no measure comparison is asserted.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

/-- The represented intrinsic Spin inclusion into intrinsic general Spin is
faithful over every commutative rational algebra. -/
theorem cliffordSpinCandidateToCliffordGeneralSpinHom_injective
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Function.Injective (V.cliffordSpinCandidateToCliffordGeneralSpinHom A) := by
  intro x y hxy
  apply (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A).injective
  apply CliffordSpinCandidatePointData.ext_clifford V A
  exact congrArg
    (fun z : V.CliffordGeneralSpinIntrinsicPoint A =>
      (z.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A)) hxy

/-- Right translation on the rational adelic general-Spin quotient is
injective. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientRightMul_injective
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    Function.Injective
      (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x) := by
  intro z w hzw
  have h := congrArg
    (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x⁻¹) hzw
  simpa [V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul_rightMul] using h

/-- The represented Spin map remains injective after quotienting both sides
by their rational diagonal subgroups. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_injective :
    Function.Injective
      V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin := by
  intro z w hzw
  induction z using Quot.inductionOn with
  | _ x =>
    induction w using Quot.inductionOn with
    | _ y =>
      change V.fullAdelicCliffordGeneralSpinLeftQuotientMap
          (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x) =
        V.fullAdelicCliffordGeneralSpinLeftQuotientMap
          (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y) at hzw
      have hdiag :=
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap_eq_iff
          (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x)
          (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y)).mp hzw
      rcases hdiag with ⟨q, hq⟩
      have hqker : q ∈
          (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V ℚ).ker := by
        change q.similitude = 1
        have hsim := congrArg
          (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V RationalAdele)
          hq
        change V.fullAdelicCliffordGeneralSpinSimilitudeHom
            (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom q) =
          V.fullAdelicCliffordGeneralSpinSimilitudeHom
              (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y) *
            (V.fullAdelicCliffordGeneralSpinSimilitudeHom
              (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x))⁻¹ at hsim
        rw [V.rational_fullAdelic_diagonal_generalSpin_similitude] at hsim
        have hsim' : rationalUnitFullAdelicDiagonalHom q.similitude = 1 := by
          change rationalUnitFullAdelicDiagonalHom q.similitude =
            (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele y).similitude *
              (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele x).similitude⁻¹
            at hsim
          simpa using hsim
        have hreal := congrArg
          (fun a : RationalAdeleˣ =>
            ((rationalAdeleUnitsRealFiniteContinuousEquiv a).1 : ℝ)) hsim'
        change
          ((rationalAdeleUnitsRealFiniteContinuousEquiv
            (rationalUnitFullAdelicDiagonalHom q.similitude)).1 : ℝ) =
          ((rationalAdeleUnitsRealFiniteContinuousEquiv (1 : RationalAdeleˣ)).1 : ℝ)
          at hreal
        rw [rationalAdeleUnitsRealFiniteContinuousEquiv_rationalUnitDiagonal,
          map_one] at hreal
        change ((q.similitude : ℚ) : ℝ) = 1 at hreal
        have hrat : (q.similitude : ℚ) = 1 := by
          exact_mod_cast hreal
        exact Units.ext hrat
      rw [← V.range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker ℚ] at hqker
      rcases hqker with ⟨s, hs⟩
      apply (V.fullAdelicCliffordSpinCandidateLeftQuotientMap_eq_iff x y).2
      refine ⟨s, ?_⟩
      apply V.cliffordSpinCandidateToCliffordGeneralSpinHom_injective RationalAdele
      rw [map_mul, map_inv]
      change V.fullAdelicCliffordSpinCandidateToGeneralSpinHom
          (V.rationalCliffordSpinCandidateFullAdelicDiagonalHom s) =
        V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y *
          (V.fullAdelicCliffordSpinCandidateToGeneralSpinHom x)⁻¹
      rw [V.rational_fullAdelic_diagonal_candidateToGeneralSpin, hs]
      exact hq

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- In lattice rank at least three the carrier parametrization by an idele
class and a Spin quotient point is bijective. -/
theorem fullAdelicCliffordGeneralSpinVerticalParametrization_bijective
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    Function.Bijective
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinVerticalParametrization
        hsurj) := by
  let V := L.rationalQuadraticSpaceMatrix
  refine ⟨?_, L.fullAdelicCliffordGeneralSpinVerticalParametrization_surjective
    hn hsurj⟩
  intro z w hzw
  have hc : z.1 = w.1 := by
    have h := congrArg
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass hzw
    rw [V.fullAdelicCliffordGeneralSpinVerticalParametrization_ideleClass,
      V.fullAdelicCliffordGeneralSpinVerticalParametrization_ideleClass] at h
    exact h
  rcases z with ⟨c, z⟩
  rcases w with ⟨d, w⟩
  dsimp only at hc
  subst d
  apply Prod.ext
  · rfl
  · apply V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_injective
    apply V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul_injective
      (V.verticalGeneralSpinRepresentative hsurj c)
    exact hzw

end PositiveDefiniteIntegralLattice

import SMSFormula.RationalCliffordGeneralSpinLatticeRationalSimilitude
import SMSFormula.RationalSquareClassFiniteLocalizationSurjectivity

/-!
# P-adic similitudes of the lattice intrinsic general-Spin group

Every p-adic square class has a positive rational representative by finite
weak approximation.  The completed rational positive-similitude theorem
realizes that representative in intrinsic `GSpin(ℚ)`.  Scalar extension and
the crossed spinor-norm square then put the original p-adic square class in
the local spinor-norm image, and fieldwise exactness adjusts within the square
class to the prescribed literal p-adic similitude.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace Rat

/-- Every p-adic square class has a positive rational-unit representative. -/
theorem exists_positive_rationalUnit_same_padicSquareClass
    (p : ℕ) [Fact p.Prime] (a : ℚ_[p]ˣ) :
    ∃ q : ℚˣ, 0 < (q : ℚ) ∧
      rationalSquareClassToPadic p (q : RationalSquareClass) =
        (a : SquareClass ℚ_[p]) := by
  classical
  letI primeFact (r : {r : ℕ // r.Prime}) : Fact r.1.Prime := ⟨r.2⟩
  let P : {r : ℕ // r.Prime} := ⟨p, Fact.out⟩
  let S : Finset {r : ℕ // r.Prime} := {P}
  let y : (r : ↥S) → SquareClass ℚ_[r.1.1] := fun r ↦ by
    have hr : r.1 = P := Finset.mem_singleton.mp r.2
    rw [hr]
    exact (a : SquareClass ℚ_[p])
  obtain ⟨q, hq, hlocal⟩ :=
    exists_positive_rat_realizing_finite_padic_squareClasses S y
  refine ⟨q, hq, ?_⟩
  let r : ↥S := ⟨P, Finset.mem_singleton_self P⟩
  have h := hlocal r
  simpa [r, P, S, y] using h

end Rat

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

namespace CliffordGeneralSpinIntrinsicPoint

/-- At every finite place, the intrinsic general-Spin similitude is
surjective for the positive-definite rational lattice form in rank at least
three.  The proof uses only the already proved rational positive image and
one-place square-class approximation. -/
theorem padicCliffordGeneralSpinSimilitudeHom_surjective
    (hn : 3 ≤ n) (p : ℕ) [Fact p.Prime] :
    Function.Surjective
      (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinSimilitudeHom p) := by
  intro a
  obtain ⟨q, hq, hclass⟩ :=
    Rat.exists_positive_rationalUnit_same_padicSquareClass p a
  obtain ⟨x, hx⟩ :=
    exists_rationalCliffordGeneralSpin_similitude_eq_of_pos L hn q hq
  let xp : L.rationalQuadraticSpaceMatrix.PadicCliffordGeneralSpinGroup p :=
    mapGroupHom L.rationalQuadraticSpaceMatrix (Algebra.ofId ℚ ℚ_[p]) x
  change a ∈ (similitudeGroupHom L.rationalQuadraticSpaceMatrix ℚ_[p]).range
  rw [range_similitudeGroupHom_eq_squareClass_comap_spinorNorm_range]
  change (a : Rat.SquareClass ℚ_[p]) ∈
    (L.rationalQuadraticSpaceMatrix.specialOrthogonalSpinorNormHom ℚ_[p]).range
  refine ⟨toSpecialOrthogonalGroupHom
    L.rationalQuadraticSpaceMatrix ℚ_[p] xp, ?_⟩
  change L.rationalQuadraticSpaceMatrix.specialOrthogonalSpinorNormHom ℚ_[p]
      xp.matrixGroup = (a : Rat.SquareClass ℚ_[p])
  rw [specialOrthogonalSpinorNorm_matrixGroup_eq_similitudeSquareClass]
  have hnu : similitudeGroupHom L.rationalQuadraticSpaceMatrix ℚ_[p] xp =
      Units.map (algebraMap ℚ ℚ_[p]) q := by
    change (mapGroupHom L.rationalQuadraticSpaceMatrix
      (Algebra.ofId ℚ ℚ_[p]) x).similitude =
        Units.map (algebraMap ℚ ℚ_[p]) q
    have hx' : x.similitude = q := hx
    rw [mapGroupHom_apply, map_similitude, hx']
    rfl
  have hnuClass := congrArg
    (fun u : ℚ_[p]ˣ ↦ (u : Rat.SquareClass ℚ_[p])) hnu
  change (xp.similitude : Rat.SquareClass ℚ_[p]) =
    ((Units.map (algebraMap ℚ ℚ_[p]) q : ℚ_[p]ˣ) :
      Rat.SquareClass ℚ_[p]) at hnuClass
  exact hnuClass.trans hclass

/-- The p-adic similitude image is the whole local unit group. -/
theorem range_padicCliffordGeneralSpinSimilitudeHom_eq_top
    (hn : 3 ≤ n) (p : ℕ) [Fact p.Prime] :
    (L.rationalQuadraticSpaceMatrix.padicCliffordGeneralSpinSimilitudeHom p).range =
      ⊤ := by
  exact MonoidHom.range_eq_top.mpr
    (padicCliffordGeneralSpinSimilitudeHom_surjective L hn p)

end CliffordGeneralSpinIntrinsicPoint

end RationalQuadraticSpaceMatrix

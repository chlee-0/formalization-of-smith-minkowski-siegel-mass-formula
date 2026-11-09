import SMSFormula.RationalIdeleClassLogSection
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import SMSFormula.RationalCliffordGeneralSpinLatticeAdelicSimilitudeExactness
import SMSFormula.RationalCliffordGeneralSpinAdelicDiagonalTopology

/-!
# The adelic general-Spin quotient map to idele classes

The similitude character descends from the rational left quotient of
intrinsic `GSpin` to rational idele classes.  For the positive-definite
lattice forms in rank at least three, the completed adelic similitude
exactness proves that this descended map is onto.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

theorem rational_fullAdelic_diagonal_generalSpin_similitude
    (x : V.RationalCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinSimilitudeHom
        (V.rationalCliffordGeneralSpinFullAdelicDiagonalHom x) =
      rationalUnitFullAdelicDiagonalHom x.similitude := by
  rfl

/-- The similitude character on the rational `GSpin` left quotient, valued
in rational idele classes. -/
def fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass :
    V.FullAdelicCliffordGeneralSpinLeftQuotient →
      RationalIdeleClassGroup :=
  Quot.lift
    (fun x => QuotientGroup.mk' rationalIdeleDiagonalSubgroup
      (V.fullAdelicCliffordGeneralSpinSimilitudeHom x)) (by
        intro x y hxy
        rcases hxy with ⟨gamma, rfl⟩
        rcases gamma.2 with ⟨q, hq⟩
        have hgamma :
            (gamma : V.FullAdelicCliffordGeneralSpinGroup) =
              V.rationalCliffordGeneralSpinFullAdelicDiagonalHom q :=
          hq.symm
        symm
        change QuotientGroup.mk' rationalIdeleDiagonalSubgroup
            (V.fullAdelicCliffordGeneralSpinSimilitudeHom
              ((gamma : V.FullAdelicCliffordGeneralSpinGroup) * x)) =
          QuotientGroup.mk' rationalIdeleDiagonalSubgroup
            (V.fullAdelicCliffordGeneralSpinSimilitudeHom x)
        rw [map_mul, hgamma,
          V.rational_fullAdelic_diagonal_generalSpin_similitude]
        change QuotientGroup.mk' rationalIdeleDiagonalSubgroup
            (rationalUnitFullAdelicDiagonalHom q.similitude) *
              QuotientGroup.mk' rationalIdeleDiagonalSubgroup
                (V.fullAdelicCliffordGeneralSpinSimilitudeHom x) =
          QuotientGroup.mk' rationalIdeleDiagonalSubgroup
            (V.fullAdelicCliffordGeneralSpinSimilitudeHom x)
        rw [show QuotientGroup.mk' rationalIdeleDiagonalSubgroup
            (rationalUnitFullAdelicDiagonalHom q.similitude) = 1 by
          exact (QuotientGroup.eq_one_iff _).mpr
            ⟨q.similitude, rfl⟩]
        change (1 : RationalIdeleClassGroup) *
            QuotientGroup.mk' rationalIdeleDiagonalSubgroup
              (V.fullAdelicCliffordGeneralSpinSimilitudeHom x) = _
        exact @one_mul RationalIdeleClassGroup _
          (QuotientGroup.mk' rationalIdeleDiagonalSubgroup
            (V.fullAdelicCliffordGeneralSpinSimilitudeHom x)))

@[simp]
theorem fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_mk
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x) =
      QuotientGroup.mk' rationalIdeleDiagonalSubgroup
        (V.fullAdelicCliffordGeneralSpinSimilitudeHom x) :=
  rfl

/-- The standard quotient topology on the existing intrinsic `GSpin`
left-coset carrier. -/
instance fullAdelicCliffordGeneralSpinLeftQuotientTopologicalSpace :
    TopologicalSpace V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  TopologicalSpace.coinduced
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap inferInstance

theorem fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap :
    Topology.IsQuotientMap
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap := by
  exact
    { isCoinducing := ⟨rfl⟩
      surjective := Quot.mk_surjective }

theorem continuous_fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass :
    Continuous V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass := by
  apply Continuous.quotient_lift
  · exact continuous_quot_mk.comp
      V.continuous_fullAdelicCliffordGeneralSpinSimilitudeHom

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

/-- For every positive-definite lattice form of rank at least three, the
descended adelic `GSpin` similitude fills all rational idele classes. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_surjective
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r) :
    Function.Surjective
      (RationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
          L.rationalQuadraticSpaceMatrix) := by
  intro c
  let a : RationalAdeleˣ := Quotient.out c
  have ha : QuotientGroup.mk'
      RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup a = c :=
    Quotient.out_eq c
  obtain ⟨q, x, hx⟩ :=
    L.exists_rationalUnit_mul_fullAdelicGeneralSpinSimilitude hr a
  refine ⟨L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientMap x, ?_⟩
  rw [L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_mk]
  rw [← ha, hx, map_mul]
  change _ = QuotientGroup.mk'
    RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
      (RationalQuadraticSpaceMatrix.rationalUnitFullAdelicDiagonalHom q) * _
  rw [show QuotientGroup.mk'
      RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
        (RationalQuadraticSpaceMatrix.rationalUnitFullAdelicDiagonalHom q) = 1 by
    exact (QuotientGroup.eq_one_iff _).mpr ⟨q, rfl⟩]
  change _ = (1 : RationalQuadraticSpaceMatrix.RationalIdeleClassGroup) * _
  exact (@one_mul RationalQuadraticSpaceMatrix.RationalIdeleClassGroup _
    (QuotientGroup.mk'
      RationalQuadraticSpaceMatrix.rationalIdeleDiagonalSubgroup
        (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom x))).symm

end PositiveDefiniteIntegralLattice

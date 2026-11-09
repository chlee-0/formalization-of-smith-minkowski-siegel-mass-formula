import SMSFormula.RationalCliffordGeneralSpinLatticeFullAdelicSimilitude
import SMSFormula.RationalCliffordGeneralSpinLatticeRationalSimilitude

/-!
# Rational exactness for lattice general-Spin adelic similitudes

Every rational idele class has a representative positive at the real place,
obtained by multiplying by `1` or `-1`.  Moreover a rational diagonal idele
is positive precisely when the rational unit is positive.  Combined with the
completed rational and full-adelic similitude image theorems, these are the
two concrete quotient-exactness equations used by the crossed `GSpin`
integral.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

/-- The diagonal embedding of rational units into rational ideles. -/
def rationalUnitFullAdelicDiagonalHom : ℚˣ →* RationalAdeleˣ :=
  Units.map (Algebra.ofId ℚ RationalAdele).toMonoidHom

theorem rationalAdele_algebraMap_snd_generalSpin (q : ℚ) :
    (algebraMap ℚ RationalAdele q).2 =
      algebraMap ℚ RationalFiniteAdele q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.snd RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalFiniteAdele)) q

theorem rationalInfiniteAdele_algebraMap_equivReal_generalSpin (q : ℚ) :
    rationalInfiniteAdeleHomeomorphReal
        (algebraMap ℚ RationalInfiniteAdele q) =
      algebraMap ℚ ℝ q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      (rationalInfiniteAdeleRingEquivReal.toRingHom.comp
        (algebraMap ℚ RationalInfiniteAdele))
      (algebraMap ℚ ℝ)) q

@[simp]
theorem rationalAdeleUnitsRealFiniteContinuousEquiv_rationalUnitDiagonal
    (q : ℚˣ) :
    rationalAdeleUnitsRealFiniteContinuousEquiv
        (rationalUnitFullAdelicDiagonalHom q) =
      (Units.map (algebraMap ℚ ℝ).toMonoidHom q,
        Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom q) := by
  apply Prod.ext <;> apply Units.ext
  · exact rationalInfiniteAdele_algebraMap_equivReal_generalSpin q
  · exact rationalAdele_algebraMap_snd_generalSpin q

/-- A rational diagonal idele is positive at infinity exactly when its
rational source unit is positive. -/
theorem rationalUnitFullAdelicDiagonal_mem_positive_iff
    (q : ℚˣ) :
    rationalUnitFullAdelicDiagonalHom q ∈ positiveRationalAdeleUnitsSubgroup ↔
      q ∈ positiveRationalUnitsSubgroup := by
  rw [mem_positiveRationalAdeleUnitsSubgroup_iff,
    rationalAdeleUnitsRealFiniteContinuousEquiv_rationalUnitDiagonal]
  change 0 < ((q : ℚ) : ℝ) ↔ 0 < (q : ℚ)
  exact_mod_cast Iff.rfl

/-- Every idele is a rational unit times an idele positive at infinity. -/
theorem exists_rationalUnit_mul_positiveRationalAdeleUnit
    (a : RationalAdeleˣ) :
    ∃ q : ℚˣ, ∃ b : RationalAdeleˣ,
      b ∈ positiveRationalAdeleUnitsSubgroup ∧
        a = rationalUnitFullAdelicDiagonalHom q * b := by
  let ar : ℝˣ := (rationalAdeleUnitsRealFiniteContinuousEquiv a).1
  by_cases ha : 0 < (ar : ℝ)
  · refine ⟨1, a, ?_, by simp⟩
    rw [mem_positiveRationalAdeleUnitsSubgroup_iff]
    exact ha
  · let q : ℚˣ := -1
    let d : RationalAdeleˣ := rationalUnitFullAdelicDiagonalHom q
    let b : RationalAdeleˣ := d⁻¹ * a
    refine ⟨q, b, ?_, ?_⟩
    · rw [mem_positiveRationalAdeleUnitsSubgroup_iff]
      change 0 <
        ((rationalAdeleUnitsRealFiniteContinuousEquiv (d⁻¹ * a)).1 : ℝ)
      rw [map_mul, map_inv]
      simp only [Prod.fst_mul, Prod.fst_inv, Units.val_mul,
        Units.val_inv_eq_inv_val]
      change 0 < (((rationalAdeleUnitsRealFiniteContinuousEquiv d).1)⁻¹ : ℝ) *
        (ar : ℝ)
      rw [show rationalAdeleUnitsRealFiniteContinuousEquiv d =
          (Units.map (algebraMap ℚ ℝ).toMonoidHom q,
            Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom q) by
        exact rationalAdeleUnitsRealFiniteContinuousEquiv_rationalUnitDiagonal q]
      simpa [q] using
        (neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt ha) ar.ne_zero))
    · change a = d * (d⁻¹ * a)
      simp

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

/-- Concrete adelic quotient surjectivity: rational units times the
full-adelic intrinsic general-Spin similitude image fill all ideles. -/
theorem exists_rationalUnit_mul_fullAdelicGeneralSpinSimilitude
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r)
    (a : RationalAdeleˣ) :
    ∃ q : ℚˣ,
      ∃ x : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinGroup,
        a = RationalQuadraticSpaceMatrix.rationalUnitFullAdelicDiagonalHom q *
          L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom x := by
  obtain ⟨q, b, hb, hab⟩ :=
    RationalQuadraticSpaceMatrix.exists_rationalUnit_mul_positiveRationalAdeleUnit a
  have hRange :=
    range_fullAdelicCliffordGeneralSpinSimilitudeHom_eq_positive L hr
  rw [← hRange] at hb
  obtain ⟨x, rfl⟩ := hb
  exact ⟨q, x, hab⟩

/-- Concrete rational intersection exactness: a rational diagonal idele lies
in the full-adelic similitude image exactly when its rational source lies in
the rational intrinsic general-Spin similitude image. -/
theorem rationalUnitDiagonal_mem_fullAdelicGeneralSpinSimilitudeRange_iff
    (L : PositiveDefiniteIntegralLattice (r + 2)) (hr : 1 ≤ r) (q : ℚˣ) :
    RationalQuadraticSpaceMatrix.rationalUnitFullAdelicDiagonalHom q ∈
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinSimilitudeHom.range ↔
      q ∈
        (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
          L.rationalQuadraticSpaceMatrix ℚ).range := by
  rw [range_fullAdelicCliffordGeneralSpinSimilitudeHom_eq_positive L hr,
    RationalQuadraticSpaceMatrix.rationalUnitFullAdelicDiagonal_mem_positive_iff,
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.range_rationalCliffordGeneralSpinSimilitudeHom_eq_positive
      L (by omega)]

end PositiveDefiniteIntegralLattice

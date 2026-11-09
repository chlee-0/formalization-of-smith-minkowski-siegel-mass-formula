import SMSFormula.RationalFiniteAdeleIntegralLatticeDilation
import SMSFormula.RationalIdeleModule
import SMSFormula.RationalAdeleCoordinateElementaryFourier
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
# Rational dilation of the normalized additive adelic Haar

This file proves on the literal rational-adelic carrier that multiplication
by a nonzero rational diagonal preserves the fixed additive Haar.  The proof
first keeps the two factors visible for a positive integer `m`: the real
interval acquires mass `m`, while the finite integral lattice acquires mass
`m⁻¹`.  Their product is one.  Multiplicativity then extends the result to
every rational unit.

No Fourier covariance, Weil-representation relation, or new Haar
normalization is asserted here.
-/

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Pointwise
open RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

/-- A nonzero natural number as a rational unit. -/
private def rationalNatUnit (m : ℕ) (hm : m ≠ 0) : ℚˣ :=
  Units.mk0 (m : ℚ) (by exact_mod_cast hm)

private theorem rationalAdele_algebraMap_fst_dilationHaar (q : ℚ) :
    (algebraMap ℚ RationalAdele q).1 =
      algebraMap ℚ RationalInfiniteAdele q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalInfiniteAdele)) q

private theorem rationalUnitFullAdelicDiagonalHom_smul_fst
    (q : ℚˣ) (x : RationalAdele) :
    (rationalUnitFullAdelicDiagonalHom q • x).1 =
      Units.map (algebraMap ℚ RationalInfiniteAdele).toMonoidHom q • x.1 := by
  change ((algebraMap ℚ RationalAdele (q : ℚ)) * x).1 =
    (algebraMap ℚ RationalInfiniteAdele (q : ℚ)) * x.1
  change (algebraMap ℚ RationalAdele (q : ℚ)).1 * x.1 = _
  rw [rationalAdele_algebraMap_fst_dilationHaar]

private theorem rationalUnitFullAdelicDiagonalHom_smul_snd
    (q : ℚˣ) (x : RationalAdele) :
    (rationalUnitFullAdelicDiagonalHom q • x).2 =
      Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom q • x.2 := by
  change ((algebraMap ℚ RationalAdele (q : ℚ)) * x).2 =
    (algebraMap ℚ RationalFiniteAdele (q : ℚ)) * x.2
  change (algebraMap ℚ RationalAdele (q : ℚ)).2 * x.2 = _
  rw [rationalAdele_algebraMap_snd_generalSpin]

/-- The image of the real adelic unit interval under multiplication by `m`. -/
def rationalInfiniteAdeleNatDilationSet (m : ℕ) (hm : m ≠ 0) :
    Set RationalInfiniteAdele :=
  (Units.map (algebraMap ℚ RationalInfiniteAdele).toMonoidHom
      (rationalNatUnit m hm)) • rationalInfiniteAdeleUnitInterval

theorem rationalInfiniteAdeleNatDilationSet_eq (m : ℕ) (hm : m ≠ 0) :
    rationalInfiniteAdeleNatDilationSet m hm =
      rationalInfiniteAdeleContinuousAddEquivReal ⁻¹' Icc (0 : ℝ) m := by
  ext x
  rw [Set.mem_preimage, rationalInfiniteAdeleNatDilationSet,
    Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : rationalInfiniteAdeleContinuousAddEquivReal y ∈
        Icc (0 : ℝ) 1 := hy
    change rationalInfiniteAdeleContinuousAddEquivReal
        ((Units.map (algebraMap ℚ RationalInfiniteAdele).toMonoidHom
          (rationalNatUnit m hm)) • y) ∈ Icc (0 : ℝ) m
    rw [show rationalInfiniteAdeleContinuousAddEquivReal
          ((Units.map (algebraMap ℚ RationalInfiniteAdele).toMonoidHom
            (rationalNatUnit m hm)) • y) =
        (m : ℝ) * rationalInfiniteAdeleContinuousAddEquivReal y by
      simp [rationalNatUnit, Units.smul_def]]
    exact ⟨mul_nonneg (Nat.cast_nonneg m) hy'.1,
      (mul_le_mul_of_nonneg_left hy'.2 (Nat.cast_nonneg m)).trans_eq
        (mul_one (m : ℝ))⟩
  · intro hx
    let y : RationalInfiniteAdele :=
      rationalInfiniteAdeleContinuousAddEquivReal.symm
        ((rationalInfiniteAdeleContinuousAddEquivReal x) / m)
    have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hy : y ∈ rationalInfiniteAdeleUnitInterval := by
      simpa [rationalInfiniteAdeleUnitInterval, y] using
        (show (rationalInfiniteAdeleContinuousAddEquivReal x) / m ∈
          Icc (0 : ℝ) 1 from
            ⟨div_nonneg hx.1 hmR.le, (div_le_one hmR).2 hx.2⟩)
    refine ⟨y, hy, ?_⟩
    apply rationalInfiniteAdeleContinuousAddEquivReal.injective
    rw [show rationalInfiniteAdeleContinuousAddEquivReal
          ((Units.map (algebraMap ℚ RationalInfiniteAdele).toMonoidHom
            (rationalNatUnit m hm)) • y) =
        (m : ℝ) * rationalInfiniteAdeleContinuousAddEquivReal y by
      simp [rationalNatUnit, Units.smul_def]]
    simp [y]
    field_simp

theorem rationalInfiniteAdeleAddHaarMeasure_natDilationSet
    (m : ℕ) (hm : m ≠ 0) :
    rationalInfiniteAdeleAddHaarMeasure
        (rationalInfiniteAdeleNatDilationSet m hm) = m := by
  rw [rationalInfiniteAdeleNatDilationSet_eq m hm,
    rationalInfiniteAdeleAddHaarMeasure]
  have hpre : rationalInfiniteAdeleContinuousAddEquivReal.symm ⁻¹'
      (rationalInfiniteAdeleContinuousAddEquivReal ⁻¹'
        Icc (0 : ℝ) m) = Icc (0 : ℝ) m := by
    ext x
    simp
  calc
    (Measure.map rationalInfiniteAdeleContinuousAddEquivReal.symm volume)
        (rationalInfiniteAdeleContinuousAddEquivReal ⁻¹'
          Icc (0 : ℝ) m) =
        volume (rationalInfiniteAdeleContinuousAddEquivReal.symm ⁻¹'
          (rationalInfiniteAdeleContinuousAddEquivReal ⁻¹'
            Icc (0 : ℝ) m)) :=
      Measure.map_apply_of_aemeasurable
        rationalInfiniteAdeleContinuousAddEquivReal.symm.measurable.aemeasurable
        (measurableSet_Icc.preimage
          rationalInfiniteAdeleContinuousAddEquivReal.measurable)
    _ = m := by rw [hpre, Real.volume_Icc]; simp

/-- The finite component of the rational unit action sends the integral
finite adeles to the literal dilation set already measured earlier. -/
theorem rationalFiniteAdeleNatUnit_smul_integral
    (m : ℕ) (hm : m ≠ 0) :
    (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
        (rationalNatUnit m hm)) •
        (integralFiniteAdeleSubring : Set RationalFiniteAdele) =
      integralFiniteAdeleNatDilationSet m := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    simp [rationalNatUnit, Units.smul_def, nsmul_eq_mul]
  · rintro ⟨y, rfl⟩
    refine ⟨(y : RationalFiniteAdele), y.property, ?_⟩
    simp [rationalNatUnit, Units.smul_def, nsmul_eq_mul]

/-- The image of the normalized full adelic block under multiplication by
the rational diagonal `m`. -/
def rationalAdeleNatDilationSet (m : ℕ) (hm : m ≠ 0) : Set RationalAdele :=
  (rationalUnitFullAdelicDiagonalHom (rationalNatUnit m hm)) •
    rationalAdeleStandardBlock

theorem rationalAdeleNatDilationSet_eq (m : ℕ) (hm : m ≠ 0) :
    rationalAdeleNatDilationSet m hm =
      rationalInfiniteAdeleNatDilationSet m hm ×ˢ
        integralFiniteAdeleNatDilationSet m := by
  rw [rationalAdeleNatDilationSet, rationalAdeleStandardBlock_eq]
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, ⟨hyReal, hyf⟩, rfl⟩
    constructor
    · rw [rationalInfiniteAdeleNatDilationSet, Set.mem_smul_set]
      refine ⟨y.1, hyReal, ?_⟩
      exact (rationalUnitFullAdelicDiagonalHom_smul_fst
        (rationalNatUnit m hm) y).symm
    · rw [← rationalFiniteAdeleNatUnit_smul_integral m hm,
        Set.mem_smul_set]
      refine ⟨y.2, hyf, ?_⟩
      exact (rationalUnitFullAdelicDiagonalHom_smul_snd
        (rationalNatUnit m hm) y).symm
  · rintro ⟨hxReal, hxf⟩
    rw [rationalInfiniteAdeleNatDilationSet, Set.mem_smul_set] at hxReal
    rw [← rationalFiniteAdeleNatUnit_smul_integral m hm,
      Set.mem_smul_set] at hxf
    obtain ⟨yReal, hyReal, hxyReal⟩ := hxReal
    obtain ⟨yf, hyf, hxyf⟩ := hxf
    let y : RationalAdele := (yReal, yf)
    refine ⟨y, ⟨hyReal, hyf⟩, ?_⟩
    apply Prod.ext
    · rw [rationalUnitFullAdelicDiagonalHom_smul_fst]
      exact hxyReal
    · rw [rationalUnitFullAdelicDiagonalHom_smul_snd]
      exact hxyf

theorem rationalAdeleAddHaarMeasure_natDilationSet
    (m : ℕ) (hm : m ≠ 0) :
    rationalAdeleAddHaarMeasure (rationalAdeleNatDilationSet m hm) = 1 := by
  rw [rationalAdeleAddHaarMeasure_eq_prod,
    rationalAdeleNatDilationSet_eq m hm]
  calc
    (rationalInfiniteAdeleAddHaarMeasure.prod
        rationalFiniteAdeleAddHaarMeasure)
        (rationalInfiniteAdeleNatDilationSet m hm ×ˢ
          integralFiniteAdeleNatDilationSet m) =
        rationalInfiniteAdeleAddHaarMeasure
            (rationalInfiniteAdeleNatDilationSet m hm) *
          rationalFiniteAdeleAddHaarMeasure
            (integralFiniteAdeleNatDilationSet m) :=
      Measure.prod_prod _ _
    _ = 1 := by
      rw [rationalInfiniteAdeleAddHaarMeasure_natDilationSet m hm,
        rationalFiniteAdeleAddHaarMeasure_natDilationSet m hm]
      exact ENNReal.mul_inv_cancel (by simp [hm]) (by simp)

/-- The distributive Haar character of the additive adeles, restricted to
the rational diagonal. -/
private noncomputable def rationalDiagonalAdditiveDilationCharacter :
    ℚˣ →* ℝ≥0 :=
  (MeasureTheory.distribHaarChar RationalAdele).comp
    rationalUnitFullAdelicDiagonalHom

private theorem rationalDiagonalAdditiveDilationCharacter_nat
    (m : ℕ) (hm : m ≠ 0) :
    rationalDiagonalAdditiveDilationCharacter (rationalNatUnit m hm) = 1 := by
  apply MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := rationalAdeleAddHaarMeasure)
    (s := rationalAdeleStandardBlock)
    (g := rationalUnitFullAdelicDiagonalHom (rationalNatUnit m hm))
    (r := 1)
  · rw [rationalAdeleAddHaarMeasure_standardBlock]
    exact one_ne_zero
  · rw [rationalAdeleAddHaarMeasure_standardBlock]
    simp
  · change rationalAdeleAddHaarMeasure
        (rationalAdeleNatDilationSet m hm) =
      (1 : ℝ≥0∞) * rationalAdeleAddHaarMeasure rationalAdeleStandardBlock
    rw [rationalAdeleAddHaarMeasure_natDilationSet m hm,
      rationalAdeleAddHaarMeasure_standardBlock, one_mul]

private theorem rationalDiagonalAdditiveDilationCharacter_neg_one :
    rationalDiagonalAdditiveDilationCharacter (-1 : ℚˣ) = 1 := by
  apply NNReal.eq
  have hsq :
      ((rationalDiagonalAdditiveDilationCharacter (-1 : ℚˣ) : ℝ) ^ 2) =
        1 := by
    rw [← NNReal.coe_pow, ← map_pow]
    norm_num
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact h
  · exfalso
    nlinarith [show (0 : ℝ) ≤
      rationalDiagonalAdditiveDilationCharacter (-1 : ℚˣ) from
        NNReal.coe_nonneg _]

private def rationalIntUnit (z : ℤ) (hz : z ≠ 0) : ℚˣ :=
  Units.mk0 (z : ℚ) (by exact_mod_cast hz)

private theorem rationalDiagonalAdditiveDilationCharacter_int
    (z : ℤ) (hz : z ≠ 0) :
    rationalDiagonalAdditiveDilationCharacter (rationalIntUnit z hz) = 1 := by
  cases z with
  | ofNat m =>
      have hm : m ≠ 0 := by simpa using hz
      simpa [rationalIntUnit, rationalNatUnit] using
        rationalDiagonalAdditiveDilationCharacter_nat m hm
  | negSucc m =>
      have hunit :
          rationalIntUnit (.negSucc m) hz =
            (-1 : ℚˣ) * rationalNatUnit (m + 1) (by omega) := by
        apply Units.ext
        simp [rationalIntUnit, rationalNatUnit]
      rw [hunit, map_mul,
        rationalDiagonalAdditiveDilationCharacter_neg_one,
        rationalDiagonalAdditiveDilationCharacter_nat (m + 1) (by omega),
        one_mul]

/-- The additive adelic distributive Haar character is trivial on every
rational diagonal. -/
theorem rationalAdele_distribHaarChar_rationalUnitDiagonal (q : ℚˣ) :
    MeasureTheory.distribHaarChar RationalAdele
        (rationalUnitFullAdelicDiagonalHom q) = 1 := by
  let numUnit : ℚˣ := rationalIntUnit (q : ℚ).num
    (Rat.num_ne_zero.mpr (Units.ne_zero q))
  let denUnit : ℚˣ := rationalNatUnit (q : ℚ).den
    (q : ℚ).den_ne_zero
  have hq : q = numUnit * denUnit⁻¹ := by
    apply Units.ext
    change (q : ℚ) = ((q : ℚ).num : ℚ) * ((q : ℚ).den : ℚ)⁻¹
    rw [← div_eq_mul_inv, Rat.num_div_den]
  change rationalDiagonalAdditiveDilationCharacter q = 1
  rw [hq, map_mul, map_inv,
    rationalDiagonalAdditiveDilationCharacter_int,
    rationalDiagonalAdditiveDilationCharacter_nat, inv_one, one_mul]

/-- Multiplication by a rational diagonal unit preserves the fixed additive
Haar on the literal full adeles. -/
theorem measurePreserving_rationalUnitFullAdelicDiagonal
    (q : ℚˣ) :
    MeasurePreserving
      (fun x : RationalAdele =>
        rationalUnitFullAdelicDiagonalHom q • x)
      rationalAdeleAddHaarMeasure rationalAdeleAddHaarMeasure := by
  refine ⟨(continuous_const_smul
    (rationalUnitFullAdelicDiagonalHom q)).measurable, ?_⟩
  change (DomMulAct.mk (rationalUnitFullAdelicDiagonalHom q)⁻¹) •
      rationalAdeleAddHaarMeasure = rationalAdeleAddHaarMeasure
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular
    ((DomMulAct.mk (rationalUnitFullAdelicDiagonalHom q)⁻¹) •
      rationalAdeleAddHaarMeasure) rationalAdeleAddHaarMeasure]
  rw [MeasureTheory.addHaarScalarFactor_smul_eq_distribHaarChar
    rationalAdeleAddHaarMeasure]
  have hchar := rationalAdele_distribHaarChar_rationalUnitDiagonal q⁻¹
  rw [map_inv] at hchar
  rw [hchar]
  simp

/-- Multiplication by a nonzero rational scalar preserves the fixed additive
Haar on the literal full adeles. -/
theorem measurePreserving_rationalAdele_rationalDilation
    (q : ℚ) (hq : q ≠ 0) :
    MeasurePreserving
      (fun x : RationalAdele => algebraMap ℚ RationalAdele q * x)
      rationalAdeleAddHaarMeasure rationalAdeleAddHaarMeasure := by
  simpa [rationalUnitFullAdelicDiagonalHom, Units.smul_def] using
    measurePreserving_rationalUnitFullAdelicDiagonal (Units.mk0 q hq)

theorem map_rationalAdeleAddHaarMeasure_rationalDilation
    (q : ℚ) (hq : q ≠ 0) :
    Measure.map (fun x : RationalAdele => algebraMap ℚ RationalAdele q * x)
        rationalAdeleAddHaarMeasure = rationalAdeleAddHaarMeasure :=
  (measurePreserving_rationalAdele_rationalDilation q hq).map_eq

/-- Coordinatewise multiplication by a nonzero rational preserves the exact
finite product of the fixed full-adelic Haar. -/
theorem measurePreserving_rationalAdeleCoordinate_rationalDilation
    (d : ℕ) (q : ℚ) (hq : q ≠ 0) :
    MeasurePreserving
      (fun x : Fin d → RationalAdele =>
        fun i => algebraMap ℚ RationalAdele q * x i)
      (rationalAdeleCoordinateAddHaarMeasure d)
      (rationalAdeleCoordinateAddHaarMeasure d) := by
  rw [rationalAdeleCoordinateAddHaarMeasure_eq_pi]
  exact measurePreserving_pi
    (fun _ : Fin d => rationalAdeleAddHaarMeasure)
    (fun _ : Fin d => rationalAdeleAddHaarMeasure)
    (fun _ => measurePreserving_rationalAdele_rationalDilation q hq)

theorem map_rationalAdeleCoordinateAddHaarMeasure_rationalDilation
    (d : ℕ) (q : ℚ) (hq : q ≠ 0) :
    Measure.map
        (fun x : Fin d → RationalAdele =>
          fun i => algebraMap ℚ RationalAdele q * x i)
        (rationalAdeleCoordinateAddHaarMeasure d) =
      rationalAdeleCoordinateAddHaarMeasure d :=
  (measurePreserving_rationalAdeleCoordinate_rationalDilation d q hq).map_eq

end PositiveDefiniteIntegralLattice

end

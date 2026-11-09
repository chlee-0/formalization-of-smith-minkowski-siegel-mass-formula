import SMSFormula.RationalFiniteAdeleQuadraticGaussAnnihilator

/-!
# Denominator containment for the finite quadratic Gauss annihilator

For an integral lattice, the finite polar matrix is its integral Gram matrix.
This file removes the numerator of a reduced rational parameter by Bezout,
then applies the integral adjugate identity.  The exact annihilator locus is
therefore contained in the standard finite-adelic lattice dilated by

`t.den / gcd t.den |det (2F)|`.

The existing finite-index Haar calculation then bounds the literal Gauss
integral by this exact dilation mass.  No primewise factorization, local Gauss
estimate, rational-height sum, or Eisenstein functional is asserted here.
-/

noncomputable section

open Matrix MeasureTheory RationalQuadraticSpaceMatrix Set

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

private theorem inv_den_mul_mem_integralFiniteAdeleSubring
    (t : ℚ) (x : RationalFiniteAdele)
    (hx : x ∈ integralFiniteAdeleSubring)
    (htx : algebraMap ℚ RationalFiniteAdele t * x ∈
      integralFiniteAdeleSubring) :
    algebraMap ℚ RationalFiniteAdele ((t.den : ℚ)⁻¹) * x ∈
      integralFiniteAdeleSubring := by
  let u : ℤ := Int.gcdA t.num (t.den : ℤ)
  let v : ℤ := Int.gcdB t.num (t.den : ℤ)
  have hbez : (1 : ℤ) = t.num * u + (t.den : ℤ) * v := by
    rw [← Int.gcd_eq_gcd_ab]
    simp [Int.gcd_eq_natAbs, t.reduced.gcd_eq_one]
  have heq :
      algebraMap ℚ RationalFiniteAdele ((t.den : ℚ)⁻¹) * x =
        algebraMap ℤ RationalFiniteAdele u *
            (algebraMap ℚ RationalFiniteAdele t * x) +
          algebraMap ℤ RationalFiniteAdele v * x := by
    have hdenQ : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_nz
    have hcoeff : ((t.den : ℚ)⁻¹) = (u : ℚ) * t + (v : ℚ) := by
      apply (mul_right_cancel₀ hdenQ)
      rw [inv_mul_cancel₀ hdenQ, add_mul, mul_assoc,
        t.mul_den_eq_num]
      exact_mod_cast (by simpa [mul_comm] using hbez)
    have hu : algebraMap ℤ RationalFiniteAdele u =
        algebraMap ℚ RationalFiniteAdele (u : ℚ) := by norm_num
    have hv : algebraMap ℤ RationalFiniteAdele v =
        algebraMap ℚ RationalFiniteAdele (v : ℚ) := by norm_num
    rw [hcoeff, map_add, map_mul]
    rw [hu, hv]
    ring
  rw [heq]
  exact integralFiniteAdeleSubring.add_mem
    (integralFiniteAdeleSubring.mul_mem
      (integer_mem_integralFiniteAdeleSubring u) htx)
    (integralFiniteAdeleSubring.mul_mem
      (integer_mem_integralFiniteAdeleSubring v) hx)

theorem integralFiniteAdeleVectors_mulVec_intMatrix
    (C : Matrix (Fin n) (Fin n) ℤ)
    (z : Fin n → RationalFiniteAdele)
    (hz : z ∈ integralFiniteAdeleVectors n) :
    (C.map (algebraMap ℤ RationalFiniteAdele)).mulVec z ∈
      integralFiniteAdeleVectors n := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem integralFiniteAdeleSubring fun j _ =>
    integralFiniteAdeleSubring.mul_mem
      (integer_mem_integralFiniteAdeleSubring (C i j)) (hz j)

/-- The exact denominator dilation left after allowing the determinant of the
integral polar matrix. -/
def finiteQuadraticGaussDenominatorDilation
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) : ℕ :=
  t.den / Nat.gcd t.den L.polarDeterminant.natAbs

/-- The determinant-corrected denominator dilation is positive. -/
theorem finiteQuadraticGaussDenominatorDilation_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    L.finiteQuadraticGaussDenominatorDilation t ≠ 0 := by
  apply Nat.ne_of_gt
  apply Nat.div_pos
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero t.den_nz)
      (Nat.gcd_dvd_left t.den L.polarDeterminant.natAbs)
  · exact Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero t.den_nz)

/-- For an integral lattice, the finite-adelic polar matrix is the image of
its integral Gram matrix. -/
theorem rationalQuadraticSpaceMatrix_finiteAdelicPolarMatrix_eq_map_polarGramMatrix
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix =
      L.polarGramMatrix.map (algebraMap ℤ RationalFiniteAdele) := by
  ext i j
  simp [RationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix,
    RationalQuadraticSpaceMatrix.polarMatrix,
    PositiveDefiniteIntegralLattice.rationalQuadraticSpaceMatrix,
    PositiveDefiniteIntegralLattice.rationalFormMatrix,
    PositiveDefiniteIntegralLattice.polarGramMatrix, Matrix.transpose_apply,
    L.form_symm.apply, two_mul]

private theorem den_polarDeterminant_div_den_eq_finiteQuadraticGaussDenominatorDilation
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    (((L.polarDeterminant : ℚ) / (t.den : ℚ)).den) =
      L.finiteQuadraticGaussDenominatorDilation t := by
  let d := L.polarDeterminant.natAbs
  let g := Nat.gcd t.den d
  let k := d / g
  let m := t.den / g
  have htdenpos : 0 < t.den := Nat.pos_of_ne_zero t.den_nz
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left d htdenpos
  have hmpos : 0 < m := Nat.div_pos
    (Nat.le_of_dvd htdenpos (Nat.gcd_dvd_left t.den d)) hgpos
  have hcop : k.Coprime m :=
    (Nat.coprime_div_gcd_div_gcd hgpos).symm
  have hgd : g * k = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right t.den d)
  have hgden : g * m = t.den :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left t.den d)
  have hdisc : (d : ℤ) = L.polarDeterminant := by
    exact Int.natAbs_of_nonneg (le_of_lt L.polarDeterminant_pos)
  have hratio :
      (L.polarDeterminant : ℚ) / (t.den : ℚ) = (k : ℚ) / (m : ℚ) := by
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hmpos)
    have htQ : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_nz
    apply (div_eq_div_iff htQ hmQ).2
    have hnat : d * m = k * t.den := by
      rw [← hgd, ← hgden]
      ring
    have hnatInt : (d : ℤ) * (m : ℤ) = (k : ℤ) * (t.den : ℤ) := by
      exact_mod_cast hnat
    exact_mod_cast (by simpa [hdisc] using hnatInt)
  have hdenInt := Rat.den_div_eq_of_coprime
    (a := (k : ℤ)) (b := (m : ℤ))
    (by exact_mod_cast hmpos) (by simpa using hcop)
  change (((L.polarDeterminant : ℚ) / (t.den : ℚ)).den) = m
  rw [hratio]
  apply Int.ofNat_inj.mp
  simpa using hdenInt

/-- The exact finite quadratic annihilator of an integral lattice is contained
in the determinant-corrected denominator dilation. -/
theorem finiteQuadraticGaussAnnihilatorLocus_subset_denominatorDilation
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    L.rationalQuadraticSpaceMatrix.finiteQuadraticGaussAnnihilatorLocus t ⊆
      integralFiniteAdeleCoordinateNatDilationSet n
        (L.finiteQuadraticGaussDenominatorDilation t) := by
  intro z hz
  let C := L.polarGramMatrix
  let Cfa := C.map (algebraMap ℤ RationalFiniteAdele)
  let denInv : RationalFiniteAdele :=
    algebraMap ℚ RationalFiniteAdele ((t.den : ℚ)⁻¹)
  let y : Fin n → RationalFiniteAdele := denInv • Cfa.mulVec z
  have hzint : z ∈ integralFiniteAdeleVectors n := hz.1
  have hCz : Cfa.mulVec z ∈ integralFiniteAdeleVectors n :=
    integralFiniteAdeleVectors_mulVec_intMatrix C z hzint
  have hscaled : ∀ i,
      algebraMap ℚ RationalFiniteAdele t * (Cfa.mulVec z) i ∈
        integralFiniteAdeleSubring := by
    intro i
    have hi := hz.2 i
    change algebraMap ℚ RationalFiniteAdele t *
      (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec z) i ∈
        integralFiniteAdeleSubring at hi
    rw [L.rationalQuadraticSpaceMatrix_finiteAdelicPolarMatrix_eq_map_polarGramMatrix]
      at hi
    exact hi
  have hy : y ∈ integralFiniteAdeleVectors n := by
    intro i
    exact inv_den_mul_mem_integralFiniteAdeleSubring t (Cfa.mulVec z i)
      (hCz i) (hscaled i)
  have hadjy :
      (C.adjugate.map (algebraMap ℤ RationalFiniteAdele)).mulVec y ∈
        integralFiniteAdeleVectors n :=
    integralFiniteAdeleVectors_mulVec_intMatrix C.adjugate y hy
  let q : ℚ := (L.polarDeterminant : ℚ) / (t.den : ℚ)
  have hmapAdjugate :
      C.adjugate.map (algebraMap ℤ RationalFiniteAdele) *
          C.map (algebraMap ℤ RationalFiniteAdele) =
        L.polarDeterminant •
          (1 : Matrix (Fin n) (Fin n) RationalFiniteAdele) := by
    rw [← Matrix.map_mul, Matrix.adjugate_mul]
    rw [show C.det = L.polarDeterminant by rfl]
    simpa using Matrix.map_smul (algebraMap ℤ RationalFiniteAdele) L.polarDeterminant
      (fun a => map_zsmul (algebraMap ℤ RationalFiniteAdele) L.polarDeterminant a)
      (1 : Matrix (Fin n) (Fin n) ℤ)
  have hqz : ∀ i,
      algebraMap ℚ RationalFiniteAdele q * z i ∈
        integralFiniteAdeleSubring := by
    intro i
    have hi := hadjy i
    convert hi using 1
    dsimp [y, denInv, Cfa, C, q]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hmapAdjugate,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Pi.mul_apply]
    have hcoef :
        algebraMap ℚ RationalFiniteAdele
            ((L.polarDeterminant : ℚ) / (t.den : ℚ)) =
          algebraMap ℚ RationalFiniteAdele ((t.den : ℚ)⁻¹) *
            algebraMap ℚ RationalFiniteAdele (L.polarDeterminant : ℚ) := by
      rw [div_eq_mul_inv, map_mul]
      ring
    rw [hcoef]
    norm_num
    ring
  have hzinv : ∀ i,
      algebraMap ℚ RationalFiniteAdele ((q.den : ℚ)⁻¹) * z i ∈
        integralFiniteAdeleSubring := fun i =>
    inv_den_mul_mem_integralFiniteAdeleSubring q (z i) (hzint i) (hqz i)
  have hqden : q.den = L.finiteQuadraticGaussDenominatorDilation t := by
    exact den_polarDeterminant_div_den_eq_finiteQuadraticGaussDenominatorDilation L t
  rw [integralFiniteAdeleCoordinateNatDilationSet]
  intro i _hi
  refine ⟨⟨algebraMap ℚ RationalFiniteAdele
      ((L.finiteQuadraticGaussDenominatorDilation t : ℚ)⁻¹) * z i, ?_⟩, ?_⟩
  · simpa [hqden] using hzinv i
  · change L.finiteQuadraticGaussDenominatorDilation t •
        (algebraMap ℚ RationalFiniteAdele
          ((L.finiteQuadraticGaussDenominatorDilation t : ℚ)⁻¹) * z i) = z i
    rw [nsmul_eq_mul]
    rw [show (L.finiteQuadraticGaussDenominatorDilation t :
          RationalFiniteAdele) =
        algebraMap ℚ RationalFiniteAdele
          (L.finiteQuadraticGaussDenominatorDilation t : ℚ) by norm_num]
    rw [← mul_assoc, ← map_mul]
    simp [L.finiteQuadraticGaussDenominatorDilation_ne_zero t]

/-- The exact annihilator mass is at most the Haar mass of its determinant-
corrected denominator dilation. -/
theorem measure_finiteQuadraticGaussAnnihilatorLocus_le_denominatorDilation
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    rationalFiniteAdeleCoordinateAddHaarMeasure n
        (L.rationalQuadraticSpaceMatrix.finiteQuadraticGaussAnnihilatorLocus t) ≤
      ((L.finiteQuadraticGaussDenominatorDilation t : ENNReal)⁻¹) ^ n := by
  calc
    rationalFiniteAdeleCoordinateAddHaarMeasure n
        (L.rationalQuadraticSpaceMatrix.finiteQuadraticGaussAnnihilatorLocus t) ≤
        rationalFiniteAdeleCoordinateAddHaarMeasure n
          (integralFiniteAdeleCoordinateNatDilationSet n
            (L.finiteQuadraticGaussDenominatorDilation t)) :=
      measure_mono (L.finiteQuadraticGaussAnnihilatorLocus_subset_denominatorDilation t)
    _ = ((L.finiteQuadraticGaussDenominatorDilation t : ENNReal)⁻¹) ^ n :=
      rationalFiniteAdeleCoordinateAddHaarMeasure_natDilationSet n _
        (L.finiteQuadraticGaussDenominatorDilation_ne_zero t)

/-- The squared norm of the literal finite Gauss integral has the exact
determinant-corrected denominator bound. -/
theorem norm_quadraticGaussIntegral_sq_le_denominatorDilation
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t‖ ^ 2 ≤
      (((L.finiteQuadraticGaussDenominatorDilation t : ENNReal)⁻¹) ^ n).toReal := by
  calc
    ‖L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegral t‖ ^ 2 ≤
        (rationalFiniteAdeleCoordinateAddHaarMeasure n
          (L.rationalQuadraticSpaceMatrix.finiteQuadraticGaussAnnihilatorLocus t)).toReal :=
      L.rationalQuadraticSpaceMatrix.norm_quadraticGaussIntegral_sq_le_measure_annihilatorLocus t
    _ ≤ (((L.finiteQuadraticGaussDenominatorDilation t : ENNReal)⁻¹) ^ n).toReal :=
      ENNReal.toReal_mono
        (ENNReal.pow_ne_top ((ENNReal.inv_ne_top).2
          (Nat.cast_ne_zero.mpr
            (L.finiteQuadraticGaussDenominatorDilation_ne_zero t))))
        (L.measure_finiteQuadraticGaussAnnihilatorLocus_le_denominatorDilation t)

end PositiveDefiniteIntegralLattice

end

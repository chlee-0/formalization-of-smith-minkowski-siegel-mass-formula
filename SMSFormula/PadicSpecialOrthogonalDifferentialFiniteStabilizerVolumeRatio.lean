import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteStabilizerVolume

/-!
# Ratios of finite differential stabilizer volumes as limits of partial ratios

For two lattices `A`, `L` with Schulze--Pillot cutoff limits `P_A, P_L > 0`, the finite
differential stabilizer volumes `t_A`, `t_L` (the finite scales `t` in the periodization scalar
`h = a · t · b`) satisfy

`t_A / t_L = lim_N (∏_{q ≤ N} vol(SO_A(ℤ_q))) / (∏_{q ≤ N} vol(SO_L(ℤ_q)))`,

with the corrected local differential stabilizer volumes.  This is the form in which the
good-place ledger `vol_V/vol_W = |r|_q · ν(ℤ_q) · δ_q(a)` can be compared with the Euler product
`∏' δ_q(a)` of the orbit Riesz ratio.  Nothing is chosen.
-/

noncomputable section

open Filter Topology
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n m : ℕ}

/-- The finite stabilizer volume is the inverse of the inverse-volume scalar. -/
theorem localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_inv
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) :
    (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P)⁻¹ =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume P := by
  rw [localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume, inv_inv]

/-- Ratio of finite stabilizer volumes: `t_A / t_L` is the limit of the ratios of the partial
products of the local differential stabilizer volumes. -/
theorem tendsto_prod_stabilizerVolume_div_prod_stabilizerVolume
    (A : PositiveDefiniteIntegralLattice n) (L : PositiveDefiniteIntegralLattice m) [NeZero n] [NeZero m] {PA PL : ℝ}
    (hPA0 : 0 < PA) (hA : massLocalInverseProductTendsTo A PA)
    (hL : massLocalInverseProductTendsTo L PL) :
    Tendsto (fun N : ℕ ↦
        (∏ q ∈ rationalPrimesUpTo N, A.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q) /
          ∏ q ∈ rationalPrimesUpTo N, L.localPadicSpecialOrthogonalDifferentialStabilizerVolumeAtPrime q)
      atTop
      (𝓝 (A.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume PA /
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume PL)) := by
  have hAt := A.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo_finiteStabilizerInverseVolume_of_massLocalInverseProductTendsTo hA
  have hLt := L.localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo_finiteStabilizerInverseVolume_of_massLocalInverseProductTendsTo hL
  unfold localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumeProductTendsTo at hAt hLt
  have hdiv := ENNReal.Tendsto.div hLt
    (Or.inr (A.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_zero hPA0))
    hAt (Or.inl (A.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume_ne_top PA))
  have hval : L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume PL /
        A.localPadicSpecialOrthogonalDifferentialFiniteStabilizerInverseVolume PA =
      A.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume PA /
        L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume PL := by
    rw [← localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_inv,
      ← localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume_inv, div_eq_mul_inv,
      div_eq_mul_inv, inv_inv, mul_comm]
  rw [hval] at hdiv
  refine hdiv.congr (fun N ↦ ?_)
  simp only [localPadicSpecialOrthogonalDifferentialStabilizerInverseVolumePartialProduct]
  rw [div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_comm]

end PositiveDefiniteIntegralLattice

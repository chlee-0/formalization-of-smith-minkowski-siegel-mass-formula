import SMSFormula.RationalAdeleRankOneFiniteGaussReciprocity
import SMSFormula.RationalAdeleRankOneWeylBruhatDecomposition

/-!
# Weyl transformation of the convergent rational cusp functional

The exact finite Gauss reciprocity theorem closes the nonzero analytic Bruhat
relation on the concrete polar Gaussian--lattice orbit.  Together with the
already proved Fourier square, this identifies every summand after applying
`W` with the old summand at the explicit rational Weyl cusp involution.

The involution then transports the certified summable family.  In particular,
the transformed finite Bruhat family is proved summable before its functional
is formed.  No generic Weil representation or nonsummable `tsum` convention
is used.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

/-- The concrete Weyl-transformed cusp summand is the original summand
reindexed by the explicit rational Weyl cusp involution.  Infinity, zero, and
the nonzero affine chart are handled by the literal Fourier-square and Bruhat
identities. -/
theorem rationalAdeleRankOneEisensteinSiegelSummand_weyl_polarGaussianLattice
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) (hn : n ≠ 0)
    {a : ℝ} (ha : 0 < a) (c : RationalRankOneProjectiveCusp) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneEisensteinSiegelSummand
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))) c =
      L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneEisensteinSiegelSummand
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))
        (rationalRankOneWeylCuspAction c) := by
  rcases c with u | t
  · cases u
    simp [rationalAdeleRankOneEisensteinSiegelSummand]
  · by_cases ht : t = 0
    · subst t
      simp only [rationalRankOneWeylCuspAction_finite_zero,
        rationalAdeleRankOneEisensteinSiegelSummand_finite,
        rationalAdeleRankOneEisensteinSiegelSummand_infinity,
        rationalAdeleRankOneBruhatCoefficient_zero]
      rw [rationalAdeleRankOneWeylOperator_iterate_two_polarGaussianLattice_eq_negOneDilation
        L ha]
      simp
      congr 1
    · rw [rationalRankOneWeylCuspAction_finite_of_ne_zero ht]
      simp only [rationalAdeleRankOneEisensteinSiegelSummand_finite]
      rw [rationalAdeleRankOneBruhatCoefficient]
      rw [rationalAdeleRankOne_nonzeroBruhatAnalyticRelation L hn ha ht]
      rw [rationalAdeleRankOne_nonzeroBruhatTarget_zero_eq_bruhatCoefficient]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

/-- In rank at least five, the finite Bruhat family of the concrete
Weyl-transformed test is summable.  The proof first transports the whole
`Unit + ℚ` family through the cusp involution and only then restricts to the
finite chart. -/
theorem summable_rationalAdeleRankOneBruhatCoefficient_weyl_polarGaussianLattice_of_rankAtLeastFive
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (hn : 5 ≤ n) :
    Summable
      (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)))) := by
  have hn0 : n ≠ 0 := by omega
  have horig :=
    L.summable_rationalAdeleRankOneEisensteinSiegelSummand_polarGaussianLattice_of_rankAtLeastFive
      ha hn
  have hcomp : Summable
      (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneEisensteinSiegelSummand
        (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) ∘
          rationalRankOneWeylCuspEquiv) :=
    (rationalRankOneWeylCuspEquiv.summable_iff).2 horig
  have hwhole : Summable
      (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneEisensteinSiegelSummand
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)))) := by
    apply hcomp.congr
    intro c
    exact
      (RationalQuadraticSpaceMatrix.rationalAdeleRankOneEisensteinSiegelSummand_weyl_polarGaussianLattice
        L hn0 ha c).symm
  exact hwhole.comp_injective Sum.inr_injective

/-- The convergence-certified specialized cusp functional is invariant under
the concrete Weyl operator. -/
theorem rationalAdeleRankOneEisensteinSiegelFunctional_weyl_polarGaussianLattice
    {n : ℕ} (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a)
    (hn : 5 ≤ n) :
    L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneEisensteinSiegelFunctional
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)))
        (L.summable_rationalAdeleRankOneBruhatCoefficient_weyl_polarGaussianLattice_of_rankAtLeastFive
          ha hn) =
      L.rationalAdeleRankOneEisensteinSiegelFunctional_polarGaussianLattice
        ha hn := by
  rw [rationalAdeleRankOneEisensteinSiegelFunctional_polarGaussianLattice]
  unfold rationalAdeleRankOneEisensteinSiegelFunctional
  calc
    (∑' c : RationalRankOneProjectiveCusp,
      L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneEisensteinSiegelSummand
        (L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneWeylOperator
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))) c) =
        ∑' c : RationalRankOneProjectiveCusp,
          L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneEisensteinSiegelSummand
            (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))
            (rationalRankOneWeylCuspEquiv c) := by
      apply tsum_congr
      intro c
      exact
        RationalQuadraticSpaceMatrix.rationalAdeleRankOneEisensteinSiegelSummand_weyl_polarGaussianLattice
          L (by omega) ha c
    _ = ∑' c : RationalRankOneProjectiveCusp,
          L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneEisensteinSiegelSummand
            (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) c :=
      rationalRankOneWeylCuspEquiv.tsum_eq _

end PositiveDefiniteIntegralLattice

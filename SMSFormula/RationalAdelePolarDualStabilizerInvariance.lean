import SMSFormula.RationalAdeleRankOneWeilGenerators
import SMSFormula.RationalCliffordGeneralSpinThetaCutoffDomination

/-!
# The polar dual carrier has the same stabilizer invariance as the standard one

The remaining finiteness route for the Weyl transform is a finiteness statement for the family
whose finite carrier is the polar dual lattice.  The existing proof for the standard test rests
on the test being fixed on the right by the integral finite stabilizer; this file supplies the
same property for the dual carrier, which is the first ingredient of that generalization.

The argument is the form relation itself.  An element of the finite orthogonal group satisfies
`g^T F g = F`, hence `g^T C g = C` for the polar matrix `C = 2F`; so `g^T (C (g y)) = C y`.
Since a stabilizer element has integral entries, so does its transpose, and integrality of
`C (g y)` therefore forces integrality of `C y`.  Applying the same implication to `g` inverse
gives the converse, so membership in the polar dual lattice is invariant.

Negative scope: invariance of the carrier, not finiteness of anything.  No theta bound, no
proper-domain factorization and no raw integral is treated here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The adelic polar matrix is twice the adelic form matrix. -/
theorem finiteAdelicPolarMatrix_eq_two_smul (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix =
      (2 : RationalFiniteAdele) • L.finiteAdelicFormMatrix := by
  ext i j
  simp [RationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix,
    RationalQuadraticSpaceMatrix.polarMatrix, PositiveDefiniteIntegralLattice.rationalFormMatrix,
    PositiveDefiniteIntegralLattice.finiteAdelicFormMatrix, IsScalarTower.algebraMap_apply ℤ ℚ,
    map_ofNat]

/-- The polar matrix is preserved by the finite orthogonal group. -/
theorem finiteAdelicOrthogonal_polarMatrix_conj
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFiniteAdelicOrthogonalGroup) :
    g.1.1ᵀ * L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix * g.1.1 =
      L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix := by
  have hform : g.1.1ᵀ * L.finiteAdelicFormMatrix * g.1.1 = L.finiteAdelicFormMatrix := g.2
  rw [L.finiteAdelicPolarMatrix_eq_two_smul, Matrix.mul_smul, Matrix.smul_mul, hform]

/-- The transpose of a stabilizer element has integral entries. -/
theorem transpose_mem_integralFiniteAdeleSubring
    (L : PositiveDefiniteIntegralLattice n) {g : L.ConcreteFiniteAdelicOrthogonalGroup}
    (hg : g ∈ L.finiteLocalLatticeStabilizerSubgroup) (i j : Fin n) :
    g.1.1ᵀ i j ∈ integralFiniteAdeleSubring :=
  hg.1 j i

/-- One direction: integrality of the polar image transfers backwards along a stabilizer
element, by the form relation and integrality of the transpose. -/
theorem polar_mulVec_mem_of_stabilizer
    (L : PositiveDefiniteIntegralLattice n) {g : L.ConcreteFiniteAdelicOrthogonalGroup}
    (hg : g ∈ L.finiteLocalLatticeStabilizerSubgroup)
    {y : Fin n → RationalFiniteAdele}
    (hy : L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec
      (g.1.1.mulVec y) ∈ integralFiniteAdeleVectors n) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec y ∈
      integralFiniteAdeleVectors n := by
  have hstep : g.1.1ᵀ.mulVec
      (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec (g.1.1.mulVec y)) =
      L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec y := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      L.finiteAdelicOrthogonal_polarMatrix_conj g]
  rw [← hstep]
  exact matrix_mulVec_mem_integralFiniteAdeleVectors
    (fun i j => L.transpose_mem_integralFiniteAdeleSubring hg i j) hy

/-- The invariance: the polar dual lattice is stable under the finite lattice stabilizer. -/
theorem mem_finitePolarDualLattice_stabilizer_mulVec_iff
    (L : PositiveDefiniteIntegralLattice n) {g : L.ConcreteFiniteAdelicOrthogonalGroup}
    (hg : g ∈ L.finiteLocalLatticeStabilizerSubgroup)
    (y : Fin n → RationalFiniteAdele) :
    g.1.1.mulVec y ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice ↔
      y ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice := by
  constructor
  · exact fun h => L.polar_mulVec_mem_of_stabilizer hg h
  · intro h
    have hinv : g⁻¹ ∈ L.finiteLocalLatticeStabilizerSubgroup := inv_mem hg
    have hcancel : (g⁻¹).1.1.mulVec (g.1.1.mulVec y) = y := by
      rw [Matrix.mulVec_mulVec]
      have hval : ((g⁻¹).1 * g.1).1 = 1 := by simp
      change ((g⁻¹).1.1 * g.1.1).mulVec y = y
      rw [show (g⁻¹).1.1 * g.1.1 = 1 from hval, Matrix.one_mulVec]
    refine L.polar_mulVec_mem_of_stabilizer (g := g⁻¹) hinv ?_
    rwa [hcancel]

/-- Hence the polar dual indicator is fixed by the stabilizer, exactly as the standard one. -/
theorem finitePolarDualLatticeIndicator_stabilizer_mulVec
    (L : PositiveDefiniteIntegralLattice n) {g : L.ConcreteFiniteAdelicOrthogonalGroup}
    (hg : g ∈ L.finiteLocalLatticeStabilizerSubgroup)
    (y : Fin n → RationalFiniteAdele) :
    L.rationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator (g.1.1.mulVec y) =
      L.rationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator y := by
  by_cases hy : y ∈ L.rationalQuadraticSpaceMatrix.finitePolarDualLattice
  · rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_mem _
      ((L.mem_finitePolarDualLattice_stabilizer_mulVec_iff hg y).mpr hy),
      RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_mem _ hy]
  · rw [RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_not_mem _
      (fun h => hy ((L.mem_finitePolarDualLattice_stabilizer_mulVec_iff hg y).mp h)),
      RationalQuadraticSpaceMatrix.finitePolarDualLatticeIndicator_of_not_mem _ hy]

end PositiveDefiniteIntegralLattice

end

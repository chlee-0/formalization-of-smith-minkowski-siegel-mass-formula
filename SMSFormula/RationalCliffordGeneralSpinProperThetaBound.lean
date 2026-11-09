import SMSFormula.RationalCliffordGeneralSpinBoundedThetaFiniteness

/-!
# The proper-domain bound, for any stabilizer-invariant test

The existing proper-domain argument is written for the standard polar Gaussian--lattice test,
but it uses that test only through two properties: right invariance under the real/integral
stabilizer, and pointwise finiteness of its theta.  This file states and proves the same chain
with the test abstracted, so that a new carrier -- in particular the polar dual one, whose
stabilizer invariance is already proved -- can use it by supplying exactly those two facts.

The chain is: invariance of the test gives right invariance of the theta; the existing proper
domain then identifies the theta with its value at the proper representative of the piece label;
so the finite sum over the finitely many proper representatives bounds the theta everywhere; and
that sum is finite as soon as each of its terms is.  Combined with the criterion that a bounded
quotient theta gives raw finiteness, a new carrier needs only pointwise theta finiteness.

Negative scope: pointwise finiteness is supplied for no new test here.  For the polar dual
carrier it remains the one genuinely analytic input, the analogue of the existing theta
summability.
-/

noncomputable section

open MeasureTheory RationalQuadraticSpaceMatrix
open PositiveDefiniteIntegralLattice
open scoped ENNReal BigOperators

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The concrete `SO` theta of an arbitrary nonnegative test. -/
def concreteSpecialOrthogonalTheta (L : PositiveDefiniteIntegralLattice n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) : ℝ≥0∞ :=
  ∑' x : Fin n → ℚ, Phi ((g⁻¹).1.1.1.mulVec (rationalAdeleVectorDiagonal n x))

theorem concreteSpecialOrthogonalTheta_eq_intrinsic (L : PositiveDefiniteIntegralLattice n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.concreteSpecialOrthogonalTheta Phi g =
      L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalTheta Phi
        (L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv.symm g) := by
  unfold concreteSpecialOrthogonalTheta
  unfold RationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalTheta
  unfold RationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalRationalVectorAction
  rw [← map_inv]
  rw [L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalEquiv_symm_apply_matrix]

/-- Right invariance of the theta, from right invariance of the test. -/
theorem concreteSpecialOrthogonalTheta_mul_stabilizer (L : PositiveDefiniteIntegralLattice n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞}
    (hinv : ∀ (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup)
      (x : Fin n → RationalAdele), Phi (h.1.1.1.1.mulVec x) = Phi x)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup) :
    L.concreteSpecialOrthogonalTheta Phi (g * h.1) =
      L.concreteSpecialOrthogonalTheta Phi g := by
  unfold concreteSpecialOrthogonalTheta
  have hmulVec (x : Fin n → ℚ) :
      (((g * h.1)⁻¹).1.1.1).mulVec (rationalAdeleVectorDiagonal n x) =
        (h⁻¹).1.1.1.1.mulVec
          ((g⁻¹).1.1.1.mulVec (rationalAdeleVectorDiagonal n x)) := by
    rw [_root_.mul_inv_rev]
    change
      (((h⁻¹).1.1.1.1 * (g⁻¹).1.1.1).mulVec (rationalAdeleVectorDiagonal n x)) = _
    rw [Matrix.mulVec_mulVec]
  apply tsum_congr
  intro x
  rw [hmulVec]
  exact hinv h⁻¹ ((g⁻¹).1.1.1.mulVec (rationalAdeleVectorDiagonal n x))

/-- The concrete theta descends to the rational `SO` left quotient. -/
def concreteSpecialOrthogonalThetaOnLeftQuotient (L : PositiveDefiniteIntegralLattice n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞) :
    L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient → ℝ≥0∞ :=
  L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalThetaOnLeftQuotient Phi ∘
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv.symm

@[simp]
theorem concreteSpecialOrthogonalThetaOnLeftQuotient_mk (L : PositiveDefiniteIntegralLattice n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.concreteSpecialOrthogonalThetaOnLeftQuotient Phi
        (L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap g) =
      L.concreteSpecialOrthogonalTheta Phi g := by
  rw [concreteSpecialOrthogonalThetaOnLeftQuotient, Function.comp_apply,
    L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv_symm_mk,
    L.rationalQuadraticSpaceMatrix.fullAdelicSpecialOrthogonalThetaOnLeftQuotient_mk]
  exact (L.concreteSpecialOrthogonalTheta_eq_intrinsic Phi g).symm

/-- On the proper domain the theta is its value at the proper representative. -/
theorem concreteSpecialOrthogonalTheta_properDomain (L : PositiveDefiniteIntegralLattice n)
    [Nonempty (Fin n)] {Phi : (Fin n → RationalAdele) → ℝ≥0∞}
    (hinv : ∀ (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup)
      (x : Fin n → RationalAdele), Phi (h.1.1.1.1.mulVec x) = Phi x)
    (z : {g : L.ConcreteFullAdelicSpecialOrthogonalGroup //
      g ∈ L.concreteFullAdelicProperTransversal}) :
    L.concreteSpecialOrthogonalTheta Phi z.1 =
      L.concreteSpecialOrthogonalTheta Phi
        (L.concreteFullAdelicProperTransversalRepresentative
          (L.concreteFullAdelicProperDomainPieceLabel z)) := by
  let h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup :=
    L.fullAdelicRealFiniteLatticeStabilizerContinuousMulEquiv
      ((L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv z.1).1,
        L.concreteFullAdelicProperDomainSelectorElement z)
  have hz : z.1 =
      L.concreteFullAdelicProperTransversalRepresentative
          (L.concreteFullAdelicProperDomainPieceLabel z) * h.1 :=
    L.concreteFullAdelicProperDomainSelectorElement_factor z
  rw [hz, L.concreteSpecialOrthogonalTheta_mul_stabilizer hinv]

/-- The finite sum over the proper representatives. -/
noncomputable def properThetaBound (L : PositiveDefiniteIntegralLattice n)
    (Phi : (Fin n → RationalAdele) → ℝ≥0∞)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet) : ℝ≥0∞ :=
  @Finset.sum L.ConcreteProperRationalDoubleCosetSet ℝ≥0∞ _
    (@Finset.univ L.ConcreteProperRationalDoubleCosetSet inst)
    (fun C ↦ L.concreteSpecialOrthogonalTheta Phi
      (L.concreteFullAdelicProperTransversalRepresentative C))

theorem concreteSpecialOrthogonalThetaOnLeftQuotient_le_properThetaBound
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞}
    (hinv : ∀ (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup)
      (x : Fin n → RationalAdele), Phi (h.1.1.1.1.mulVec x) = Phi x)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (q : L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient) :
    L.concreteSpecialOrthogonalThetaOnLeftQuotient Phi q ≤
      L.properThetaBound Phi inst := by
  let z := L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDomain q
  let C := L.concreteFullAdelicProperDomainPieceLabel z
  have hq : L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap z.1 = q :=
    L.concreteFullAdelicSpecialOrthogonalLeftQuotientProperDomainEquiv.left_inv q
  have htheta : L.concreteSpecialOrthogonalThetaOnLeftQuotient Phi q =
      L.concreteSpecialOrthogonalTheta Phi
        (L.concreteFullAdelicProperTransversalRepresentative C) := by
    rw [← hq, L.concreteSpecialOrthogonalThetaOnLeftQuotient_mk]
    exact L.concreteSpecialOrthogonalTheta_properDomain hinv z
  rw [htheta]
  exact Finset.single_le_sum
    (fun C' _hC' ↦ (show (0 : ℝ≥0∞) ≤ L.concreteSpecialOrthogonalTheta Phi
      (L.concreteFullAdelicProperTransversalRepresentative C') from zero_le))
    (Finset.mem_univ C)

theorem properThetaBound_ne_top (L : PositiveDefiniteIntegralLattice n)
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞}
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (hfin : ∀ g : L.ConcreteFullAdelicSpecialOrthogonalGroup,
      L.concreteSpecialOrthogonalTheta Phi g ≠ ⊤) :
    L.properThetaBound Phi inst ≠ ⊤ := by
  unfold properThetaBound
  exact ENNReal.sum_ne_top.2 fun C _hC => hfin _

/-- The bound on the `GSpin` quotient theta, for any stabilizer-invariant test. -/
theorem fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_le_properThetaBound
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    {Phi : (Fin n → RationalAdele) → ℝ≥0∞}
    (hinv : ∀ (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup)
      (x : Fin n → RationalAdele), Phi (h.1.1.1.1.mulVec x) = Phi x)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    (Z : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient) :
    L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient Phi Z ≤
      L.properThetaBound Phi inst := by
  let V := L.rationalQuadraticSpaceMatrix
  let q := V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal Z
  have hbound := L.concreteSpecialOrthogonalThetaOnLeftQuotient_le_properThetaBound
    hinv inst (L.rationalQuadraticSpaceMatrixFullAdelicLeftQuotientEquiv q)
  rw [concreteSpecialOrthogonalThetaOnLeftQuotient, Function.comp_apply,
    Equiv.symm_apply_apply] at hbound
  rw [V.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_eq_specialOrthogonalTheta]
  exact hbound

end PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

/-- The payoff: for any stabilizer-invariant test whose concrete `SO` theta is pointwise
finite, the raw cutoff integral against the existing unit cutoff is finite, hence so is the
cutoff-normalized functional. -/
theorem cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_ne_top_of_stabilizerInvariant
    (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))]
    (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {cutoffProduct : ℝ} (hcutoffProduct : 0 < cutoffProduct)
    (hconv : massLocalInverseProductTendsTo L cutoffProduct)
    {Phi : (Fin (r + 2) → RationalAdele) → ℝ≥0∞}
    (hinv : ∀ (h : L.fullAdelicRealFiniteLatticeStabilizerSubgroup)
      (x : Fin (r + 2) → RationalAdele), Phi (h.1.1.1.1.mulVec x) = Phi x)
    (hfin : ∀ g : L.ConcreteFullAdelicSpecialOrthogonalGroup,
      L.concreteSpecialOrthogonalTheta Phi g ≠ ⊤) :
    L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta hr inst hcutoffProduct hconv Phi
        rationalIdeleClassUnitLogCutoff ≠ ⊤ :=
  L.cutoffNormalizedFullAdelicCliffordGeneralSpinTheta_unit_ne_top_of_thetaOnLeftQuotient_le
    hr inst hcutoffProduct hconv Phi (L.properThetaBound_ne_top inst hfin)
    (fun Z => L.fullAdelicCliffordGeneralSpinThetaOnLeftQuotient_le_properThetaBound
      hinv inst Z)

end PositiveDefiniteIntegralLattice

end

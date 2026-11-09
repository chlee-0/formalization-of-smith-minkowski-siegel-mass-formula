import SMSFormula.RationalCliffordSpinCandidateCanonicalMapIso

/-!
# Finite faithful flatness over the Spin involution invariants

The remaining effective-quotient problem compares the implemented `SO`
coordinate ring with the fixed subalgebra of the nontrivial central `mu_2`
action.  Over that fixed subalgebra itself, however, the trace automatically
descends.  This file applies the completed canonical tensor witness to prove
that the Spin-candidate coordinate ring is finite projective and faithfully
flat over its fixed subalgebra.

This isolates the genuine missing statement: surjectivity of
`specialOrthogonalToNegOneInvariantAlgHom`.  No equality between the
implemented `SO` coordinate ring and the invariant subalgebra is inferred
here.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

open RationalTamagawa

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

private abbrev Inv := V.negOneInvariantSubalgebra
private abbrev SpinCoord := V.cliffordSpinCandidateCoordinateRing

/-- The nontrivial scalar action, now regarded as an algebra endomorphism over
its literal fixed subalgebra. -/
def cliffordSpinCandidateNegOneInvariantCoordinateAlgHom :
    V.SpinCoord →ₐ[V.Inv] V.SpinCoord where
  toFun := V.cliffordSpinCandidateNegOneCoordinateAlgEquiv
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := V.cliffordSpinCandidateNegOneCoordinateAlgEquiv.map_add
  commutes' c := c.2

theorem cliffordSpinCandidateNegOneInvariantCoordinateAlgHom_comp_self :
    V.cliffordSpinCandidateNegOneInvariantCoordinateAlgHom.comp
        V.cliffordSpinCandidateNegOneInvariantCoordinateAlgHom =
      AlgHom.id V.Inv V.SpinCoord := by
  ext b
  exact DFunLike.congr_fun
    V.cliffordSpinCandidateNegOneCoordinateAlgHom_comp_self b

/-- The nontrivial scalar action as an involutive algebra automorphism over
its fixed subalgebra. -/
def cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv :
    V.SpinCoord ≃ₐ[V.Inv] V.SpinCoord :=
  AlgEquiv.ofAlgHom
    V.cliffordSpinCandidateNegOneInvariantCoordinateAlgHom
    V.cliffordSpinCandidateNegOneInvariantCoordinateAlgHom
    V.cliffordSpinCandidateNegOneInvariantCoordinateAlgHom_comp_self
    V.cliffordSpinCandidateNegOneInvariantCoordinateAlgHom_comp_self

/-- Over the fixed subalgebra, the involution trace has a tautological linear
lift. -/
def negOneTraceOverInvariantLinearMap : V.SpinCoord →ₗ[V.Inv] V.Inv where
  toFun b := ⟨b + V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv b,
    V.negOne_trace_invariant b⟩
  map_add' x y := by
    apply Subtype.ext
    change (x + y) +
        V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv (x + y) =
      (x + V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv x) +
        (y + V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv y)
    rw [map_add]
    abel
  map_smul' c b := by
    apply Subtype.ext
    change c.1 * b +
        V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv (c.1 * b) =
      c.1 * (b + V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv b)
    rw [map_mul]
    have hc : V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv
        (c : V.SpinCoord) = c := c.2
    rw [hc]
    ring

@[simp] theorem negOneTraceOverInvariantLinearMap_apply (b : V.SpinCoord) :
    ((negOneTraceOverInvariantLinearMap V) b).1 =
      b + V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv b := rfl

/-- The dual functional associated to one pure tensor in the completed
canonical witness. -/
noncomputable def negOneInvariantDualBasisFunctional
    (i : Fin V.canonicalRankTwoWitness.size) : V.SpinCoord →ₗ[V.Inv] V.Inv :=
  (negOneTraceOverInvariantLinearMap V).comp
    (LinearMap.mulLeft V.Inv (V.canonicalRankTwoWitness.right i))

/-- The canonical tensor witness and the invariant trace reconstruct every
Spin-coordinate element. -/
theorem negOneInvariant_dual_basis (b : V.SpinCoord) :
    ∑ i, ((V.negOneInvariantDualBasisFunctional i b : V.Inv) : V.SpinCoord) *
      V.canonicalRankTwoWitness.left i = b := by
  let W := V.canonicalRankTwoWitness
  let φ : Fin W.size → V.SpinCoord →ₗ[V.Inv] V.Inv := fun i =>
    (negOneTraceOverInvariantLinearMap V).comp
      (LinearMap.mulLeft V.Inv (W.right i))
  change ∑ i, ((φ i b : V.Inv) : V.SpinCoord) * W.left i = b
  simp_rw [φ, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    negOneTraceOverInvariantLinearMap_apply]
  calc
    ∑ i, (W.right i * b +
        V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv
          (W.right i * b)) * W.left i =
        ∑ i, (W.left i * W.right i * b + W.left i *
          V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv
            (W.right i) *
          V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv b) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul]
      ring
    _ = (∑ i, W.left i * W.right i) * b +
        (∑ i, W.left i *
          V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv
            (W.right i)) *
          V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv b := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
    _ = b := by
      have hzero : ∑ i, W.left i *
          V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv
            (W.right i) = 0 := W.canonical_zero
      rw [W.canonical_one, hzero]
      simp

/-- The Spin coordinate ring is finite over its nontrivial-involution fixed
subalgebra. -/
noncomputable def cliffordSpinCandidateModuleFiniteOverNegOneInvariant :
    Module.Finite V.Inv V.SpinCoord := by
  exact Module.finite_of_finite_dual_basis (R := V.Inv) (M := V.SpinCoord)
    V.canonicalRankTwoWitness.left
    V.negOneInvariantDualBasisFunctional (fun b => by
      simpa only [Algebra.smul_def] using V.negOneInvariant_dual_basis b)

/-- The Spin coordinate ring is projective over its nontrivial-involution
fixed subalgebra. -/
noncomputable def cliffordSpinCandidateModuleProjectiveOverNegOneInvariant :
    Module.Projective V.Inv V.SpinCoord := by
  exact Module.projective_of_finite_dual_basis (R := V.Inv) (M := V.SpinCoord)
    V.canonicalRankTwoWitness.left
    V.negOneInvariantDualBasisFunctional (fun b => by
      simpa only [Algebra.smul_def] using V.negOneInvariant_dual_basis b)

theorem negOneInvariantToCliffordSpinCandidateCoordinateRingHom_injective :
    Function.Injective (algebraMap V.Inv V.SpinCoord) :=
  Subtype.val_injective

/-- The fixed-subalgebra inclusion is finite. -/
theorem negOneInvariantToCliffordSpinCandidateCoordinateRingHom_finite :
    RingHom.Finite (A := V.Inv) (B := V.SpinCoord)
      (algebraMap V.Inv V.SpinCoord) := by
  rw [RingHom.finite_algebraMap]
  exact V.cliffordSpinCandidateModuleFiniteOverNegOneInvariant

/-- The Spin coordinate ring is faithfully flat over the literal fixed
subalgebra of the nontrivial central action. -/
theorem negOneInvariantToCliffordSpinCandidateCoordinateRingHom_faithfullyFlat :
    RingHom.FaithfullyFlat (R := V.Inv) (S := V.SpinCoord)
      (algebraMap V.Inv V.SpinCoord) := by
  let W := V.canonicalRankTwoWitness
  exact RingHom.faithfullyFlat_of_involution_torsor_witness
    V.cliffordSpinCandidateNegOneInvariantCoordinateAlgEquiv
    (negOneTraceOverInvariantLinearMap V)
    (negOneTraceOverInvariantLinearMap_apply V)
    W.left W.right W.canonical_one W.canonical_zero
    V.negOneInvariantToCliffordSpinCandidateCoordinateRingHom_injective

end RationalQuadraticSpaceMatrix

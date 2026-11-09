import SMSFormula.RationalCliffordSpinCandidatePointTopology
import SMSFormula.RationalCliffordSpinCandidateCoordinateHopf
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Topological-group structure on Clifford--Spin candidate points

Every element of the finite-coordinate Spin-candidate coordinate ring is
represented by a multivariate polynomial in the Clifford and matrix
coordinates.  Hence its evaluation on candidate points is continuous.  The
inverse point is evaluation after the already constructed coordinate
antipode, so inversion is continuous without choosing a matrix inverse
formula separately.
-/

noncomputable section

open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The values of all polynomial variables at a candidate point. -/
def cliffordSpinCandidatePointVariableMap
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : V.CliffordSpinCandidateGroup A) :
    (Finset (Fin n) ⊕ (Fin n × Fin n)) → A
  | Sum.inl s => x (V.cliffordSpinCandidateCliffordCoordinate s)
  | Sum.inr (i, j) => x (V.cliffordSpinCandidateMatrixCoordinate i j)

/-- The full polynomial-variable assignment varies continuously with a
candidate point. -/
theorem continuous_cliffordSpinCandidatePointVariableMap
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] :
    Continuous (V.cliffordSpinCandidatePointVariableMap A) := by
  rw [continuous_pi_iff]
  intro z
  rcases z with s | ij
  · exact V.continuous_cliffordSpinCandidateCliffordCoordinate A s
  · exact V.continuous_cliffordSpinCandidateMatrixCoordinate A ij.1 ij.2

/-- Evaluation of a polynomial representative is ordinary multivariate
polynomial evaluation in the finite point coordinates. -/
theorem cliffordSpinCandidate_apply_quotient_mk
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : V.CliffordSpinCandidateGroup A)
    (p : cliffordSpinCandidatePolynomialRing n) :
    x (Ideal.Quotient.mk V.cliffordSpinCandidateRelationIdeal p) =
      MvPolynomial.eval (V.cliffordSpinCandidatePointVariableMap A x)
        (p.map (algebraMap ℚ A)) := by
  change (x.comp (Ideal.Quotient.mkₐ ℚ
    V.cliffordSpinCandidateRelationIdeal)) p = _
  rw [V.cliffordSpinCandidateCoordinateAlgHom_comp_mk]
  simp only [cliffordSpinCandidateBaseChangeEvaluation,
    MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  apply congrArg (fun g => MvPolynomial.eval g (p.map (algebraMap ℚ A)))
  funext z
  rcases z with s | ij
  · exact V.cliffordSpinCandidateElementOfCoordinateAlgHom_repr A x s
  · rfl

/-- Evaluation at any element of the candidate coordinate ring is continuous
for the finite-coordinate topology. -/
theorem continuous_cliffordSpinCandidate_apply
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (a : V.cliffordSpinCandidateCoordinateRing) :
    Continuous (fun x : V.CliffordSpinCandidateGroup A => x a) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp_rw [V.cliffordSpinCandidate_apply_quotient_mk A]
  exact (MvPolynomial.continuous_eval (p.map (algebraMap ℚ A))).comp
    (V.continuous_cliffordSpinCandidatePointVariableMap A)

/-- Point-group inversion is coordinate precomposition with the affine-group
antipode. -/
theorem cliffordSpinCandidate_inv_eq_comp_antipode
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : V.CliffordSpinCandidateGroup A) :
    x⁻¹ = x.comp V.cliffordSpinCandidateCoordinateAntipode := by
  have h := map_inv
    (V.cliffordSpinCandidateCoordinateAlgHomMap
      V.cliffordSpinCandidateCoordinateRing x)
    (AlgHom.id ℚ
    V.cliffordSpinCandidateCoordinateRing)
  change x.comp ((AlgHom.id ℚ
      V.cliffordSpinCandidateCoordinateRing)⁻¹) = x⁻¹ at h
  exact h.symm

/-- Inversion is continuous for the finite-coordinate topology. -/
theorem continuous_inv_cliffordSpinCandidateGroup
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun x : V.CliffordSpinCandidateGroup A => x⁻¹) := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply continuous_pi
    intro s
    change Continuous (fun x : V.CliffordSpinCandidateGroup A =>
      x⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s))
    simp_rw [V.cliffordSpinCandidate_inv_eq_comp_antipode A]
    exact V.continuous_cliffordSpinCandidate_apply A
      (V.cliffordSpinCandidateCoordinateAntipode
        (V.cliffordSpinCandidateCliffordCoordinate s))
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun x : V.CliffordSpinCandidateGroup A =>
      x⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j))
    simp_rw [V.cliffordSpinCandidate_inv_eq_comp_antipode A]
    exact V.continuous_cliffordSpinCandidate_apply A
      (V.cliffordSpinCandidateCoordinateAntipode
        (V.cliffordSpinCandidateMatrixCoordinate i j))

/-- The natural finite-coordinate topology makes the candidate point group a
topological group. -/
noncomputable instance cliffordSpinCandidateGroupIsTopologicalGroup
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    IsTopologicalGroup (V.CliffordSpinCandidateGroup A) where
  continuous_mul := V.continuous_mul_cliffordSpinCandidateGroup A
  continuous_inv := V.continuous_inv_cliffordSpinCandidateGroup A

/-- The candidate-to-special-orthogonal homomorphism is continuous for the
finite-coordinate topology and the inherited matrix-subgroup topology. -/
theorem continuous_cliffordSpinCandidateGroupToSpecialOrthogonal
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (V.cliffordSpinCandidateGroupToSpecialOrthogonal A) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  let g : V.CliffordSpinCandidateGroup A →* GL (Fin n) A :=
    (Subgroup.subtype
      (PositiveDefiniteIntegralLattice.formPreservingMatrixSubgroup
        (V.specialOrthogonalMappedFormMatrix A))).comp
      ((Subgroup.subtype
        (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
          (V.specialOrthogonalMappedFormMatrix A))).comp
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal A))
  change Continuous g
  apply Continuous.of_coeHom_comp
  change Continuous (fun x : V.CliffordSpinCandidateGroup A => (g x).1)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simpa [g, cliffordSpinCandidateGroupToSpecialOrthogonal,
    cliffordSpinCandidateMatrixOfCoordinateAlgHom] using
      V.continuous_cliffordSpinCandidateMatrixCoordinate A i j

end RationalQuadraticSpaceMatrix

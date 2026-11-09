import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicAdmissiblePrincipalBlockTopology
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Local compactness precursor for Clifford--Spin candidate points

The finite coordinate realization of the Clifford--Spin candidate is the
zero locus of its explicit polynomial relation set.  Over a Hausdorff
topological rational ring this makes the coordinate map a closed embedding.

Over a p-adic field the ambient finite coordinate space is locally compact,
so the local candidate group is locally compact.  Requiring all coordinates
of a point and its inverse to lie in the p-adic integer ring cuts out a closed
subset of the compact integral coordinate box; hence the local integral
factor is compact.

No restricted-product compactness or measure is constructed here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 800000

/-! ## The closed finite-coordinate realization -/

/-- The value assigned to every polynomial variable by a candidate finite
coordinate tuple. -/
def cliffordSpinCandidateCoordinateVariableValue
    (_V : RationalQuadraticSpaceMatrix n)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (Finset (Fin n) → A) × Matrix (Fin n) (Fin n) A) :
    (Finset (Fin n) ⊕ Fin n × Fin n) → A
  | Sum.inl s => z.1 s
  | Sum.inr (i, j) => z.2 i j

/-- Evaluation of the candidate polynomial presentation at a finite
coordinate tuple. -/
def cliffordSpinCandidateCoordinateEvaluation
    (V : RationalQuadraticSpaceMatrix n)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (Finset (Fin n) → A) × Matrix (Fin n) (Fin n) A) :
    cliffordSpinCandidatePolynomialRing n →ₐ[ℚ] A :=
  MvPolynomial.aeval (V.cliffordSpinCandidateCoordinateVariableValue A z)

@[simp]
theorem cliffordSpinCandidateCoordinateEvaluation_cliffordVariable
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (Finset (Fin n) → A) × Matrix (Fin n) (Fin n) A)
    (s : Finset (Fin n)) :
    V.cliffordSpinCandidateCoordinateEvaluation A z
        (cliffordSpinVariable (n := n) s) = z.1 s := by
  simp [cliffordSpinCandidateCoordinateEvaluation,
    cliffordSpinCandidateCoordinateVariableValue, cliffordSpinVariable]

@[simp]
theorem cliffordSpinCandidateCoordinateEvaluation_matrixVariable
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (Finset (Fin n) → A) × Matrix (Fin n) (Fin n) A)
    (i j : Fin n) :
    V.cliffordSpinCandidateCoordinateEvaluation A z
        (cliffordSpinMatrixVariable (n := n) i j) = z.2 i j := by
  simp [cliffordSpinCandidateCoordinateEvaluation,
    cliffordSpinCandidateCoordinateVariableValue,
    cliffordSpinMatrixVariable]

/-- Polynomial evaluation at a finite coordinate tuple agrees with the
coordinate-ring point before passing to the quotient. -/
theorem cliffordSpinCandidateCoordinateEvaluation_coordinateMap
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : V.CliffordSpinCandidateGroup A) :
    V.cliffordSpinCandidateCoordinateEvaluation A
        (V.cliffordSpinCandidatePointCoordinateMap A x) =
      x.comp (Ideal.Quotient.mkₐ ℚ V.cliffordSpinCandidateRelationIdeal) := by
  apply MvPolynomial.algHom_ext
  intro z
  rcases z with s | ij
  · rw [show MvPolynomial.X (Sum.inl s) =
        cliffordSpinVariable (n := n) s by rfl,
      V.cliffordSpinCandidateCoordinateEvaluation_cliffordVariable]
    rfl
  · rcases ij with ⟨i, j⟩
    rw [show MvPolynomial.X (Sum.inr (i, j)) =
        cliffordSpinMatrixVariable (n := n) i j by rfl,
      V.cliffordSpinCandidateCoordinateEvaluation_matrixVariable]
    rfl

/-- The image of the finite coordinate map is exactly the common zero locus
of the explicit relation generators. -/
theorem range_cliffordSpinCandidatePointCoordinateMap
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Set.range (V.cliffordSpinCandidatePointCoordinateMap A) =
      {z | ∀ p ∈ V.cliffordSpinCandidateRelationSet,
        V.cliffordSpinCandidateCoordinateEvaluation A z p = 0} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩ p hp
    rw [V.cliffordSpinCandidateCoordinateEvaluation_coordinateMap]
    change x (Ideal.Quotient.mk V.cliffordSpinCandidateRelationIdeal p) = 0
    have hpzero :
        Ideal.Quotient.mk V.cliffordSpinCandidateRelationIdeal p = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hp)
    rw [hpzero, map_zero]
  · intro hz
    have hker : V.cliffordSpinCandidateRelationIdeal ≤
        RingHom.ker
          (V.cliffordSpinCandidateCoordinateEvaluation A z).toRingHom := by
      rw [cliffordSpinCandidateRelationIdeal]
      exact Ideal.span_le.2 hz
    let x : V.CliffordSpinCandidateGroup A :=
      Ideal.Quotient.liftₐ V.cliffordSpinCandidateRelationIdeal
        (V.cliffordSpinCandidateCoordinateEvaluation A z) hker
    have hxcomp :
        x.comp (Ideal.Quotient.mkₐ ℚ V.cliffordSpinCandidateRelationIdeal) =
          V.cliffordSpinCandidateCoordinateEvaluation A z := by
      exact Ideal.Quotient.liftₐ_comp
        V.cliffordSpinCandidateRelationIdeal
        (V.cliffordSpinCandidateCoordinateEvaluation A z) hker
    refine ⟨x, ?_⟩
    apply Prod.ext
    · funext s
      change (x.comp (Ideal.Quotient.mkₐ ℚ
        V.cliffordSpinCandidateRelationIdeal))
          (cliffordSpinVariable (n := n) s) = z.1 s
      rw [hxcomp,
        V.cliffordSpinCandidateCoordinateEvaluation_cliffordVariable]
    · ext i j
      change (x.comp (Ideal.Quotient.mkₐ ℚ
        V.cliffordSpinCandidateRelationIdeal))
          (cliffordSpinMatrixVariable (n := n) i j) = z.2 i j
      rw [hxcomp,
        V.cliffordSpinCandidateCoordinateEvaluation_matrixVariable]

/-- The assignment of all polynomial variables is continuous in the ambient
finite-coordinate topology. -/
theorem continuous_cliffordSpinCandidateCoordinateVariableValue
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] :
    Continuous (V.cliffordSpinCandidateCoordinateVariableValue A) := by
  apply continuous_pi
  intro z
  rcases z with s | ij
  · exact (continuous_apply s).comp continuous_fst
  · rcases ij with ⟨i, j⟩
    exact (continuous_apply j).comp
      ((continuous_apply i).comp continuous_snd)

/-- Every defining polynomial is a continuous function of the ambient finite
coordinates. -/
theorem continuous_cliffordSpinCandidateCoordinateEvaluation
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (p : cliffordSpinCandidatePolynomialRing n) :
    Continuous (fun z =>
      V.cliffordSpinCandidateCoordinateEvaluation A z p) := by
  simp only [cliffordSpinCandidateCoordinateEvaluation,
    MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  exact (MvPolynomial.continuous_eval
      (MvPolynomial.map (algebraMap ℚ A) p)).comp
    (V.continuous_cliffordSpinCandidateCoordinateVariableValue A)

/-- The finite-coordinate image of the candidate point group is closed. -/
theorem isClosed_range_cliffordSpinCandidatePointCoordinateMap
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] :
    IsClosed (Set.range (V.cliffordSpinCandidatePointCoordinateMap A)) := by
  rw [V.range_cliffordSpinCandidatePointCoordinateMap]
  rw [show
      {z : (Finset (Fin n) → A) × Matrix (Fin n) (Fin n) A |
        ∀ p ∈ V.cliffordSpinCandidateRelationSet,
          V.cliffordSpinCandidateCoordinateEvaluation A z p = 0} =
        ⋂ p, ⋂ (_hp : p ∈ V.cliffordSpinCandidateRelationSet),
          {z | V.cliffordSpinCandidateCoordinateEvaluation A z p = 0} by
      ext z
      simp]
  apply isClosed_iInter
  intro p
  apply isClosed_iInter
  intro hp
  exact isClosed_eq
    (V.continuous_cliffordSpinCandidateCoordinateEvaluation A p)
    continuous_const

/-- The candidate point coordinate map is a closed embedding over every
Hausdorff topological rational ring. -/
theorem cliffordSpinCandidatePointCoordinateMap_isClosedEmbedding
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] :
    Topology.IsClosedEmbedding
      (V.cliffordSpinCandidatePointCoordinateMap A) :=
  ⟨V.cliffordSpinCandidatePointCoordinateMap_isEmbedding A,
    V.isClosed_range_cliffordSpinCandidatePointCoordinateMap A⟩

/-! ## P-adic local compactness and integral-factor compactness -/

local instance cliffordSpinLocalCompactnessPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Every local p-adic Clifford--Spin candidate group is locally compact. -/
noncomputable instance heightOnePadicCliffordSpinCandidateGroupLocallyCompactSpace
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    LocallyCompactSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  letI : Fact (Nat.Prime p) :=
    cliffordSpinLocalCompactnessPrimeFact v
  letI : LocallyCompactSpace (Finset (Fin n) → ℚ_[p]) :=
    Pi.locallyCompactSpace_of_finite
  letI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℚ_[p]) :=
    Pi.locallyCompactSpace_of_finite
  change LocallyCompactSpace (V.CliffordSpinCandidateGroup ℚ_[p])
  exact
    (V.cliffordSpinCandidatePointCoordinateMap_isClosedEmbedding ℚ_[p])
      |>.locallyCompactSpace

/-- The height-one completion definition of local integrality is equivalent
to literal p-adic integer membership in every displayed coordinate. -/
theorem heightOnePadicCliffordSpinCandidateIsIntegral_iff_padic
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (g : V.HeightOnePadicCliffordSpinCandidateGroup v) :
    V.HeightOnePadicCliffordSpinCandidateIsIntegral v g ↔
      (∀ s, g (V.cliffordSpinCandidateCliffordCoordinate s) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
      (∀ i j, g (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
      (∀ s, g⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
      (∀ i j, g⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
        PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) := by
  unfold HeightOnePadicCliffordSpinCandidateIsIntegral
  constructor
  · rintro ⟨hc, hm, hci, hmi⟩
    refine ⟨fun s => ?_, fun i j => ?_, fun s => ?_, fun i j => ?_⟩
    · have h := (mem_adicCompletionIntegers_iff_padic v
          ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            (g (V.cliffordSpinCandidateCliffordCoordinate s)))).1 (hc s)
      rw [(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply] at h
      exact h
    · have h := (mem_adicCompletionIntegers_iff_padic v
          ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            (g (V.cliffordSpinCandidateMatrixCoordinate i j)))).1 (hm i j)
      rw [(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply] at h
      exact h
    · have h := (mem_adicCompletionIntegers_iff_padic v
          ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            (g⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s)))).1 (hci s)
      rw [(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply] at h
      exact h
    · have h := (mem_adicCompletionIntegers_iff_padic v
          ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            (g⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j)))).1 (hmi i j)
      rw [(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply] at h
      exact h
  · rintro ⟨hc, hm, hci, hmi⟩
    refine ⟨fun s => ?_, fun i j => ?_, fun s => ?_, fun i j => ?_⟩
    · apply (mem_adicCompletionIntegers_iff_padic v _).2
      rw [(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply]
      exact hc s
    · apply (mem_adicCompletionIntegers_iff_padic v _).2
      rw [(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply]
      exact hm i j
    · apply (mem_adicCompletionIntegers_iff_padic v _).2
      rw [(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply]
      exact hci s
    · apply (mem_adicCompletionIntegers_iff_padic v _).2
      rw [(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).apply_symm_apply]
      exact hmi i j

private theorem isClosed_heightOnePadicCliffordSpinCandidateIsIntegral
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    IsClosed
      {g : V.HeightOnePadicCliffordSpinCandidateGroup v |
        V.HeightOnePadicCliffordSpinCandidateIsIntegral v g} := by
  have hclosed : IsClosed
      (PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 :
        Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :=
    (show IsCompact
        (PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 :
          Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) by
      simpa only [isCompact_iff_compactSpace] using
        PadicInt.compactSpace (Rat.HeightOneSpectrum.primesEquiv v).1).isClosed
  rw [show
      {g : V.HeightOnePadicCliffordSpinCandidateGroup v |
        V.HeightOnePadicCliffordSpinCandidateIsIntegral v g} =
        {g |
          (∀ s, g (V.cliffordSpinCandidateCliffordCoordinate s) ∈
            PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
          (∀ i j, g (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
            PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
          (∀ s, g⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s) ∈
            PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
          (∀ i j, g⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
            PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)} by
      ext g
      exact V.heightOnePadicCliffordSpinCandidateIsIntegral_iff_padic v g]
  have hc : IsClosed
      {g : V.HeightOnePadicCliffordSpinCandidateGroup v |
        ∀ s, g (V.cliffordSpinCandidateCliffordCoordinate s) ∈
          PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun s => hclosed.preimage
      (V.continuous_cliffordSpinCandidateCliffordCoordinate
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s)
  have hm : IsClosed
      {g : V.HeightOnePadicCliffordSpinCandidateGroup v |
        ∀ i j, g (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
          PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1} := by
    rw [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    rw [Set.setOf_forall]
    exact isClosed_iInter fun j => hclosed.preimage
      (V.continuous_cliffordSpinCandidateMatrixCoordinate
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] i j)
  have hci : IsClosed
      {g : V.HeightOnePadicCliffordSpinCandidateGroup v |
        ∀ s, g⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s) ∈
          PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun s => hclosed.preimage
      ((V.continuous_cliffordSpinCandidateCliffordCoordinate
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s).comp continuous_inv)
  have hmi : IsClosed
      {g : V.HeightOnePadicCliffordSpinCandidateGroup v |
        ∀ i j, g⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
          PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1} := by
    rw [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    rw [Set.setOf_forall]
    exact isClosed_iInter fun j => hclosed.preimage
      ((V.continuous_cliffordSpinCandidateMatrixCoordinate
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] i j).comp continuous_inv)
  exact hc.inter (hm.inter (hci.inter hmi))

/-- The local integral-coordinate Clifford--Spin candidate locus is open. -/
theorem isOpen_heightOnePadicCliffordSpinCandidateIsIntegral
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    IsOpen
      {g : V.HeightOnePadicCliffordSpinCandidateGroup v |
        V.HeightOnePadicCliffordSpinCandidateIsIntegral v g} := by
  have hopen : IsOpen
      (PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 :
        Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) := by
    change IsOpen
      {x : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] | ‖x‖ ≤ 1}
    simpa [Metric.closedBall, dist_zero_right] using
      (IsUltrametricDist.isOpen_closedBall
        (x := (0 : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
        (r := 1) one_ne_zero)
  rw [show
      {g : V.HeightOnePadicCliffordSpinCandidateGroup v |
        V.HeightOnePadicCliffordSpinCandidateIsIntegral v g} =
        {g |
          (∀ s, g (V.cliffordSpinCandidateCliffordCoordinate s) ∈
            PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
          (∀ i j, g (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
            PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
          (∀ s, g⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s) ∈
            PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) ∧
          (∀ i j, g⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
            PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)} by
      ext g
      exact V.heightOnePadicCliffordSpinCandidateIsIntegral_iff_padic v g]
  have hc : IsOpen
      {g : V.HeightOnePadicCliffordSpinCandidateGroup v |
        ∀ s, g (V.cliffordSpinCandidateCliffordCoordinate s) ∈
          PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1} := by
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro s
    exact hopen.preimage
      (V.continuous_cliffordSpinCandidateCliffordCoordinate
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s)
  have hm : IsOpen
      {g : V.HeightOnePadicCliffordSpinCandidateGroup v |
        ∀ i j, g (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
          PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1} := by
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact hopen.preimage
      (V.continuous_cliffordSpinCandidateMatrixCoordinate
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] i j)
  have hci : IsOpen
      {g : V.HeightOnePadicCliffordSpinCandidateGroup v |
        ∀ s, g⁻¹ (V.cliffordSpinCandidateCliffordCoordinate s) ∈
          PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1} := by
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro s
    exact hopen.preimage
      ((V.continuous_cliffordSpinCandidateCliffordCoordinate
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s).comp continuous_inv)
  have hmi : IsOpen
      {g : V.HeightOnePadicCliffordSpinCandidateGroup v |
        ∀ i j, g⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
          PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1} := by
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact hopen.preimage
      ((V.continuous_cliffordSpinCandidateMatrixCoordinate
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] i j).comp continuous_inv)
  exact hc.inter (hm.inter (hci.inter hmi))

/-- The local integral-coordinate Clifford--Spin candidate locus is compact. -/
theorem isCompact_heightOnePadicCliffordSpinCandidateIsIntegral
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    IsCompact
      {g : V.HeightOnePadicCliffordSpinCandidateGroup v |
        V.HeightOnePadicCliffordSpinCandidateIsIntegral v g} := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  letI : Fact (Nat.Prime p) :=
    cliffordSpinLocalCompactnessPrimeFact v
  let K : Set ((Finset (Fin n) → ℚ_[p]) × Matrix (Fin n) (Fin n) ℚ_[p]) :=
    {z | (∀ s, z.1 s ∈ PadicInt.subring p) ∧
      ∀ i j, z.2 i j ∈ PadicInt.subring p}
  have hp : IsCompact (PadicInt.subring p : Set ℚ_[p]) := by
    simpa only [isCompact_iff_compactSpace] using PadicInt.compactSpace p
  have hK : IsCompact K := by
    have hclifford : IsCompact
        {c : Finset (Fin n) → ℚ_[p] | ∀ s, c s ∈ PadicInt.subring p} := by
      rw [show
          {c : Finset (Fin n) → ℚ_[p] | ∀ s, c s ∈ PadicInt.subring p} =
            Set.univ.pi fun _ => (PadicInt.subring p : Set ℚ_[p]) by
          ext c
          simp]
      exact isCompact_univ_pi fun _ => hp
    have hmatrix : IsCompact
        {M : Matrix (Fin n) (Fin n) ℚ_[p] |
          ∀ i j, M i j ∈ PadicInt.subring p} := by
      rw [show
          {M : Matrix (Fin n) (Fin n) ℚ_[p] |
            ∀ i j, M i j ∈ PadicInt.subring p} =
            Set.univ.pi fun _ => Set.univ.pi fun _ =>
              (PadicInt.subring p : Set ℚ_[p]) by
          ext M
          constructor
          · intro h i _hi j _hj
            exact h i j
          · intro h i j
            exact h i (Set.mem_univ i) j (Set.mem_univ j)]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hp
    exact hclifford.prod hmatrix
  have hpreimage : IsCompact
      ((V.cliffordSpinCandidatePointCoordinateMap ℚ_[p]) ⁻¹' K) :=
    (V.cliffordSpinCandidatePointCoordinateMap_isClosedEmbedding ℚ_[p])
      |>.isCompact_preimage hK
  apply IsCompact.of_isClosed_subset hpreimage
    (V.isClosed_heightOnePadicCliffordSpinCandidateIsIntegral v)
  intro g hg
  change
    (∀ s, g (V.cliffordSpinCandidateCliffordCoordinate s) ∈
      PadicInt.subring p) ∧
      ∀ i j, g (V.cliffordSpinCandidateMatrixCoordinate i j) ∈
        PadicInt.subring p
  exact
    ⟨(V.heightOnePadicCliffordSpinCandidateIsIntegral_iff_padic v g).1 hg |>.1,
      (V.heightOnePadicCliffordSpinCandidateIsIntegral_iff_padic v g).1 hg |>.2.1⟩

/-! ## Compact-open good local factors -/

/-- Away from the normalized exceptional set, the displayed local-factor
subgroup has exactly the integral-coordinate carrier. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor_carrier_eq_integral
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
        S v : Set (V.HeightOnePadicCliffordSpinCandidateGroup v)) =
      {g | V.HeightOnePadicCliffordSpinCandidateIsIntegral v g} := by
  ext g
  simp [hv]

/-- Every nonexceptional local factor in an admissible principal block is
compact. -/
theorem
    isCompact_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    IsCompact
      (V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
        S v : Set (V.HeightOnePadicCliffordSpinCandidateGroup v)) := by
  rw [V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor_carrier_eq_integral
    S v hv]
  exact V.isCompact_heightOnePadicCliffordSpinCandidateIsIntegral v

/-- Every nonexceptional local factor in an admissible principal block is
open. -/
theorem
    isOpen_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    IsOpen
      (V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
        S v : Set (V.HeightOnePadicCliffordSpinCandidateGroup v)) := by
  rw [V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor_carrier_eq_integral
    S v hv]
  exact V.isOpen_heightOnePadicCliffordSpinCandidateIsIntegral v

/-- A nonexceptional admissible local factor carries its compact subtype
topology. -/
noncomputable def
    finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorCompactSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) :
    CompactSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) :=
  isCompact_iff_compactSpace.mp
    (V.isCompact_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
      S v hv)

/- The exceptional local factors are full locally compact p-adic groups,
while the nonexceptional factors are compact. -/
noncomputable instance
    finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorLocallyCompactSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    LocallyCompactSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
        S v) := by
  by_cases hv : v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S
  · change LocallyCompactSpace
      ↥(V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup
        S v)
    rw [V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorSubgroup_eq_top
      S v hv]
    exact isOpen_univ.locallyCompactSpace
  · letI : CompactSpace
        (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
          S v) :=
      V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorCompactSpace
        S v hv
    infer_instance

end RationalQuadraticSpaceMatrix

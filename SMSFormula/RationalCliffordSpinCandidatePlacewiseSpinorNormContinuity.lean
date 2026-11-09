import SMSFormula.RationalCliffordSpinCandidateSpinorNormKernel
import SMSFormula.RationalCliffordSpinCandidatePlacewiseImageOpennessPrecursor
import SMSFormula.RationalTernaryHasseMinkowski
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Compactness.Lindelof

/-!
# Continuity of the real and p-adic spinor norms

The local square subgroups are open: this follows directly from the existing
real and p-adic open-square-orbit lemmas.  Their quotient square-class groups
are therefore discrete and countable.

Continuity of the special-orthogonal spinor norm is proved without assuming
that its kernel is open.  A generic Haar--Steinhaus argument shows that a
sigma-compact subgroup of a second-countable locally compact group is open
whenever it is the kernel of a homomorphism to a countable group.  Indeed the
subgroup is measurable, its countably many fibers cover the target, and hence
it has positive Haar measure; Steinhaus then supplies an identity
neighborhood inside it.  Applying the completed identification of the
spinor-norm kernel with the Spin-candidate image proves that the local point
maps are open and local homeomorphisms.

No pointwise surjectivity, local differential measure, adelic normalization,
condition (K), Ono comparison, or Tamagawa-volume statement is asserted.
-/

noncomputable section

open scoped Pointwise Topology

namespace Rat

/-- The subgroup of squares in the real unit group is open. -/
theorem isOpen_square_real_units :
    IsOpen (Subgroup.square ℝˣ : Set ℝˣ) := by
  obtain ⟨U, hUopen, hUone, hU⟩ :=
    exists_isOpen_mem_subset_real_nonzeroSqOrbit (c := (1 : ℝ)) one_ne_zero
  apply (Subgroup.square ℝˣ).isOpen_of_mem_nhds (g := 1)
  refine Filter.mem_of_superset
    (Units.continuous_val.continuousAt (by simpa using hUopen.mem_nhds hUone)) ?_
  intro x hx
  obtain ⟨s, hs0, hs⟩ := hU hx
  change x ∈ Subgroup.square ℝˣ
  rw [Subgroup.mem_square]
  refine ⟨Units.mk0 s hs0, ?_⟩
  apply Units.ext
  simpa [pow_two] using hs

/-- The subgroup of squares in a p-adic unit group is open. -/
theorem isOpen_square_padic_units (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen (Subgroup.square ℚ_[p]ˣ : Set ℚ_[p]ˣ) := by
  obtain ⟨U, hUopen, hUone, hU⟩ :=
    exists_isOpen_mem_subset_padic_nonzeroSqOrbit
      (p := p) (c := (1 : ℚ_[p])) one_ne_zero
  apply (Subgroup.square ℚ_[p]ˣ).isOpen_of_mem_nhds (g := 1)
  refine Filter.mem_of_superset
    (Units.continuous_val.continuousAt (by simpa using hUopen.mem_nhds hUone)) ?_
  intro x hx
  obtain ⟨s, hs0, hs⟩ := hU hx
  change x ∈ Subgroup.square ℚ_[p]ˣ
  rw [Subgroup.mem_square]
  refine ⟨Units.mk0 s hs0, ?_⟩
  apply Units.ext
  simpa [pow_two] using hs

/-- Real square classes have the quotient discrete topology. -/
noncomputable instance realSquareClassDiscreteTopology :
    DiscreteTopology (SquareClass ℝ) :=
  QuotientGroup.discreteTopology isOpen_square_real_units

/-- P-adic square classes have the quotient discrete topology. -/
noncomputable instance padicSquareClassDiscreteTopology
    (p : ℕ) [Fact (Nat.Prime p)] :
    DiscreteTopology (SquareClass ℚ_[p]) :=
  QuotientGroup.discreteTopology (isOpen_square_padic_units p)

/-- The real square-class group is countable. -/
noncomputable instance realSquareClassCountable : Countable (SquareClass ℝ) :=
  by
    letI : SecondCountableTopology ℝˣ :=
      Units.isEmbedding_val₀.secondCountableTopology
    letI : SecondCountableTopology (SquareClass ℝ) := inferInstance
    exact countable_of_Lindelof_of_discrete

/-- Every p-adic square-class group is countable. -/
noncomputable instance padicSquareClassCountable
    (p : ℕ) [Fact (Nat.Prime p)] : Countable (SquareClass ℚ_[p]) :=
  by
    letI : SecondCountableTopology ℚ_[p]ˣ :=
      Units.isEmbedding_val₀.secondCountableTopology
    letI : SecondCountableTopology (SquareClass ℚ_[p]) := inferInstance
    exact countable_of_Lindelof_of_discrete

end Rat

namespace MonoidHom

/-- A continuous image of a sigma-compact space into a Hausdorff Borel space
is measurable.  This small bridge is useful when the image is subsequently
treated as a subgroup carrying Haar measure. -/
theorem measurableSet_range_of_sigmaCompact
    {G H : Type*} [TopologicalSpace G] [SigmaCompactSpace G]
    [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (f : G → H) (hf : Continuous f) : MeasurableSet (Set.range f) := by
  have hsigma : IsSigmaCompact (Set.range f) := by
    rw [← Set.image_univ]
    exact isSigmaCompact_univ.image hf
  obtain ⟨K, hK, hKU⟩ := hsigma
  rw [← hKU]
  exact MeasurableSet.iUnion fun m ↦ (hK m).isClosed.measurableSet

/-- Haar--Steinhaus openness criterion for a countable obstruction.

No topology or continuity is required on `D`.  The kernel is assumed to be a
continuous sigma-compact image, hence is Borel measurable.  Its countably
many fibers cover `H`; left invariance forces the kernel to have positive
Haar measure, and Steinhaus makes it an identity neighborhood. -/
theorem isOpen_range_of_countable_obstruction
    {G H D : Type*} [Group G] [TopologicalSpace G] [SigmaCompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] [Group D] [Countable D]
    (f : G →* H) (hf : Continuous f) (delta : H →* D)
    (hker : delta.ker = f.range) : IsOpen (f.range : Set H) := by
  let μ : MeasureTheory.Measure H := MeasureTheory.Measure.haar
  have hmeas : MeasurableSet (delta.ker : Set H) := by
    rw [hker]
    change MeasurableSet (Set.range f)
    exact measurableSet_range_of_sigmaCompact f hf
  have hpos : 0 < μ (delta.ker : Set H) := by
    rw [pos_iff_ne_zero]
    intro hzero
    have hfiber : ∀ d : D, μ (delta ⁻¹' {d}) = 0 := by
      intro d
      by_cases hd : ∃ a : H, delta a = d
      · obtain ⟨a, rfl⟩ := hd
        have heq : delta ⁻¹' {delta a} = a • (delta.ker : Set H) := by
          ext x
          simp only [Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul,
            SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
          constructor
          · intro h
            simp [h]
          · intro h
            exact (inv_mul_eq_one.mp h).symm
        rw [heq, MeasureTheory.measure_smul]
        exact hzero
      · have heq : delta ⁻¹' {d} = (∅ : Set H) := by
          ext x
          constructor
          · intro hx
            exact (hd ⟨x, by simpa using hx⟩).elim
          · simp
        simp [heq]
    have hcover : (⋃ d : D, delta ⁻¹' {d}) = (Set.univ : Set H) := by
      ext x
      simp
    have hunivzero : μ (Set.univ : Set H) = 0 := by
      rw [← hcover]
      exact MeasureTheory.measure_iUnion_null hfiber
    exact (ne_of_gt (isOpen_univ.measure_pos μ Set.univ_nonempty)) hunivzero
  have hnhds : (delta.ker : Set H) / (delta.ker : Set H) ∈ nhds (1 : H) :=
    MeasureTheory.Measure.div_mem_nhds_one_of_haar_pos μ
      (delta.ker : Set H) hmeas hpos
  rw [coe_div_coe] at hnhds
  rw [← hker]
  exact delta.ker.isOpen_of_mem_nhds hnhds

/-- A homomorphism to a discrete group is continuous when its kernel is
open. Every nonempty fiber is a left translate of the kernel. -/
theorem continuous_of_discrete_of_isOpen_ker
    {H D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [Group D] [TopologicalSpace D] [DiscreteTopology D]
    (delta : H →* D) (hker : IsOpen (delta.ker : Set H)) :
    Continuous delta := by
  rw [continuous_discrete_rng]
  intro d
  by_cases hd : ∃ a : H, delta a = d
  · obtain ⟨a, rfl⟩ := hd
    have heq : delta ⁻¹' {delta a} = a • (delta.ker : Set H) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul,
        SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
      constructor
      · intro h
        simp [h]
      · intro h
        exact (inv_mul_eq_one.mp h).symm
    rw [heq]
    exact hker.smul a
  · have heq : delta ⁻¹' {d} = (∅ : Set H) := by
      ext x
      constructor
      · intro hx
        exact (hd ⟨x, by simpa using hx⟩).elim
      · simp
    simp [heq]

end MonoidHom

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## Borel and countability instances for the local targets -/

noncomputable instance realSpecialOrthogonalGroupMeasurableSpace_spinorNorm :
    MeasurableSpace V.RealSpecialOrthogonalGroup := borel _

noncomputable instance realSpecialOrthogonalGroupBorelSpace_spinorNorm :
    BorelSpace V.RealSpecialOrthogonalGroup := ⟨rfl⟩

noncomputable instance padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := borel _

noncomputable instance padicSpecialOrthogonalGroupBorelSpace_spinorNorm
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) := ⟨rfl⟩

noncomputable instance realSpecialOrthogonalGroupSecondCountable_spinorNorm :
    SecondCountableTopology V.RealSpecialOrthogonalGroup :=
  PositiveDefiniteIntegralLattice.specialFormPreservingRealGroup_secondCountable V.pairingMatrix

noncomputable instance padicSpecialOrthogonalGroupSecondCountable_spinorNorm
    (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_secondCountable
    V.pairingMatrix p

/-! ## Spin-image openness -/

/-- The real Spin-candidate image is open.  The proof uses countability of
real square classes and Haar--Steinhaus, not prior continuity of the spinor
norm. -/
theorem isOpen_realCliffordSpinCandidateImage :
    IsOpen (V.RealCliffordSpinCandidateImage :
      Set V.RealSpecialOrthogonalGroup) :=
  MonoidHom.isOpen_range_of_countable_obstruction
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℝ)
    V.realSpecialOrthogonalSpinorNormHom
    V.realSpecialOrthogonalSpinorNorm_ker_eq_cliffordSpinCandidate_range

/-- Every p-adic Spin-candidate image is open. -/
theorem isOpen_padicCliffordSpinCandidateImage
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen (V.PadicCliffordSpinCandidateImage p :
      Set (V.specialOrthogonalMatrixGroup ℚ_[p])) :=
  MonoidHom.isOpen_range_of_countable_obstruction
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.padicSpecialOrthogonalSpinorNormHom p)
    (V.padicSpecialOrthogonalSpinorNorm_ker_eq_cliffordSpinCandidate_range p)

/-! ## Spinor-norm continuity and local point-map charts -/

/-- The real special-orthogonal spinor norm is continuous for the quotient
discrete topology on real square classes. -/
theorem continuous_realSpecialOrthogonalSpinorNormHom :
    Continuous V.realSpecialOrthogonalSpinorNormHom := by
  apply MonoidHom.continuous_of_discrete_of_isOpen_ker
  rw [V.realSpecialOrthogonalSpinorNorm_ker_eq_cliffordSpinCandidate_range]
  exact V.isOpen_realCliffordSpinCandidateImage

/-- Every p-adic special-orthogonal spinor norm is continuous for the
quotient discrete topology on p-adic square classes. -/
theorem continuous_padicSpecialOrthogonalSpinorNormHom
    (p : ℕ) [Fact (Nat.Prime p)] :
    Continuous (V.padicSpecialOrthogonalSpinorNormHom p) := by
  apply MonoidHom.continuous_of_discrete_of_isOpen_ker
  rw [V.padicSpecialOrthogonalSpinorNorm_ker_eq_cliffordSpinCandidate_range]
  exact V.isOpen_padicCliffordSpinCandidateImage p

/-- The real Spin-candidate point map is open. -/
theorem realCliffordSpinCandidateToSpecialOrthogonal_isOpenMap :
    IsOpenMap V.realCliffordSpinCandidateToSpecialOrthogonalHom :=
  V.realCliffordSpinCandidateToSpecialOrthogonal_isOpenMap_iff_isOpen_image.2
    V.isOpen_realCliffordSpinCandidateImage

/-- Every p-adic Spin-candidate point map is open. -/
theorem padicCliffordSpinCandidateToSpecialOrthogonal_isOpenMap
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpenMap (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]) :=
  (V.padicCliffordSpinCandidateToSpecialOrthogonal_isOpenMap_iff_isOpen_image p).2
    (V.isOpen_padicCliffordSpinCandidateImage p)

/-- The real Spin-candidate point map is a local homeomorphism. -/
theorem realCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph :
    IsLocalHomeomorph V.realCliffordSpinCandidateToSpecialOrthogonalHom :=
  V.realCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_iff_isOpen_image.2
    V.isOpen_realCliffordSpinCandidateImage

/-- Every p-adic Spin-candidate point map is a local homeomorphism. -/
theorem padicCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocalHomeomorph
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]) :=
  (V.padicCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_iff_isOpen_image
      p).2 (V.isOpen_padicCliffordSpinCandidateImage p)

end RationalQuadraticSpaceMatrix

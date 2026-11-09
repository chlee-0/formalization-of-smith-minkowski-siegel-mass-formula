import SMSFormula.RationalCliffordSpinCandidateCanonicalMapIso
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import SMSFormula.RationalCliffordSpinCandidateFppf
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import SMSFormula.RationalCliffordSpinCandidateCoordinateHopf
import SMSFormula.RationalSpecialOrthogonalTamagawa
import Mathlib.Data.Matrix.DualNumber
import SMSFormula.RationalSpecialOrthogonalDifferentialNormalization
import SMSFormula.SpecialOrthogonalRealChartMeasure
import SMSFormula.PadicCayleyHomeomorph
import SMSFormula.PadicCayleyCoordinateJacobianDensityENNRealPositive
import SMSFormula.PadicCayleyDomainOpenness
import SMSFormula.SkewSymmetricPadicGeneralCongruenceCharacter
import SMSFormula.PadicCayleyLeftTrivializedInversePowerDeterminant
import SMSFormula.SkewAdjointPadicMeasureGeneralTransport
import SMSFormula.PadicCayleyLeftTrivializedInverseModulus
import SMSFormula.PadicCayleyTangentModulus
import SMSFormula.RationalCliffordSpinCandidateKernelMuTwo
import SMSFormula.RationalCliffordSpinCandidateTopologicalGroup
import SMSFormula.RationalCliffordSpinCandidateAdelicCarrier
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.IsLocalHomeomorph

/-!
# Placewise local-homeomorphism precursor for the Spin candidate

The real and p-adic Spin-candidate point maps have finite kernel because the
algebraic kernel calculation identifies it with `mu_2`. Finite
subsets of the Hausdorff point groups are discrete, and elementary
topological-group separation then makes each point map locally injective.

For a continuous group homomorphism with finite kernel, local injectivity
shows that the remaining condition for a local homeomorphism is exactly
openness. This reduces the local-homeomorphism property to openness, without
inferring an analytic inverse theorem from scheme-theoretic etaleness.
-/

noncomputable section

open scoped Pointwise Topology

namespace MonoidHom

/-- A homomorphism out of a topological group with finite kernel is locally
injective. -/
theorem isLocallyInjective_of_finite_ker
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T1Space G] [Group H] (f : G →* H) [Finite f.ker] :
    IsLocallyInjective f := by
  rw [isLocallyInjective_iff_nhds]
  have hfinite : (f.ker : Set G).Finite := Set.toFinite _
  have hdisc : IsDiscrete (f.ker : Set G) := hfinite.isDiscrete
  obtain ⟨U, hU, _hUinv, hdisj⟩ :=
    hdisc.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty f.ker
  intro x
  refine ⟨(fun y : G => y * x⁻¹) ⁻¹' U, ?_, ?_⟩
  · exact (continuous_mul_right x⁻¹).continuousAt.preimage_mem_nhds
      (by simpa using hU)
  · intro y hy z hz hyz
    let a : G := y * x⁻¹
    let b : G := z * x⁻¹
    let g : G := b * a⁻¹
    have hab : f a = f b := by simp [a, b, hyz]
    have hgker : g ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      simp [g, hab]
    have hinter : ((g * ·) '' U ∩ U).Nonempty := by
      refine ⟨b, ⟨a, hy, ?_⟩, hz⟩
      simp [g]
    have hg : g = 1 := hdisj g hgker hinter
    have hab' : b = a := by
      have := congrArg (fun t : G => t * a) hg
      simpa [g] using this
    dsimp [a, b] at hab'
    exact (mul_right_cancel hab').symm

/-- For a continuous group homomorphism with finite kernel, the exact
remaining local-homeomorphism condition is openness. -/
theorem isLocalHomeomorph_iff_isOpenMap_of_finite_ker
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T1Space G] [Group H] [TopologicalSpace H]
    (f : G →* H) [Finite f.ker] (hcont : Continuous f) :
    IsLocalHomeomorph f ↔ IsOpenMap f := by
  constructor
  · exact IsLocalHomeomorph.isOpenMap
  · intro hopen
    rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
    intro x
    obtain ⟨U, hUopen, hxU, hinj⟩ :=
      f.isLocallyInjective_of_finite_ker x
    refine ⟨U, hUopen.mem_nhds hxU, ?_⟩
    exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hcont.comp continuous_subtype_val)
      (Set.injOn_iff_injective.mp hinj)
      (hopen.comp hUopen.isOpenMap_subtype_val)

end MonoidHom

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The real Spin-candidate point-map kernel is finite. -/
noncomputable instance realCliffordSpinCandidateToSpecialOrthogonalKerFinite :
    Finite V.realCliffordSpinCandidateToSpecialOrthogonalHom.ker :=
  Finite.of_injective
    (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint ℝ).symm
    (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint ℝ).symm.injective

/-- The p-adic Spin-candidate point-map kernel is finite. -/
noncomputable instance padicCliffordSpinCandidateToSpecialOrthogonalKerFinite
    (p : ℕ) [Fact (Nat.Prime p)] :
    Finite (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).ker :=
  Finite.of_injective
    (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint ℚ_[p]).symm
    (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint ℚ_[p]).symm.injective

/-- The real Spin-candidate point-map kernel is a discrete subset of the
finite-coordinate point group. -/
theorem isDiscrete_realCliffordSpinCandidateToSpecialOrthogonalKer :
    IsDiscrete
      (V.realCliffordSpinCandidateToSpecialOrthogonalHom.ker :
        Set V.RealCliffordSpinCandidateGroup) := by
  letI hT2 : T2Space V.RealCliffordSpinCandidateGroup :=
    V.cliffordSpinCandidateGroupT2Space ℝ
  letI : T1Space V.RealCliffordSpinCandidateGroup :=
    @T2Space.t1Space _ _ hT2
  letI : Finite V.realCliffordSpinCandidateToSpecialOrthogonalHom.ker :=
    V.realCliffordSpinCandidateToSpecialOrthogonalKerFinite
  exact (Set.toFinite _).isDiscrete

/-- Every p-adic Spin-candidate point-map kernel is a discrete subset of the
finite-coordinate point group. -/
theorem isDiscrete_padicCliffordSpinCandidateToSpecialOrthogonalKer
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsDiscrete
      ((V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).ker :
        Set (V.PadicCliffordSpinCandidateGroup p)) := by
  letI hT2 : T2Space (V.PadicCliffordSpinCandidateGroup p) :=
    V.cliffordSpinCandidateGroupT2Space ℚ_[p]
  letI : T1Space (V.PadicCliffordSpinCandidateGroup p) :=
    @T2Space.t1Space _ _ hT2
  letI : Finite
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).ker :=
    V.padicCliffordSpinCandidateToSpecialOrthogonalKerFinite p
  exact (Set.toFinite _).isDiscrete

/-- The real Spin-candidate point map is locally injective. -/
theorem realCliffordSpinCandidateToSpecialOrthogonal_isLocallyInjective :
    IsLocallyInjective V.realCliffordSpinCandidateToSpecialOrthogonalHom := by
  letI hT2 : T2Space V.RealCliffordSpinCandidateGroup :=
    V.cliffordSpinCandidateGroupT2Space ℝ
  letI : T1Space V.RealCliffordSpinCandidateGroup :=
    @T2Space.t1Space _ _ hT2
  letI : Finite V.realCliffordSpinCandidateToSpecialOrthogonalHom.ker :=
    V.realCliffordSpinCandidateToSpecialOrthogonalKerFinite
  exact MonoidHom.isLocallyInjective_of_finite_ker
    V.realCliffordSpinCandidateToSpecialOrthogonalHom

/-- Every p-adic Spin-candidate point map is locally injective. -/
theorem padicCliffordSpinCandidateToSpecialOrthogonal_isLocallyInjective
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocallyInjective
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]) := by
  letI hT2 : T2Space (V.PadicCliffordSpinCandidateGroup p) :=
    V.cliffordSpinCandidateGroupT2Space ℚ_[p]
  letI : T1Space (V.PadicCliffordSpinCandidateGroup p) :=
    @T2Space.t1Space _ _ hT2
  letI : Finite
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).ker :=
    V.padicCliffordSpinCandidateToSpecialOrthogonalKerFinite p
  exact MonoidHom.isLocallyInjective_of_finite_ker
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])

/-- The real Spin-candidate point map is a local homeomorphism exactly when
it is open. -/
theorem realCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_iff_isOpenMap :
    IsLocalHomeomorph V.realCliffordSpinCandidateToSpecialOrthogonalHom ↔
      IsOpenMap V.realCliffordSpinCandidateToSpecialOrthogonalHom := by
  letI hT2 : T2Space V.RealCliffordSpinCandidateGroup :=
    V.cliffordSpinCandidateGroupT2Space ℝ
  letI : T1Space V.RealCliffordSpinCandidateGroup :=
    @T2Space.t1Space _ _ hT2
  letI : Finite V.realCliffordSpinCandidateToSpecialOrthogonalHom.ker :=
    V.realCliffordSpinCandidateToSpecialOrthogonalKerFinite
  exact MonoidHom.isLocalHomeomorph_iff_isOpenMap_of_finite_ker
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℝ)

/-- A p-adic Spin-candidate point map is a local homeomorphism exactly when
it is open. -/
theorem padicCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_iff_isOpenMap
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocalHomeomorph
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]) ↔
      IsOpenMap
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]) := by
  letI hT2 : T2Space (V.PadicCliffordSpinCandidateGroup p) :=
    V.cliffordSpinCandidateGroupT2Space ℚ_[p]
  letI : T1Space (V.PadicCliffordSpinCandidateGroup p) :=
    @T2Space.t1Space _ _ hT2
  letI : Finite
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).ker :=
    V.padicCliffordSpinCandidateToSpecialOrthogonalKerFinite p
  exact MonoidHom.isLocalHomeomorph_iff_isOpenMap_of_finite_ker
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])

/-- Openness of the real point map supplies an actual open partial
homeomorphism chart around the Spin identity whose underlying function is the
candidate-to-`SO` map. -/
theorem exists_realCliffordSpinCandidateToSpecialOrthogonal_identityOpenPartialHomeomorph
    (hopen : IsOpenMap V.realCliffordSpinCandidateToSpecialOrthogonalHom) :
    ∃ e : OpenPartialHomeomorph
        V.RealCliffordSpinCandidateGroup V.RealSpecialOrthogonalGroup,
      (1 : V.RealCliffordSpinCandidateGroup) ∈ e.source ∧
        (V.realCliffordSpinCandidateToSpecialOrthogonalHom :
          V.RealCliffordSpinCandidateGroup → V.RealSpecialOrthogonalGroup) = e :=
  (V.realCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_iff_isOpenMap.mpr
    hopen) 1

/-- Openness of a p-adic point map supplies an actual open partial
homeomorphism chart around the Spin identity whose underlying function is the
candidate-to-`SO` map. -/
theorem exists_padicCliffordSpinCandidateToSpecialOrthogonal_identityOpenPartialHomeomorph
    (p : ℕ) [Fact (Nat.Prime p)]
    (hopen : IsOpenMap
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])) :
    ∃ e : OpenPartialHomeomorph
        (V.PadicCliffordSpinCandidateGroup p)
        (V.specialOrthogonalMatrixGroup ℚ_[p]),
      (1 : V.PadicCliffordSpinCandidateGroup p) ∈ e.source ∧
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p] :
          V.PadicCliffordSpinCandidateGroup p →
            V.specialOrthogonalMatrixGroup ℚ_[p]) = e :=
  (V.padicCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_iff_isOpenMap
    p |>.mpr hopen) 1

end RationalQuadraticSpaceMatrix

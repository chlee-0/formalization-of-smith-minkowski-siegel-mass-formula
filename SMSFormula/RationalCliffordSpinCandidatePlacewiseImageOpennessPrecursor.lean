import SMSFormula.RationalCliffordSpinCandidatePlacewiseLocalHomeomorphPrecursor
import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicLocalCompactness
import SMSFormula.SpecialOrthogonalRealDifferentialHaar
import SMSFormula.PadicCayleyTranslatedChartDifferentialHaar
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Placewise image-openness precursor for the Spin candidate

Mathlib's topological-group open-mapping theorem shows that a continuous
homomorphism from a sigma-compact group is open onto any open locally compact
range. Applied to the real and p-adic Spin-candidate point maps, this reduces
the local-homeomorphism property from openness of the entire map to openness
of its image subgroup.

The file also records a spinor-norm criterion. If a continuous homomorphism
from the local special-orthogonal group to a discrete group has kernel equal
to the Spin image, that image is open and the point map is a local
homeomorphism. No such homomorphism is constructed here.
-/

noncomputable section

open scoped Topology

set_option synthInstance.maxHeartbeats 400000

namespace MonoidHom

/-- A continuous homomorphism from a sigma-compact topological group is open
as soon as its range is open in a locally compact Hausdorff target. The open
mapping theorem is applied to the surjective range restriction. -/
theorem isOpenMap_of_sigmaCompact_of_isOpen_range
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    (f : G →* H) (hcont : Continuous f)
    (hrange : IsOpen (f.range : Set H)) :
    IsOpenMap f := by
  let f' : G →* f.range := f.rangeRestrict
  have hcont' : Continuous f' := hcont.subtype_mk _
  letI : LocallyCompactSpace f.range :=
    hrange.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hopen' : IsOpenMap f' :=
    f'.isOpenMap_of_sigmaCompact f.rangeRestrict_surjective hcont'
  exact hrange.isOpenMap_subtype_val.comp hopen'

/-- For a continuous homomorphism from a sigma-compact group to a locally
compact Hausdorff group, openness of the map is exactly openness of its
range. -/
theorem isOpenMap_iff_isOpen_range_of_sigmaCompact
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    (f : G →* H) (hcont : Continuous f) :
    IsOpenMap f ↔ IsOpen (f.range : Set H) :=
  ⟨fun hopen => hopen.isOpen_range,
    fun hrange => f.isOpenMap_of_sigmaCompact_of_isOpen_range hcont hrange⟩

/-- A continuous homomorphism to a discrete group makes its kernel open. If
that kernel is the range of another homomorphism, the latter range is open. -/
theorem isOpen_range_of_continuous_discrete_obstruction
    {G H D : Type*} [Group G] [Group H] [TopologicalSpace H]
    [Group D] [TopologicalSpace D] [DiscreteTopology D]
    (f : G →* H) (delta : H →* D) (hdelta : Continuous delta)
    (hker : delta.ker = f.range) :
    IsOpen (f.range : Set H) := by
  rw [← hker]
  change IsOpen (delta ⁻¹' ({1} : Set D))
  exact hdelta.isOpen_preimage _ (isOpen_discrete _)

/-- A continuous discrete obstruction whose kernel is exactly the range,
together with the open mapping theorem onto that range, proves the original
homomorphism open. -/
theorem isOpenMap_of_continuous_discrete_obstruction
    {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    [Group D] [TopologicalSpace D] [DiscreteTopology D]
    (f : G →* H) (hcont : Continuous f) (delta : H →* D)
    (hdelta : Continuous delta) (hker : delta.ker = f.range) :
    IsOpenMap f :=
  f.isOpenMap_of_sigmaCompact_of_isOpen_range hcont
    (f.isOpen_range_of_continuous_discrete_obstruction delta hdelta hker)

end MonoidHom

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## Placewise countability and local compactness -/

/-- The real finite-coordinate Spin-candidate group is second countable. -/
noncomputable instance realCliffordSpinCandidateGroupSecondCountableTopology :
    SecondCountableTopology V.RealCliffordSpinCandidateGroup := by
  letI : SecondCountableTopology (Finset (Fin n) → ℝ) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact
    (V.cliffordSpinCandidatePointCoordinateMap_isEmbedding ℝ)
      |>.secondCountableTopology

/-- Every p-adic finite-coordinate Spin-candidate group is locally compact. -/
noncomputable instance padicCliffordSpinCandidateGroupLocallyCompactSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    LocallyCompactSpace (V.PadicCliffordSpinCandidateGroup p) := by
  letI : LocallyCompactSpace (Finset (Fin n) → ℚ_[p]) :=
    Pi.locallyCompactSpace_of_finite
  letI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℚ_[p]) :=
    Pi.locallyCompactSpace_of_finite
  exact
    (V.cliffordSpinCandidatePointCoordinateMap_isClosedEmbedding ℚ_[p])
      |>.locallyCompactSpace

/-- Every p-adic finite-coordinate Spin-candidate group is second
countable. -/
noncomputable instance padicCliffordSpinCandidateGroupSecondCountableTopology
    (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology (V.PadicCliffordSpinCandidateGroup p) := by
  letI : SecondCountableTopology (Finset (Fin n) → ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact
    (V.cliffordSpinCandidatePointCoordinateMap_isEmbedding ℚ_[p])
      |>.secondCountableTopology

/-- The real Spin-candidate group is sigma-compact. -/
noncomputable instance realCliffordSpinCandidateGroupSigmaCompactSpace :
    SigmaCompactSpace V.RealCliffordSpinCandidateGroup := by
  infer_instance

/-- Every p-adic Spin-candidate group is sigma-compact. -/
noncomputable instance padicCliffordSpinCandidateGroupSigmaCompactSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    SigmaCompactSpace (V.PadicCliffordSpinCandidateGroup p) := by
  infer_instance

/-- The real special-orthogonal target is locally compact through its exact
Cayley charts. -/
noncomputable instance realSpecialOrthogonalGroupLocallyCompactSpace :
    LocallyCompactSpace V.RealSpecialOrthogonalGroup :=
  PositiveDefiniteIntegralLattice.specialFormPreservingRealGroup_locallyCompact
    V.pairingMatrix V.form_symm V.form_det_ne_zero

/-- Every p-adic special-orthogonal target is locally compact through its
exact translated Cayley charts. -/
noncomputable instance padicSpecialOrthogonalGroupLocallyCompactSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    LocallyCompactSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalGroup_locallyCompact
    p n V.pairingMatrix V.form_det_ne_zero

/-! ## Spin images and exact openness criteria -/

/-- The image subgroup of the real Spin-candidate point map. -/
abbrev RealCliffordSpinCandidateImage : Subgroup V.RealSpecialOrthogonalGroup :=
  V.realCliffordSpinCandidateToSpecialOrthogonalHom.range

/-- The image subgroup of a p-adic Spin-candidate point map. -/
abbrev PadicCliffordSpinCandidateImage
    (p : ℕ) [Fact (Nat.Prime p)] :
    Subgroup (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).range

/-- The real point map is open exactly when its image subgroup is open. -/
theorem realCliffordSpinCandidateToSpecialOrthogonal_isOpenMap_iff_isOpen_image :
    IsOpenMap V.realCliffordSpinCandidateToSpecialOrthogonalHom ↔
      IsOpen (V.RealCliffordSpinCandidateImage :
        Set V.RealSpecialOrthogonalGroup) :=
  MonoidHom.isOpenMap_iff_isOpen_range_of_sigmaCompact
    V.realCliffordSpinCandidateToSpecialOrthogonalHom
    (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℝ)

/-- A p-adic point map is open exactly when its image subgroup is open. -/
theorem padicCliffordSpinCandidateToSpecialOrthogonal_isOpenMap_iff_isOpen_image
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpenMap (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]) ↔
      IsOpen (V.PadicCliffordSpinCandidateImage p :
        Set (V.specialOrthogonalMatrixGroup ℚ_[p])) :=
  MonoidHom.isOpenMap_iff_isOpen_range_of_sigmaCompact
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
    (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])

/-- The real point map is a local homeomorphism exactly when its image
subgroup is open. -/
theorem
    realCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_iff_isOpen_image :
    IsLocalHomeomorph V.realCliffordSpinCandidateToSpecialOrthogonalHom ↔
      IsOpen (V.RealCliffordSpinCandidateImage :
        Set V.RealSpecialOrthogonalGroup) :=
  V.realCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_iff_isOpenMap.trans
    V.realCliffordSpinCandidateToSpecialOrthogonal_isOpenMap_iff_isOpen_image

/-- A p-adic point map is a local homeomorphism exactly when its image
subgroup is open. -/
theorem
    padicCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_iff_isOpen_image
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocalHomeomorph
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]) ↔
      IsOpen (V.PadicCliffordSpinCandidateImage p :
        Set (V.specialOrthogonalMatrixGroup ℚ_[p])) :=
  (V.padicCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_iff_isOpenMap
      p).trans
    (V.padicCliffordSpinCandidateToSpecialOrthogonal_isOpenMap_iff_isOpen_image p)

/-! ## Prospective discrete spinor-norm interface -/

/-- Any continuous discrete-valued obstruction on the real `SO` group whose
kernel is exactly the Spin image proves that image open. -/
theorem isOpen_realCliffordSpinCandidateImage_of_discrete_obstruction
    {D : Type*} [Group D] [TopologicalSpace D] [DiscreteTopology D]
    (delta : V.RealSpecialOrthogonalGroup →* D) (hdelta : Continuous delta)
    (hker : delta.ker = V.RealCliffordSpinCandidateImage) :
    IsOpen (V.RealCliffordSpinCandidateImage :
      Set V.RealSpecialOrthogonalGroup) :=
  V.realCliffordSpinCandidateToSpecialOrthogonalHom
    |>.isOpen_range_of_continuous_discrete_obstruction delta hdelta hker

/-- Any continuous discrete-valued obstruction on a p-adic `SO` group whose
kernel is exactly the Spin image proves that image open. -/
theorem isOpen_padicCliffordSpinCandidateImage_of_discrete_obstruction
    (p : ℕ) [Fact (Nat.Prime p)]
    {D : Type*} [Group D] [TopologicalSpace D] [DiscreteTopology D]
    (delta : V.specialOrthogonalMatrixGroup ℚ_[p] →* D)
    (hdelta : Continuous delta)
    (hker : delta.ker = V.PadicCliffordSpinCandidateImage p) :
    IsOpen (V.PadicCliffordSpinCandidateImage p :
      Set (V.specialOrthogonalMatrixGroup ℚ_[p])) :=
  V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]
    |>.isOpen_range_of_continuous_discrete_obstruction delta hdelta hker

/-- A prospective continuous real spinor norm with discrete target and the
correct kernel supplies the actual local-homeomorphism theorem. -/
theorem
    realCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_of_discrete_obstruction
    {D : Type*} [Group D] [TopologicalSpace D] [DiscreteTopology D]
    (delta : V.RealSpecialOrthogonalGroup →* D) (hdelta : Continuous delta)
    (hker : delta.ker = V.RealCliffordSpinCandidateImage) :
    IsLocalHomeomorph V.realCliffordSpinCandidateToSpecialOrthogonalHom :=
  V.realCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_iff_isOpen_image.mpr
    (V.isOpen_realCliffordSpinCandidateImage_of_discrete_obstruction
      delta hdelta hker)

/-- A prospective continuous p-adic spinor norm with discrete target and the
correct kernel supplies the actual local-homeomorphism theorem. -/
theorem
    padicCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_of_discrete_obstruction
    (p : ℕ) [Fact (Nat.Prime p)]
    {D : Type*} [Group D] [TopologicalSpace D] [DiscreteTopology D]
    (delta : V.specialOrthogonalMatrixGroup ℚ_[p] →* D)
    (hdelta : Continuous delta)
    (hker : delta.ker = V.PadicCliffordSpinCandidateImage p) :
    IsLocalHomeomorph
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]) :=
  (V.padicCliffordSpinCandidateToSpecialOrthogonal_isLocalHomeomorph_iff_isOpen_image
      p).mpr
    (V.isOpen_padicCliffordSpinCandidateImage_of_discrete_obstruction
      p delta hdelta hker)

end RationalQuadraticSpaceMatrix

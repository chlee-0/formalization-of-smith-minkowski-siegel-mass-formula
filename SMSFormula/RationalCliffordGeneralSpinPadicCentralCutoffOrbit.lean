import SMSFormula.RationalCliffordGeneralSpinHorizontalPadicCentralCutoff
import SMSFormula.QuadraticPadicCayleyOrbitAction
import SMSFormula.RationalCliffordGeneralSpinBlockFieldShell

/-!
# The shell orbit of a p-adic central cutoff is the special-orthogonal orbit

A GSpin point acts on the final coordinate through its special-orthogonal image:
the shell orbit map sends `z` to `toSO(z) · x_old`.  For a supplied subgroup `U ≤ ℚ_p^×` and
a supplied `K ≤ SO(V)(ℚ_p)` whose points lift with similitude in `U`, the central cutoff
`{ν ∈ U, toSO ∈ K}` maps onto `K` under `toSO`, so its shell orbit is exactly the
special-orthogonal orbit `K · x_old`.  This is the same ambient set as the orbit
`range (γ ↦ γ • x_old)` of the Cayley stabilizer theorem, so the bad-place orbit test and
the local comparison refer to one orbit.  Nothing is chosen.
-/

noncomputable section

open Set Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) (p : ℕ) [Fact (Nat.Prime p)]

/-- The shell orbit of the central cutoff is the special-orthogonal orbit `K · x_old`. -/
theorem image_shellOrbit_centralFiber_preimage (U : Subgroup ℚ_[p]ˣ)
    (K : Subgroup ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p]))
    (hlift : ∀ g ∈ K, ∃ y : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint
        ℚ_[p], y.similitude ∈ U ∧
          CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g) :
    (fun z ↦ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha ℚ_[p] z).1) ''
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom (W.nonisotropicLastExtension a ha)
          ℚ_[p] ⁻¹' ((U : Set ℚ_[p]ˣ) ×ˢ (K : Set _))) =
      (fun g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p] ↦
        (g.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) *ᵥ lastCoordinateVector) '' (K : Set _) := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.matrixGroup, hz.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨y, hyU, hyg⟩ := hlift g hg
    have hyg' : y.matrixGroup = g := hyg
    refine ⟨y, ⟨hyU, ?_⟩, ?_⟩
    · change y.matrixGroup ∈ K
      rw [hyg']; exact hg
    · change (y.matrixGroup.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) *ᵥ lastCoordinateVector = _
      rw [hyg']

/-- The Cayley orbit of `K`, as an ambient set, is `K · x_old`. -/
theorem val_image_range_lastFiberSmul (K : Subgroup (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) :
    Subtype.val '' range (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha) =
      (fun g : PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
          ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ↦
        (g.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) *ᵥ lastCoordinateVector) '' (K : Set _) := by
  ext v
  constructor
  · rintro ⟨_, ⟨γ, rfl⟩, rfl⟩
    exact ⟨γ, γ.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩

end RationalQuadraticSpaceMatrix

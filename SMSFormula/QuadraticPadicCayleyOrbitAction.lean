import SMSFormula.QuadraticPadicCayleyStabilizerFiberMass
import SMSFormula.OrbitTranslatePartition

/-! The group action on the value {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} and the stabilizer of `x_old`. The
higher special form-preserving group acts on the fiber `{Q = a}` through the
isometries (`valueFiberMap`, i.e. matrix multiplication). The stabilizer of
`x_old = e_last` is exactly the range of the fixed-last-coordinate embedding
`ι`, and inside a subgroup `K` it is `(K ⊓ range ι).subgroupOf K`. Hence the
generic orbit partition counts `K · x_old` with the same index
`m = [K : K'(K ∩ H)]` that appears in the stabilizer volume identities: any
measure on the fiber giving every translate piece mass `c` gives `K · x_old`
mass `m · c`. No chart, section, baseline or measure is chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Set QuadraticMap
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]
variable (a : ℚ) (ha : a ≠ 0)

/-- The isometry of a group element acts by matrix multiplication. -/
theorem specialOrthogonalMatrixGroupIsometryEquiv_padic_apply
    (V : RationalQuadraticSpaceMatrix n) (g : V.specialOrthogonalMatrixGroup ℚ_[p])
    (x : Fin n → ℚ_[p]) :
    V.specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g x = g.1.1.1 *ᵥ x := by
  change Matrix.toLin' g.1.1.1 x = _
  rfl

/-- The action of the higher group on the value fiber `{Q = a}`. -/
instance lastFiberMulAction : MulAction (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} where
  smul g y := ⟨g.1.1.1 *ᵥ y.1, by
    rw [← W.nonisotropicLastExtension a ha |>.specialOrthogonalMatrixGroupIsometryEquiv_padic_apply p g,
      QuadraticMap.IsometryEquiv.map_app]
    exact y.2⟩
  one_smul y := Subtype.ext (by
    change ((1 : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) *ᵥ y.1 = y.1
    simp)
  mul_smul g h y := Subtype.ext (by
    change ((g * h).1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) *ᵥ y.1 =
      (g.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) *ᵥ ((h.1.1.1 : Matrix _ _ ℚ_[p]) *ᵥ y.1)
    rw [Matrix.mulVec_mulVec]
    rfl)

@[simp] theorem lastFiberMulAction_smul_val (g : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) (y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a}) :
    (g • y).1 = (g.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) *ᵥ y.1 := rfl

/-- The action is the `valueFiberMap` of the isometry. -/
theorem lastFiberMulAction_smul_eq_valueFiberMap (g : specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) (y : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a}) :
    g • y = ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g).valueFiberMap
      ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) (algebraMap ℚ ℚ_[p] a) y := by
  apply Subtype.ext
  change _ = (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroupIsometryEquiv ℚ_[p] g y.1
  rw [specialOrthogonalMatrixGroupIsometryEquiv_padic_apply]
  rfl

/-- The base point `x_old` of the value fiber. -/
def lastFiberBasePoint : {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a} :=
  ⟨lastCoordinateVector, W.nonisotropicLastExtension_quadratic_last a ha⟩

/-- The stabilizer of `x_old` is the lower group: it is the range of the
fixed-last-coordinate embedding. -/
theorem stabilizer_lastFiberBasePoint :
    MulAction.stabilizer (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) (W.lastFiberBasePoint p a ha) = (W.lastFiberEmbedHom p a ha).range := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MonoidHom.mem_range]
  constructor
  · intro hg
    have hfix : g ∈ W.nonisotropicLastCoordinateFiber a ha ℚ_[p] := by
      change (g.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) *ᵥ lastCoordinateVector = lastCoordinateVector
      exact congrArg Subtype.val hg
    exact ⟨W.nonisotropicLastCoordinateFiberExtract a ha ℚ_[p] ⟨g, hfix⟩,
      congrArg Subtype.val (W.nonisotropicLastCoordinateFiberEmbed_extract a ha ℚ_[p] ⟨g, hfix⟩)⟩
  · rintro ⟨h, rfl⟩
    apply Subtype.ext
    exact W.nonisotropicLastCoordinateFiberEmbedGroup_mem a ha ℚ_[p] h

/-- Inside a subgroup `K` the stabilizer of `x_old` is `(K ⊓ range ι).subgroupOf K`. -/
theorem stabilizer_subgroup_lastFiberBasePoint (K : Subgroup (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) :
    MulAction.stabilizer K (W.lastFiberBasePoint p a ha) =
      (K ⊓ (W.lastFiberEmbedHom p a ha).range).subgroupOf K := by
  ext x
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    ← W.stabilizer_lastFiberBasePoint p a ha, MulAction.mem_stabilizer_iff]
  exact ⟨fun h ↦ ⟨x.2, h⟩, fun h ↦ h.2⟩

/-- Orbit counting for `K · x_old`: for `K'` normal in `K` with finite orbit index
`m = [K : K'(K ∩ H)]`, every measure on the value fiber giving each translate
piece mass `c` gives the orbit `K · x_old` mass `m · c`. -/
theorem measure_lastFiberOrbit_eq_index_mul [MeasurableSpace {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a}]
    (K K' : Subgroup (specialFormPreservingMatrixSubgroup
      ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])))) [hN : (K'.subgroupOf K).Normal]
    (hm : ((K ⊓ (W.lastFiberEmbedHom p a ha).range).subgroupOf K ⊔ K'.subgroupOf K).index ≠ 0)
    (μ : Measure {y : Fin (n+1) → ℚ_[p] // (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y = algebraMap ℚ ℚ_[p] a})
    (hmeas : ∀ q, MeasurableSet
      (MulAction.normalOrbitTranslate (K'.subgroupOf K) (W.lastFiberBasePoint p a ha) q))
    {c : ℝ≥0∞}
    (hc : ∀ q, μ (MulAction.normalOrbitTranslate (K'.subgroupOf K) (W.lastFiberBasePoint p a ha) q) = c) :
    μ (range (fun γ : K ↦ γ • W.lastFiberBasePoint p a ha)) =
      (((K ⊓ (W.lastFiberEmbedHom p a ha).range).subgroupOf K ⊔ K'.subgroupOf K).index : ℝ≥0∞) * c := by
  have hidx : K'.subgroupOf K ⊔ MulAction.stabilizer K (W.lastFiberBasePoint p a ha) =
      (K ⊓ (W.lastFiberEmbedHom p a ha).range).subgroupOf K ⊔ K'.subgroupOf K := by
    rw [W.stabilizer_subgroup_lastFiberBasePoint p a ha K, sup_comm]
  haveI : (K'.subgroupOf K ⊔ MulAction.stabilizer K (W.lastFiberBasePoint p a ha)).FiniteIndex :=
    ⟨by rw [hidx]; exact hm⟩
  haveI : Finite (K ⧸ (K'.subgroupOf K ⊔ MulAction.stabilizer K (W.lastFiberBasePoint p a ha))) :=
    Subgroup.finite_quotient_of_finiteIndex
  rw [MulAction.measure_orbit_eq_index_mul (K'.subgroupOf K) (W.lastFiberBasePoint p a ha) μ hmeas hc,
    hidx]

end RationalQuadraticSpaceMatrix

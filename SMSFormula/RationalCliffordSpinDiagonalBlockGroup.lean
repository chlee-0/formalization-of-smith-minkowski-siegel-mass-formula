import SMSFormula.RationalCliffordSpinDiagonalBlockProduct
import SMSFormula.RationalCliffordSpinCandidateTopologicalGroup
import SMSFormula.RationalCliffordSpinCandidateAdelicCarrier

/-!
# The block Spin isomorphism on represented points

The intrinsic block Spin isomorphism `Φ` of `RationalCliffordSpinDiagonalBlockProduct` is
transported to the represented candidate groups `Spin(T)(A) × Spin(T)(A) ≃* Spin(U)(A)`,
`U = T ⊥ ⟨f₀f₁f₂⟩`, natural in the coefficient algebra.

Continuity is obtained by a Yoneda argument, not by a coordinate computation: naturality
writes `Φ(x, y) = (x ⊗ y) ∘ Φ(i₁, i₂)` for the universal pair on `R_T ⊗ R_T`, so every
coordinate of `Φ(x, y)` is a finite sum of products of coordinates of `x` and `y`.  Likewise
the inverse is `z ↦ z ∘ Ψ(id)`.  The rational diagonal subgroups correspond exactly.
-/

noncomputable section

open CliffordAlgebra Matrix PositiveDefiniteIntegralLattice
open scoped TensorProduct

namespace RationalQuadraticSpaceMatrix

section Group

variable (T : RationalQuadraticSpaceMatrix 3) {f : Fin 3 → ℚ} (hT : T.pairingMatrix = diagonal f)
  (hδ : f 0 * f 1 * f 2 ≠ 0)

/-- The represented block Spin isomorphism `Spin(T)(A) × Spin(T)(A) ≃* Spin(U)(A)`. -/
def diagonalBlockSpinGroupMulEquiv (A : Type*) [CommRing A] [Algebra ℚ A] :
    (T.CliffordSpinCandidateGroup A × T.CliffordSpinCandidateGroup A) ≃*
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinCandidateGroup A :=
  ((T.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A).prodCongr
      (T.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A)).trans
    ((T.diagonalBlockSpinMulEquiv hT hδ A).trans
      ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint
        A).symm)

theorem diagonalBlockSpinGroupMulEquiv_intrinsic (A : Type*) [CommRing A] [Algebra ℚ A]
    (p : T.CliffordSpinCandidateGroup A × T.CliffordSpinCandidateGroup A) :
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A
        (T.diagonalBlockSpinGroupMulEquiv hT hδ A p) =
      T.diagonalBlockSpinMulEquiv hT hδ A
        (T.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A p.1,
          T.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A p.2) :=
  MulEquiv.apply_symm_apply _ _

theorem cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint_comp {n : ℕ}
    (V : RationalQuadraticSpaceMatrix n) {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B]
    [Algebra ℚ B] (φ : A →ₐ[ℚ] B) (x : V.CliffordSpinCandidateGroup A) :
    V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint B (φ.comp x) =
      V.cliffordSpinIntrinsicPointMap φ (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A x) := by
  unfold cliffordSpinIntrinsicPointMap
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  rfl

/-- Naturality of the represented block isomorphism. -/
theorem diagonalBlockSpinGroupMulEquiv_comp {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B]
    [Algebra ℚ B] (φ : A →ₐ[ℚ] B) (x y : T.CliffordSpinCandidateGroup A) :
    T.diagonalBlockSpinGroupMulEquiv hT hδ B (φ.comp x, φ.comp y) =
      φ.comp (T.diagonalBlockSpinGroupMulEquiv hT hδ A (x, y)) := by
  apply ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint
    B).injective
  rw [T.diagonalBlockSpinGroupMulEquiv_intrinsic hT hδ B,
    cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint_comp _ φ
      (T.diagonalBlockSpinGroupMulEquiv hT hδ A (x, y)),
    T.diagonalBlockSpinGroupMulEquiv_intrinsic hT hδ A]
  dsimp only
  rw [cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint_comp T φ x,
    cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint_comp T φ y]
  exact (T.diagonalBlockSpinMulEquiv_naturality hT hδ φ
    (T.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A x,
      T.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A y)).symm

/-- Naturality of the inverse block isomorphism. -/
theorem diagonalBlockSpinGroupMulEquiv_symm_comp {A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B]
    [Algebra ℚ B] (φ : A →ₐ[ℚ] B)
    (z : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinCandidateGroup A) :
    (T.diagonalBlockSpinGroupMulEquiv hT hδ B).symm (φ.comp z) =
      (φ.comp ((T.diagonalBlockSpinGroupMulEquiv hT hδ A).symm z).1,
        φ.comp ((T.diagonalBlockSpinGroupMulEquiv hT hδ A).symm z).2) := by
  apply (T.diagonalBlockSpinGroupMulEquiv hT hδ B).injective
  rw [MulEquiv.apply_symm_apply, T.diagonalBlockSpinGroupMulEquiv_comp hT hδ φ]
  simp

/-! ## Continuity by Yoneda -/

section Topology

variable (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The universal pair on `R_T ⊗ R_T`. -/
abbrev diagonalBlockUniversalPair :
    T.CliffordSpinCandidateGroup (T.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
        T.cliffordSpinCandidateCoordinateRing) ×
      T.CliffordSpinCandidateGroup (T.cliffordSpinCandidateCoordinateRing ⊗[ℚ]
        T.cliffordSpinCandidateCoordinateRing) :=
  (Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight)

theorem diagonalBlockSpinGroupMulEquiv_eq_productMap (x y : T.CliffordSpinCandidateGroup A) :
    T.diagonalBlockSpinGroupMulEquiv hT hδ A (x, y) =
      (Algebra.TensorProduct.productMap x y).comp
        (T.diagonalBlockSpinGroupMulEquiv hT hδ _ T.diagonalBlockUniversalPair) := by
  have h := T.diagonalBlockSpinGroupMulEquiv_comp hT hδ (Algebra.TensorProduct.productMap x y)
    (T.diagonalBlockUniversalPair).1 (T.diagonalBlockUniversalPair).2
  rw [Algebra.TensorProduct.productMap_left, Algebra.TensorProduct.productMap_right] at h
  exact h

omit [IsTopologicalRing A] in
theorem continuous_productMap_apply {n : ℕ} (V : RationalQuadraticSpaceMatrix n) [IsTopologicalRing A]
    (w : V.cliffordSpinCandidateCoordinateRing ⊗[ℚ] V.cliffordSpinCandidateCoordinateRing) :
    Continuous fun p : V.CliffordSpinCandidateGroup A × V.CliffordSpinCandidateGroup A ↦
      Algebra.TensorProduct.productMap p.1 p.2 w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact continuous_const
  | tmul a b =>
    simp only [Algebra.TensorProduct.productMap_apply_tmul]
    exact ((V.continuous_cliffordSpinCandidate_apply A a).comp continuous_fst).mul
      ((V.continuous_cliffordSpinCandidate_apply A b).comp continuous_snd)
  | add w w' hw hw' => simp only [map_add]; exact hw.add hw'

/-- Every coordinate of `Φ(x, y)` is a coordinate of the universal block point. -/
theorem diagonalBlockSpinGroupMulEquiv_apply_eq (p : T.CliffordSpinCandidateGroup A × T.CliffordSpinCandidateGroup A)
    (a : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateCoordinateRing) :
    T.diagonalBlockSpinGroupMulEquiv hT hδ A p a =
      Algebra.TensorProduct.productMap p.1 p.2
        (T.diagonalBlockSpinGroupMulEquiv hT hδ _ T.diagonalBlockUniversalPair a) := by
  rw [show p = (p.1, p.2) from rfl, T.diagonalBlockSpinGroupMulEquiv_eq_productMap hT hδ A]
  rfl

theorem continuous_diagonalBlockSpinGroupMulEquiv :
    Continuous (T.diagonalBlockSpinGroupMulEquiv hT hδ A) := by
  rw [((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidatePointCoordinateMap_isEmbedding
    A).continuous_iff]
  have h : ∀ a, Continuous fun p ↦ T.diagonalBlockSpinGroupMulEquiv hT hδ A p a := fun a ↦ by
    simp_rw [T.diagonalBlockSpinGroupMulEquiv_apply_eq hT hδ A]
    exact continuous_productMap_apply A T _
  exact Continuous.prodMk (continuous_pi fun u ↦ h _)
    (continuous_pi fun i ↦ continuous_pi fun j ↦ h _)

/-- The universal point of `U` on `R_U ⊗ ℚ` (tensoring with `ℚ` avoids the endomorphism monoid
structure on `R_U →ₐ R_U`). -/
abbrev diagonalBlockUniversalTarget :
    (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinCandidateGroup
      ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateCoordinateRing ⊗[ℚ] ℚ) :=
  Algebra.TensorProduct.includeLeft

set_option backward.isDefEq.respectTransparency false in
@[reducible]
noncomputable local instance diagonalBlockUniversalTargetPointGroup :
    Group (T.CliffordSpinCandidateGroup
      ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateCoordinateRing ⊗[ℚ] ℚ)) :=
  T.cliffordSpinCandidateCoordinateAlgHomGroup
    ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateCoordinateRing ⊗[ℚ] ℚ)

set_option backward.isDefEq.respectTransparency false in
@[reducible]
noncomputable local instance diagonalBlockUniversalExtendedTargetPointGroup :
    Group ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinCandidateGroup
      ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateCoordinateRing ⊗[ℚ] ℚ)) :=
  (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateCoordinateAlgHomGroup
    ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateCoordinateRing ⊗[ℚ] ℚ)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse is precomposition with the inverse of the universal point. -/
theorem diagonalBlockSpinGroupMulEquiv_symm_apply_eq
    (z : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinCandidateGroup A) :
    (T.diagonalBlockSpinGroupMulEquiv hT hδ A).symm z =
      ((Algebra.TensorProduct.productMap z (Algebra.ofId ℚ A)).comp
          ((T.diagonalBlockSpinGroupMulEquiv hT hδ _).symm (T.diagonalBlockUniversalTarget hδ)).1,
        (Algebra.TensorProduct.productMap z (Algebra.ofId ℚ A)).comp
          ((T.diagonalBlockSpinGroupMulEquiv hT hδ _).symm (T.diagonalBlockUniversalTarget hδ)).2) := by
  have h := T.diagonalBlockSpinGroupMulEquiv_symm_comp hT hδ
    (Algebra.TensorProduct.productMap z (Algebra.ofId ℚ A)) (T.diagonalBlockUniversalTarget hδ)
  rwa [Algebra.TensorProduct.productMap_left] at h

omit [IsTopologicalRing A] in
theorem continuous_productMap_ofId_apply {n : ℕ} (V : RationalQuadraticSpaceMatrix n) [IsTopologicalRing A]
    (w : V.cliffordSpinCandidateCoordinateRing ⊗[ℚ] ℚ) :
    Continuous fun z : V.CliffordSpinCandidateGroup A ↦
      Algebra.TensorProduct.productMap z (Algebra.ofId ℚ A) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact continuous_const
  | tmul a b =>
    simp only [Algebra.TensorProduct.productMap_apply_tmul]
    exact (V.continuous_cliffordSpinCandidate_apply A a).mul continuous_const
  | add w w' hw hw' => simp only [map_add]; exact hw.add hw'

set_option backward.isDefEq.respectTransparency false in
theorem continuous_diagonalBlockSpinGroupMulEquiv_symm :
    Continuous (T.diagonalBlockSpinGroupMulEquiv hT hδ A).symm := by
  simp_rw [funext (T.diagonalBlockSpinGroupMulEquiv_symm_apply_eq hT hδ A)]
  have h : ∀ w : T.CliffordSpinCandidateGroup
      ((T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).cliffordSpinCandidateCoordinateRing ⊗[ℚ] ℚ),
      Continuous fun z : (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinCandidateGroup A ↦
        ((Algebra.TensorProduct.productMap z (Algebra.ofId ℚ A)).comp w : T.CliffordSpinCandidateGroup A) :=
    fun w ↦ by
      rw [(T.cliffordSpinCandidatePointCoordinateMap_isEmbedding A).continuous_iff]
      exact Continuous.prodMk
        (continuous_pi fun u ↦ continuous_productMap_ofId_apply A _ _)
        (continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_productMap_ofId_apply A _ _)
  exact (h _).prodMk (h _)

/-- The block Spin isomorphism as a topological group isomorphism. -/
def diagonalBlockSpinGroupContinuousMulEquiv :
    (T.CliffordSpinCandidateGroup A × T.CliffordSpinCandidateGroup A) ≃ₜ*
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).CliffordSpinCandidateGroup A :=
  ContinuousMulEquiv.mk'
    { toEquiv := (T.diagonalBlockSpinGroupMulEquiv hT hδ A).toEquiv
      continuous_toFun := T.continuous_diagonalBlockSpinGroupMulEquiv hT hδ A
      continuous_invFun := T.continuous_diagonalBlockSpinGroupMulEquiv_symm hT hδ A }
    (T.diagonalBlockSpinGroupMulEquiv hT hδ A).map_mul

@[simp]
theorem diagonalBlockSpinGroupContinuousMulEquiv_apply
    (p : T.CliffordSpinCandidateGroup A × T.CliffordSpinCandidateGroup A) :
    T.diagonalBlockSpinGroupContinuousMulEquiv hT hδ A p = T.diagonalBlockSpinGroupMulEquiv hT hδ A p :=
  rfl

end Topology

/-! ## Rational points -/

/-- The block isomorphism maps the product of the rational diagonal subgroups onto the rational
diagonal subgroup. -/
theorem diagonalBlockSpinGroup_diagonalSubgroup_map :
    (T.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup.prod
        T.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup).map
        (T.diagonalBlockSpinGroupMulEquiv hT hδ RationalAdele).toMonoidHom =
      (T.nonisotropicLastExtension (f 0 * f 1 * f 2) hδ).rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_prod, rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
    MonoidHom.mem_range, rationalCliffordSpinCandidateFullAdelicDiagonalHom, cliffordSpinCandidateGroupMap_apply,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨⟨x₀, rfl⟩, ⟨y₀, rfl⟩⟩, rfl⟩
    exact ⟨T.diagonalBlockSpinGroupMulEquiv hT hδ ℚ (x₀, y₀),
      (T.diagonalBlockSpinGroupMulEquiv_comp hT hδ _ x₀ y₀).symm⟩
  · rintro ⟨z₀, rfl⟩
    refine ⟨((Algebra.ofId ℚ RationalAdele).comp ((T.diagonalBlockSpinGroupMulEquiv hT hδ ℚ).symm z₀).1,
      (Algebra.ofId ℚ RationalAdele).comp ((T.diagonalBlockSpinGroupMulEquiv hT hδ ℚ).symm z₀).2),
      ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, ?_⟩
    rw [T.diagonalBlockSpinGroupMulEquiv_comp hT hδ, MulEquiv.apply_symm_apply]

end Group

end RationalQuadraticSpaceMatrix

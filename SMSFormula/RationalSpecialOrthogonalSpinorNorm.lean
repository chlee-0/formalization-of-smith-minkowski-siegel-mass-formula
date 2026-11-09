import SMSFormula.QuadraticDeterminantOneSpinorNorm
import SMSFormula.RationalCliffordSpinCandidateSurjectivity
import SMSFormula.RationalSpecialOrthogonalFullAdelicRealFiniteCarrier

/-!
# The spinor norm on concrete rational special-orthogonal groups

For every characteristic-zero rational field `K`, this file identifies the
repository's concrete matrix group `SO(V)(K)` with the determinant-one
self-isometry group of the scalar-extended quadratic form.  Transporting the
completed reflection-pair construction gives a genuine homomorphism

```text
SO(V)(K) -> K^x / K^(x2).
```

The construction is specialized to the real and standard p-adic carriers.
No continuity or theorem identifying its kernel with the Spin-candidate image
is asserted here.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

open QuadraticMap.ReflectionWord

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The concrete matrix action as a homomorphism to determinant-one quadratic
self-isometries. -/
def specialOrthogonalMatrixGroupDetOneIsometryHom
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K] :
    V.specialOrthogonalMatrixGroup K →*
      DetOneIsometryGroup (V.commutativeScalarExtensionQuadraticForm K) where
  toFun g := ⟨V.specialOrthogonalMatrixGroupIsometryEquiv K g, by
    apply Units.ext
    simp only [LinearEquiv.coe_det, Units.val_one]
    rw [← LinearMap.det_toMatrix',
      V.specialOrthogonalMatrixGroupIsometryEquiv_toMatrix']
    exact (PositiveDefiniteIntegralLattice.mem_specialFormPreservingMatrixSubgroup_iff
      (V.specialOrthogonalMappedFormMatrix K) g.1).1 g.2⟩
  map_one' := by
    apply Subtype.ext
    apply DFunLike.coe_injective
    funext x
    have hlin :
        (V.specialOrthogonalMatrixGroupIsometryEquiv K
          (1 : V.specialOrthogonalMatrixGroup K)).toLinearEquiv.toLinearMap =
          (QuadraticMap.IsometryEquiv.refl
            (V.commutativeScalarExtensionQuadraticForm K)).toLinearEquiv.toLinearMap := by
      apply (LinearMap.toMatrix' (R := K) (m := Fin n) (n := Fin n)).injective
      rw [V.specialOrthogonalMatrixGroupIsometryEquiv_toMatrix']
      ext i j
      classical
      by_cases hij : i = j <;>
        simp [LinearMap.toMatrix'_apply, QuadraticMap.IsometryEquiv.refl, hij]
    exact LinearMap.congr_fun hlin x
  map_mul' g h := by
    apply Subtype.ext
    apply DFunLike.coe_injective
    funext x
    have hlin :
        (V.specialOrthogonalMatrixGroupIsometryEquiv K (g * h)).toLinearEquiv.toLinearMap =
          (V.specialOrthogonalMatrixGroupIsometryEquiv K g).toLinearEquiv.toLinearMap.comp
            (V.specialOrthogonalMatrixGroupIsometryEquiv K h).toLinearEquiv.toLinearMap := by
      apply (LinearMap.toMatrix' (R := K) (m := Fin n) (n := Fin n)).injective
      rw [V.specialOrthogonalMatrixGroupIsometryEquiv_toMatrix',
        LinearMap.toMatrix'_comp,
        V.specialOrthogonalMatrixGroupIsometryEquiv_toMatrix',
        V.specialOrthogonalMatrixGroupIsometryEquiv_toMatrix']
      rfl
    change V.specialOrthogonalMatrixGroupIsometryEquiv K (g * h) x =
      V.specialOrthogonalMatrixGroupIsometryEquiv K g
        (V.specialOrthogonalMatrixGroupIsometryEquiv K h x)
    exact LinearMap.congr_fun hlin x

theorem commutativeScalarExtensionQuadraticForm_associated_nondegenerate
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K] :
    (V.commutativeScalarExtensionQuadraticForm K).associated.Nondegenerate := by
  simpa [commutativeScalarExtensionQuadraticForm,
    commutativeScalarExtensionFormMatrix,
    scalarExtensionQuadraticForm, scalarExtensionFormMatrix] using
    V.scalarExtensionQuadraticForm_associated_nondegenerate K

/-- The special-orthogonal matrix point underlying a determinant-one
self-isometry. -/
def detOneIsometrySpecialOrthogonalMatrixPoint
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (g : DetOneIsometryGroup
      (V.commutativeScalarExtensionQuadraticForm K)) :
    V.specialOrthogonalMatrixPoint K := by
  letI : Invertible (2 : K) := rationalAlgebraInvertibleTwo K
  let Q := V.commutativeScalarExtensionQuadraticForm K
  refine ⟨LinearMap.toMatrix' g.1.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · have hcomp : Q.comp g.1.toLinearEquiv.toLinearMap = Q := by
      apply QuadraticMap.ext
      intro m
      exact g.1.map_app m
    have hmatrix := congrArg QuadraticForm.toMatrix' hcomp
    rw [QuadraticForm.toMatrix'_comp] at hmatrix
    dsimp [Q] at hmatrix
    rw [V.commutativeScalarExtensionQuadraticForm_toMatrix' K] at hmatrix
    simpa [Q, specialOrthogonalMappedFormMatrix,
      commutativeScalarExtensionFormMatrix] using hmatrix
  · rw [LinearMap.det_toMatrix']
    exact detOneIsometryGroup_det Q g

noncomputable def detOneIsometrySpecialOrthogonalMatrixGroup
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (g : DetOneIsometryGroup
      (V.commutativeScalarExtensionQuadraticForm K)) :
    V.specialOrthogonalMatrixGroup K :=
  V.specialOrthogonalMatrixPointToGroup K
    (V.detOneIsometrySpecialOrthogonalMatrixPoint K g)

@[simp]
theorem detOneIsometrySpecialOrthogonalMatrixGroup_apply_matrix
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (g : DetOneIsometryGroup
      (V.commutativeScalarExtensionQuadraticForm K)) :
    (V.detOneIsometrySpecialOrthogonalMatrixGroup K g).1.1.1 =
      LinearMap.toMatrix' g.1.toLinearEquiv.toLinearMap := by
  have h := (V.specialOrthogonalMatrixPointEquivGroup K).left_inv
    (V.detOneIsometrySpecialOrthogonalMatrixPoint K g)
  exact congrArg Subtype.val h

theorem specialOrthogonalMatrixGroupDetOneIsometryHom_inverse_apply
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (g : DetOneIsometryGroup
      (V.commutativeScalarExtensionQuadraticForm K)) :
    V.specialOrthogonalMatrixGroupDetOneIsometryHom K
        (V.detOneIsometrySpecialOrthogonalMatrixGroup K g) = g := by
  apply Subtype.ext
  apply DFunLike.coe_injective
  funext x
  have hlin :
      (V.specialOrthogonalMatrixGroupIsometryEquiv K
        (V.detOneIsometrySpecialOrthogonalMatrixGroup K g)).toLinearEquiv.toLinearMap =
        g.1.toLinearEquiv.toLinearMap := by
    apply (LinearMap.toMatrix'
      (R := K) (m := Fin n) (n := Fin n)).injective
    rw [V.specialOrthogonalMatrixGroupIsometryEquiv_toMatrix',
      V.detOneIsometrySpecialOrthogonalMatrixGroup_apply_matrix]
  exact LinearMap.congr_fun hlin x

theorem specialOrthogonalMatrixGroupDetOneIsometryHom_bijective
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K] :
    Function.Bijective
      (V.specialOrthogonalMatrixGroupDetOneIsometryHom K) := by
  constructor
  · intro g h hgh
    have hiso : V.specialOrthogonalMatrixGroupIsometryEquiv K g =
        V.specialOrthogonalMatrixGroupIsometryEquiv K h :=
      congrArg Subtype.val hgh
    have hmat := congrArg
      (fun e : (V.commutativeScalarExtensionQuadraticForm K).IsometryEquiv
          (V.commutativeScalarExtensionQuadraticForm K) =>
        LinearMap.toMatrix' e.toLinearEquiv.toLinearMap) hiso
    change LinearMap.toMatrix'
        (V.specialOrthogonalMatrixGroupIsometryEquiv K g).toLinearEquiv.toLinearMap =
      LinearMap.toMatrix'
        (V.specialOrthogonalMatrixGroupIsometryEquiv K h).toLinearEquiv.toLinearMap at hmat
    rw [V.specialOrthogonalMatrixGroupIsometryEquiv_toMatrix',
      V.specialOrthogonalMatrixGroupIsometryEquiv_toMatrix'] at hmat
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact hmat
  · intro g
    exact ⟨V.detOneIsometrySpecialOrthogonalMatrixGroup K g,
      V.specialOrthogonalMatrixGroupDetOneIsometryHom_inverse_apply K g⟩

/-- Concrete special-orthogonal matrices are multiplicatively equivalent to
determinant-one quadratic self-isometries. -/
noncomputable def specialOrthogonalMatrixGroupDetOneIsometryMulEquiv
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K] :
    V.specialOrthogonalMatrixGroup K ≃*
      DetOneIsometryGroup
        (V.commutativeScalarExtensionQuadraticForm K) :=
  MulEquiv.ofBijective
    (V.specialOrthogonalMatrixGroupDetOneIsometryHom K)
    (V.specialOrthogonalMatrixGroupDetOneIsometryHom_bijective K)

/-- The spinor norm on the concrete scalar-extension special-orthogonal
matrix group. -/
noncomputable def specialOrthogonalSpinorNormHom
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K] :
    V.specialOrthogonalMatrixGroup K →* Rat.SquareClass K :=
  (determinantOneSpinorNormHom
      (V.commutativeScalarExtensionQuadraticForm K)
      (V.commutativeScalarExtensionQuadraticForm_associated_nondegenerate K)).comp
    (V.specialOrthogonalMatrixGroupDetOneIsometryHom K)

theorem specialOrthogonalSpinorNormHom_eq_reflectionPairSquareClassProduct
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (g : V.specialOrthogonalMatrixGroup K)
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair
      (V.commutativeScalarExtensionQuadraticForm K)))
    (hps : eval (V.commutativeScalarExtensionQuadraticForm K)
      (flattenPairs (V.commutativeScalarExtensionQuadraticForm K) ps) =
        V.specialOrthogonalMatrixGroupIsometryEquiv K g) :
    V.specialOrthogonalSpinorNormHom K g =
      reflectionPairSquareClassProduct
        (V.commutativeScalarExtensionQuadraticForm K) ps := by
  exact determinantOneSpinorNorm_eq_reflectionPairSquareClassProduct
    (V.commutativeScalarExtensionQuadraticForm K)
    (V.commutativeScalarExtensionQuadraticForm_associated_nondegenerate K)
    (V.specialOrthogonalMatrixGroupDetOneIsometryHom K g) ps hps

/-- The real spinor-norm homomorphism. -/
noncomputable def realSpecialOrthogonalSpinorNormHom :
    V.RealSpecialOrthogonalGroup →* Rat.SquareClass ℝ :=
  V.specialOrthogonalSpinorNormHom ℝ

/-- The spinor-norm homomorphism over the standard p-adic field. -/
noncomputable def padicSpecialOrthogonalSpinorNormHom
    (p : ℕ) [Fact p.Prime] :
    V.specialOrthogonalMatrixGroup ℚ_[p] →* Rat.SquareClass ℚ_[p] :=
  V.specialOrthogonalSpinorNormHom ℚ_[p]

end RationalQuadraticSpaceMatrix

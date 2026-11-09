import SMSFormula.RationalCliffordSpinCandidateTopologicalGroup
import SMSFormula.RationalSpecialOrthogonalFullAdelicRealFiniteCarrier

/-!
# Real/finite product splitting for full-adelic Spin-candidate points

The affine point functor on the Spin-candidate coordinate ring sends a product
of rational algebras to the product of the two point groups.  Applying this to
the literal product presentation of the full rational adele ring and then to
the unique infinite-place equivalence gives a continuous group equivalence

```text
SpinCandidate(A_Q) ≃ₜ* SpinCandidate(R) × SpinCandidate(A_Q,f).
```

This is a topological carrier statement only.  It does not identify the finite
factor with a restricted product and constructs no Haar or Tamagawa measure.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-! ## Affine points over product algebras -/

/-- Candidate points over a product algebra split into their two component
point groups. -/
def cliffordSpinCandidateGroupProdEquiv
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] :
    V.CliffordSpinCandidateGroup (A × B) ≃*
      V.CliffordSpinCandidateGroup A × V.CliffordSpinCandidateGroup B where
  toFun x :=
    (V.cliffordSpinCandidateGroupMap (AlgHom.fst ℚ A B) x,
      V.cliffordSpinCandidateGroupMap (AlgHom.snd ℚ A B) x)
  invFun x := AlgHom.prod x.1 x.2
  left_inv x := by
    ext a <;> rfl
  right_inv x := by
    apply Prod.ext <;> ext a <;> rfl
  map_mul' x y := by
    exact Prod.ext
      (map_mul (V.cliffordSpinCandidateGroupMap (AlgHom.fst ℚ A B)) x y)
      (map_mul (V.cliffordSpinCandidateGroupMap (AlgHom.snd ℚ A B)) x y)

@[simp]
theorem cliffordSpinCandidateGroupProdEquiv_apply_fst
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (x : V.CliffordSpinCandidateGroup (A × B)) :
    (V.cliffordSpinCandidateGroupProdEquiv A B x).1 =
      V.cliffordSpinCandidateGroupMap (AlgHom.fst ℚ A B) x :=
  rfl

@[simp]
theorem cliffordSpinCandidateGroupProdEquiv_apply_snd
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (x : V.CliffordSpinCandidateGroup (A × B)) :
    (V.cliffordSpinCandidateGroupProdEquiv A B x).2 =
      V.cliffordSpinCandidateGroupMap (AlgHom.snd ℚ A B) x :=
  rfl

@[simp]
theorem cliffordSpinCandidateGroupProdEquiv_symm_apply
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (x : V.CliffordSpinCandidateGroup A ×
      V.CliffordSpinCandidateGroup B) :
    (V.cliffordSpinCandidateGroupProdEquiv A B).symm x =
      AlgHom.prod x.1 x.2 :=
  rfl

/-- The product splitting of candidate point groups is a topological group
equivalence for the finite-coordinate topologies. -/
def cliffordSpinCandidateGroupProdContinuousEquiv
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B] :
    V.CliffordSpinCandidateGroup (A × B) ≃ₜ*
      V.CliffordSpinCandidateGroup A × V.CliffordSpinCandidateGroup B where
  toMulEquiv := V.cliffordSpinCandidateGroupProdEquiv A B
  continuous_toFun := by
    apply Continuous.prodMk
    · exact V.continuous_cliffordSpinCandidateGroupMap
        (AlgHom.fst ℚ A B) continuous_fst
    · exact V.continuous_cliffordSpinCandidateGroupMap
        (AlgHom.snd ℚ A B) continuous_snd
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    apply Continuous.prodMk
    · apply continuous_pi
      intro u
      change Continuous (fun x : V.CliffordSpinCandidateGroup A ×
        V.CliffordSpinCandidateGroup B =>
          ((V.cliffordSpinCandidateGroupProdEquiv A B).symm x)
            (V.cliffordSpinCandidateCliffordCoordinate u))
      simp only [V.cliffordSpinCandidateGroupProdEquiv_symm_apply]
      exact
        ((V.continuous_cliffordSpinCandidateCliffordCoordinate A u).comp
          continuous_fst).prodMk
        ((V.continuous_cliffordSpinCandidateCliffordCoordinate B u).comp
          continuous_snd)
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      change Continuous (fun x : V.CliffordSpinCandidateGroup A ×
        V.CliffordSpinCandidateGroup B =>
          ((V.cliffordSpinCandidateGroupProdEquiv A B).symm x)
            (V.cliffordSpinCandidateMatrixCoordinate i j))
      simp only [V.cliffordSpinCandidateGroupProdEquiv_symm_apply]
      exact
        ((V.continuous_cliffordSpinCandidateMatrixCoordinate A i j).comp
          continuous_fst).prodMk
        ((V.continuous_cliffordSpinCandidateMatrixCoordinate B i j).comp
          continuous_snd)

/-! ## Transport along rational ring equivalences -/

/-- A rational ring equivalence induces an equivalence of candidate point
groups by scalar extension. -/
def cliffordSpinCandidateGroupRingEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (e : A ≃+* B) :
    V.CliffordSpinCandidateGroup A ≃*
      V.CliffordSpinCandidateGroup B where
  toFun := V.cliffordSpinCandidateGroupMap e.toRingHom.toRatAlgHom
  invFun := V.cliffordSpinCandidateGroupMap e.symm.toRingHom.toRatAlgHom
  left_inv x := by
    ext a
    exact e.symm_apply_apply (x a)
  right_inv x := by
    ext a
    exact e.apply_symm_apply (x a)
  map_mul' x y :=
    map_mul (V.cliffordSpinCandidateGroupMap e.toRingHom.toRatAlgHom) x y

/-- A continuous rational ring equivalence with continuous inverse induces a
continuous equivalence of candidate point groups. -/
def cliffordSpinCandidateGroupRingContinuousEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃+* B) (he : Continuous e) (he_symm : Continuous e.symm) :
    V.CliffordSpinCandidateGroup A ≃ₜ*
      V.CliffordSpinCandidateGroup B where
  toMulEquiv := V.cliffordSpinCandidateGroupRingEquiv e
  continuous_toFun :=
    V.continuous_cliffordSpinCandidateGroupMap
      e.toRingHom.toRatAlgHom he
  continuous_invFun :=
    V.continuous_cliffordSpinCandidateGroupMap
      e.symm.toRingHom.toRatAlgHom he_symm

/-! ## Rational full-adeles -/

/-- Infinite-adelic candidate points are continuously equivalent to real
candidate points. -/
def infiniteAdelicCliffordSpinCandidateGroupContinuousEquivReal :
    V.CliffordSpinCandidateGroup RationalInfiniteAdele ≃ₜ*
      V.RealCliffordSpinCandidateGroup :=
  V.cliffordSpinCandidateGroupRingContinuousEquiv
    rationalInfiniteAdeleRingEquivReal
    rationalInfiniteAdeleHomeomorphReal.continuous
    rationalInfiniteAdeleHomeomorphReal.symm.continuous

/-- Full-adelic candidate points split continuously into their infinite and
finite components. -/
def fullAdelicCliffordSpinCandidateGroupProdContinuousEquiv :
    V.FullAdelicCliffordSpinCandidateGroup ≃ₜ*
      V.CliffordSpinCandidateGroup RationalInfiniteAdele ×
        V.FiniteAdelicCliffordSpinCandidateGroup :=
  V.cliffordSpinCandidateGroupProdContinuousEquiv
    RationalInfiniteAdele RationalFiniteAdele

/-- Full-adelic candidate points split continuously into their real and
finite-adelic components. -/
def fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv :
    V.FullAdelicCliffordSpinCandidateGroup ≃ₜ*
      V.RealCliffordSpinCandidateGroup ×
        V.FiniteAdelicCliffordSpinCandidateGroup :=
  V.fullAdelicCliffordSpinCandidateGroupProdContinuousEquiv.trans
    (prodContinuousMulEquiv
      V.infiniteAdelicCliffordSpinCandidateGroupContinuousEquivReal
      (ContinuousMulEquiv.refl _))

@[simp]
theorem fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv_apply_real
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv x).1 =
      V.cliffordSpinCandidateGroupMap
        rationalInfiniteAdeleRingEquivReal.toRingHom.toRatAlgHom
        (V.cliffordSpinCandidateGroupMap
          (AlgHom.fst ℚ RationalInfiniteAdele RationalFiniteAdele) x) :=
  rfl

@[simp]
theorem fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv_apply_finite
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv x).2 =
      V.cliffordSpinCandidateGroupMap
        (AlgHom.snd ℚ RationalInfiniteAdele RationalFiniteAdele) x :=
  rfl

/-- The real/finite product splitting commutes with the completed
candidate-to-special-orthogonal homomorphisms. -/
theorem fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv_toSpecialOrthogonal
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    V.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        (V.fullAdelicCliffordSpinCandidateToSpecialOrthogonalHom x) =
      (V.realCliffordSpinCandidateToSpecialOrthogonalHom
          (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv x).1,
        V.finiteAdelicCliffordSpinCandidateToSpecialOrthogonalHom
          (V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv x).2) := by
  apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext
  · ext i j
    rfl
  · ext i j
    rfl

end RationalQuadraticSpaceMatrix

import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralTopology

/-!
# Special-orthogonal transport under an arbitrary rational isometry

The represented special-orthogonal point map attached to a supplied rational
quadratic isometry is promoted to a continuous multiplicative equivalence on
the repository's existing matrix-group carriers.  Continuity is proved
coordinatewise from the scalar-extended isometry and its inverse.

No rank identification, Haar measure, chart, integral structure, quotient
measure, raw certificate, or Tamagawa value is selected.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 800000

variable {r s : ℕ}
variable (U : RationalQuadraticSpaceMatrix r)
variable (V : RationalQuadraticSpaceMatrix s)
variable (e : U.quadraticForm.IsometryEquiv V.quadraticForm)

private local instance specialOrthogonalMatrixPointTopologicalSpace
    {a : ℕ} {W : RationalQuadraticSpaceMatrix a}
    {A : Type*} [CommRing A] [Algebra ℚ A] [TopologicalSpace A] :
    TopologicalSpace (W.specialOrthogonalMatrixPoint A) :=
  TopologicalSpace.induced Subtype.val inferInstance

private theorem continuous_specialOrthogonalMatrixPointToGroup
    {a : ℕ} (W : RationalQuadraticSpaceMatrix a)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (W.specialOrthogonalMatrixPointToGroup A) := by
  let toSet : W.specialOrthogonalMatrixPoint A →
      Matrix.specialOrthogonalMatrixSet
        (W.specialOrthogonalMappedFormMatrix A) := fun g ↦
    ⟨g.1,
      (Matrix.formPreservingConstraint_eq_zero_iff
        (W.specialOrthogonalMappedFormMatrix A) g.1).mpr g.2.1,
      g.2.2⟩
  have htoSet : Continuous toSet := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  rw [show W.specialOrthogonalMatrixPointToGroup A =
      fun g ↦ specialOrthogonalMatrixSetToSpecialSubgroup
        (W.specialOrthogonalMappedFormMatrix A) (toSet g) by
    funext g
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl]
  exact
    (continuous_specialOrthogonalMatrixSetToSpecialSubgroup
      (W.specialOrthogonalMappedFormMatrix A)).comp htoSet

private theorem continuous_specialOrthogonalMatrixPointOfGroup
    {a : ℕ} (W : RationalQuadraticSpaceMatrix a)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (W.specialOrthogonalMatrixPointOfGroup A) := by
  apply continuous_induced_rng.mpr
  exact Units.continuous_val.comp
    (continuous_subtype_val.comp continuous_subtype_val)

/-- Reversing an arbitrary rational isometry is a left inverse on represented
special-orthogonal points. -/
theorem rationalIsometrySpecialOrthogonalMatrixPoint_symm_apply_apply
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : U.specialOrthogonalMatrixPoint A) :
    rationalIsometrySpecialOrthogonalMatrixPoint V U e.symm A
        (rationalIsometrySpecialOrthogonalMatrixPoint U V e A g) = g := by
  apply Subtype.ext
  ext i j
  let E := rationalIsometryBaseChangeIsometryEquiv U V e A
  let b : Fin r → A := Pi.single j 1
  have hvec :
      Matrix.mulVec
          (rationalIsometrySpecialOrthogonalMatrixPoint V U e.symm A
            (rationalIsometrySpecialOrthogonalMatrixPoint U V e A g)).1 b =
        Matrix.mulVec g.1 b := by
    rw [rationalIsometrySpecialOrthogonalMatrixPoint_mulVec]
    change E.symm
        (V.specialOrthogonalMatrixPointIsometryEquiv A
          (rationalIsometrySpecialOrthogonalMatrixPoint U V e A g) (E b)) = _
    rw [V.specialOrthogonalMatrixPointIsometryEquiv_apply]
    rw [rationalIsometrySpecialOrthogonalMatrixPoint_mulVec]
    change E.symm (E
      (U.specialOrthogonalMatrixPointIsometryEquiv A g
        (E.symm (E b)))) = _
    calc
      E.symm (E
          (U.specialOrthogonalMatrixPointIsometryEquiv A g
            (E.symm (E b)))) =
        U.specialOrthogonalMatrixPointIsometryEquiv A g
          (E.symm (E b)) := E.symm_apply_apply _
      _ = U.specialOrthogonalMatrixPointIsometryEquiv A g b := by
        exact congrArg (U.specialOrthogonalMatrixPointIsometryEquiv A g)
          (E.toLinearEquiv.symm_apply_apply b)
      _ = Matrix.mulVec g.1 b :=
        U.specialOrthogonalMatrixPointIsometryEquiv_apply A g b
  simpa [Matrix.mulVec, dotProduct, b, Pi.single_apply] using congrFun hvec i

/-- Forward arbitrary-isometry transport is a left inverse to transport along
the reversed isometry on represented special-orthogonal points. -/
theorem rationalIsometrySpecialOrthogonalMatrixPoint_apply_symm_apply
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : V.specialOrthogonalMatrixPoint A) :
    rationalIsometrySpecialOrthogonalMatrixPoint U V e A
        (rationalIsometrySpecialOrthogonalMatrixPoint V U e.symm A g) = g := by
  exact rationalIsometrySpecialOrthogonalMatrixPoint_symm_apply_apply
    V U e.symm A g

/-- The represented special-orthogonal group equivalence induced by an
arbitrary supplied rational quadratic isometry. -/
def rationalIsometrySpecialOrthogonalGroupEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    U.specialOrthogonalMatrixGroup A ≃ V.specialOrthogonalMatrixGroup A where
  toFun g := V.specialOrthogonalMatrixPointToGroup A
    (rationalIsometrySpecialOrthogonalMatrixPoint U V e A
      (U.specialOrthogonalMatrixPointOfGroup A g))
  invFun g := U.specialOrthogonalMatrixPointToGroup A
    (rationalIsometrySpecialOrthogonalMatrixPoint V U e.symm A
      (V.specialOrthogonalMatrixPointOfGroup A g))
  left_inv g := by
    change U.specialOrthogonalMatrixPointToGroup A
      (rationalIsometrySpecialOrthogonalMatrixPoint V U e.symm A
        (rationalIsometrySpecialOrthogonalMatrixPoint U V e A
          (U.specialOrthogonalMatrixPointOfGroup A g))) = g
    rw [rationalIsometrySpecialOrthogonalMatrixPoint_symm_apply_apply]
    exact U.specialOrthogonalMatrixPointEquivGroup A |>.apply_symm_apply g
  right_inv g := by
    change V.specialOrthogonalMatrixPointToGroup A
      (rationalIsometrySpecialOrthogonalMatrixPoint U V e A
        (rationalIsometrySpecialOrthogonalMatrixPoint V U e.symm A
          (V.specialOrthogonalMatrixPointOfGroup A g))) = g
    rw [rationalIsometrySpecialOrthogonalMatrixPoint_apply_symm_apply]
    exact V.specialOrthogonalMatrixPointEquivGroup A |>.apply_symm_apply g

/-- Arbitrary-isometry special-orthogonal transport preserves matrix
multiplication. -/
theorem rationalIsometrySpecialOrthogonalGroupEquiv_map_mul
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g h : U.specialOrthogonalMatrixGroup A) :
    rationalIsometrySpecialOrthogonalGroupEquiv U V e A (g * h) =
      rationalIsometrySpecialOrthogonalGroupEquiv U V e A g *
        rationalIsometrySpecialOrthogonalGroupEquiv U V e A h := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  let E := rationalIsometryBaseChangeIsometryEquiv U V e A
  let b : Fin s → A := Pi.single j 1
  let gp := U.specialOrthogonalMatrixPointOfGroup A g
  let hp := U.specialOrthogonalMatrixPointOfGroup A h
  let ghp := U.specialOrthogonalMatrixPointOfGroup A (g * h)
  let G := rationalIsometrySpecialOrthogonalMatrixPoint U V e A gp
  let H := rationalIsometrySpecialOrthogonalMatrixPoint U V e A hp
  let GH := rationalIsometrySpecialOrthogonalMatrixPoint U V e A ghp
  have htransport (q : U.specialOrthogonalMatrixGroup A)
      (qp : U.specialOrthogonalMatrixPoint A)
      (hqp : qp = U.specialOrthogonalMatrixPointOfGroup A q)
      (y : Fin s → A) :
      Matrix.mulVec
          (rationalIsometrySpecialOrthogonalMatrixPoint U V e A qp).1 y =
        E (Matrix.mulVec q.1.1.1 (E.symm y)) := by
    subst qp
    rw [rationalIsometrySpecialOrthogonalMatrixPoint_mulVec]
    change E
        (U.specialOrthogonalMatrixPointIsometryEquiv A
          (U.specialOrthogonalMatrixPointOfGroup A q) (E.symm y)) = _
    rw [U.specialOrthogonalMatrixPointIsometryEquiv_apply]
    rfl
  have hHpre :
      Matrix.mulVec h.1.1.1 (E.symm b) =
        E.symm (Matrix.mulVec H.1 b) := by
    calc
      Matrix.mulVec h.1.1.1 (E.symm b) =
          E.symm (E (Matrix.mulVec h.1.1.1 (E.symm b))) :=
        (E.symm_apply_apply _).symm
      _ = E.symm (Matrix.mulVec H.1 b) :=
        congrArg E.symm (htransport h hp rfl b).symm
  have hvec : Matrix.mulVec GH.1 b = Matrix.mulVec (G.1 * H.1) b := by
    calc
      Matrix.mulVec GH.1 b =
          E (U.specialOrthogonalMatrixPointIsometryEquiv A ghp
            (E.symm b)) :=
        rationalIsometrySpecialOrthogonalMatrixPoint_mulVec U V e A ghp b
      _ = E (Matrix.mulVec (g.1.1.1 * h.1.1.1) (E.symm b)) := by
        rw [U.specialOrthogonalMatrixPointIsometryEquiv_apply]
        rfl
      _ = E (Matrix.mulVec g.1.1.1
          (Matrix.mulVec h.1.1.1 (E.symm b))) := by
        rw [Matrix.mulVec_mulVec]
      _ = E (Matrix.mulVec g.1.1.1
          (E.symm (Matrix.mulVec H.1 b))) := by
        rw [hHpre]
      _ = Matrix.mulVec G.1 (Matrix.mulVec H.1 b) := by
        exact (htransport g gp rfl (Matrix.mulVec H.1 b)).symm
      _ = Matrix.mulVec (G.1 * H.1) b := by
        rw [Matrix.mulVec_mulVec]
  simpa [rationalIsometrySpecialOrthogonalGroupEquiv, G, H, GH,
    Matrix.mulVec, dotProduct, b, Pi.single_apply] using congrFun hvec i

/-- The arbitrary-isometry special-orthogonal group equivalence as a
multiplicative equivalence. -/
def rationalIsometrySpecialOrthogonalGroupMulEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    U.specialOrthogonalMatrixGroup A ≃* V.specialOrthogonalMatrixGroup A where
  toEquiv := rationalIsometrySpecialOrthogonalGroupEquiv U V e A
  map_mul' := rationalIsometrySpecialOrthogonalGroupEquiv_map_mul U V e A

private theorem continuous_rationalIsometrySpecialOrthogonalMatrixPoint
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (rationalIsometrySpecialOrthogonalMatrixPoint U V e A) := by
  let E := rationalIsometryBaseChangeIsometryEquiv U V e A
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  let b : Fin s → A := Pi.single j 1
  let v : Fin r → A := E.symm b
  have hmatrix (k l : Fin r) : Continuous
      (fun g : U.specialOrthogonalMatrixPoint A ↦ g.1 k l) :=
    (continuous_apply l).comp
      ((continuous_apply k).comp
        (continuous_subtype_val : Continuous
          (Subtype.val : U.specialOrthogonalMatrixPoint A →
            Matrix (Fin r) (Fin r) A)))
  have hcont : Continuous (fun g : U.specialOrthogonalMatrixPoint A ↦
      E (Matrix.mulVec g.1 v) i) := by
    apply (continuous_apply i).comp
    apply (continuous_rationalIsometryBaseChangeIsometryEquiv U V e A).comp
    apply continuous_pi
    intro k
    change Continuous (fun g : U.specialOrthogonalMatrixPoint A ↦
      ∑ l, g.1 k l * v l)
    apply continuous_finset_sum
    intro l _
    exact (hmatrix k l).mul continuous_const
  change Continuous (fun g : U.specialOrthogonalMatrixPoint A ↦
    (rationalIsometrySpecialOrthogonalMatrixPoint U V e A g).1 i j)
  rw [show (fun g : U.specialOrthogonalMatrixPoint A ↦
      (rationalIsometrySpecialOrthogonalMatrixPoint U V e A g).1 i j) =
      fun g ↦ E (Matrix.mulVec g.1 v) i by
    funext g
    have hcol :
        (rationalIsometrySpecialOrthogonalMatrixPoint U V e A g).1 i j =
          Matrix.mulVec
            (rationalIsometrySpecialOrthogonalMatrixPoint U V e A g).1 b i := by
      simp [b, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hcol, rationalIsometrySpecialOrthogonalMatrixPoint_mulVec]
    ]
  exact hcont

/-- The arbitrary-isometry special-orthogonal group equivalence is continuous
for every native topological rational algebra. -/
def rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    U.specialOrthogonalMatrixGroup A ≃ₜ* V.specialOrthogonalMatrixGroup A :=
  ContinuousMulEquiv.mk'
    { toEquiv := (rationalIsometrySpecialOrthogonalGroupMulEquiv U V e A).toEquiv
      continuous_toFun :=
        (continuous_specialOrthogonalMatrixPointToGroup V A).comp
          ((continuous_rationalIsometrySpecialOrthogonalMatrixPoint U V e A).comp
            (continuous_specialOrthogonalMatrixPointOfGroup U A))
      continuous_invFun :=
        (continuous_specialOrthogonalMatrixPointToGroup U A).comp
          ((continuous_rationalIsometrySpecialOrthogonalMatrixPoint V U e.symm A).comp
            (continuous_specialOrthogonalMatrixPointOfGroup V A)) }
    (rationalIsometrySpecialOrthogonalGroupMulEquiv U V e A).map_mul

@[simp]
theorem rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv_apply
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (g : U.specialOrthogonalMatrixGroup A) :
    rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv U V e A g =
      V.specialOrthogonalMatrixPointToGroup A
        (rationalIsometrySpecialOrthogonalMatrixPoint U V e A
          (U.specialOrthogonalMatrixPointOfGroup A g)) :=
  rfl

/-- Arbitrary-isometry Spin transport commutes with its represented
special-orthogonal group equivalence. -/
theorem rationalIsometrySpinCandidate_specialOrthogonal_commutes
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (z : U.CliffordSpinCandidateGroup A) :
    rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv U V e A
        (U.cliffordSpinCandidateGroupToSpecialOrthogonal A z) =
      V.cliffordSpinCandidateGroupToSpecialOrthogonal A
        (rationalIsometrySpinCandidateMulEquiv U V e A z) := by
  rw [rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv_apply]
  have h :=
    cliffordSpinCandidateToGeneralSpin_rationalIsometrySpinCandidateMulEquiv
      U V e A z
  have hm := congrArg
    (fun w : V.CliffordGeneralSpinIntrinsicPoint A ↦ w.matrixGroup) h
  exact hm.symm

end RationalQuadraticSpaceMatrix

end

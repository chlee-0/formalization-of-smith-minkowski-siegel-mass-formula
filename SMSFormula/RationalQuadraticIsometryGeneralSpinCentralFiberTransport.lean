import SMSFormula.RationalQuadraticIsometryGeneralSpinRealTangentHaar
import SMSFormula.RationalQuadraticIsometryGeneralSpinHaarFactorization

/-!
# Central-fiber transport across anisotropic presentations

The supplied rational quadratic isometry transports not only intrinsic
`GSpin` points but also their special-orthogonal coordinate.  This file
packages the latter transport as a multiplicative equivalence and proves that
the crossed map `(nu, pi)` commutes literally with presentation transport.

This is the algebraic square underlying the remaining real identity-chart
measure comparison.  No equality between independently chosen
partial-homeomorphism domains and no Haar-measure identity is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- Reverse special-orthogonal presentation transport is a left inverse of
the forward transport. -/
theorem ambientToBlockSpecialOrthogonalMatrixPoint_blockToAmbient
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : (P.blockSpace hx).specialOrthogonalMatrixPoint A) :
    P.ambientToBlockSpecialOrthogonalMatrixPoint A hx
        (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx g) = g := by
  apply Subtype.ext
  ext i j
  let e := P.blockToAmbientBaseChangeIsometryEquiv hx A
  let b : Fin (m + 1) → A := Pi.single j 1
  have hvec :
      Matrix.mulVec
          (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx
            (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx g)).1 b =
        Matrix.mulVec g.1 b := by
    rw [P.ambientToBlockSpecialOrthogonalMatrixPoint_mulVec A hx]
    change e.symm
        (V.specialOrthogonalMatrixPointIsometryEquiv A
          (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx g) (e b)) = _
    rw [V.specialOrthogonalMatrixPointIsometryEquiv_apply]
    rw [P.blockToAmbientSpecialOrthogonalMatrixPoint_mulVec A hx]
    change e.symm (e
      ((P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A g
        (e.symm (e b)))) = _
    calc
      e.symm (e
          ((P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A g
            (e.symm (e b)))) =
        (P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A g
          (e.symm (e b)) := e.symm_apply_apply _
      _ = (P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A g b := by
        exact congrArg
          ((P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A g)
          (e.toLinearEquiv.symm_apply_apply b)
      _ = Matrix.mulVec g.1 b :=
        (P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv_apply
          A g b
  simpa [Matrix.mulVec, dotProduct, b, Pi.single_apply] using congrFun hvec i

/-- Forward special-orthogonal presentation transport is a left inverse of
the reverse transport. -/
theorem blockToAmbientSpecialOrthogonalMatrixPoint_ambientToBlock
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : V.specialOrthogonalMatrixPoint A) :
    P.blockToAmbientSpecialOrthogonalMatrixPoint A hx
        (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx g) = g := by
  apply Subtype.ext
  ext i j
  let e := P.blockToAmbientBaseChangeIsometryEquiv hx A
  let b : Fin n → A := Pi.single j 1
  have hvec :
      Matrix.mulVec
          (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx
            (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx g)).1 b =
        Matrix.mulVec g.1 b := by
    rw [P.blockToAmbientSpecialOrthogonalMatrixPoint_mulVec A hx]
    change e
        ((P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A
          (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx g) (e.symm b)) = _
    rw [(P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv_apply]
    rw [P.ambientToBlockSpecialOrthogonalMatrixPoint_mulVec A hx]
    change e (e.symm
      (V.specialOrthogonalMatrixPointIsometryEquiv A g
        (e (e.symm b)))) = _
    calc
      e (e.symm
          (V.specialOrthogonalMatrixPointIsometryEquiv A g
            (e (e.symm b)))) =
        V.specialOrthogonalMatrixPointIsometryEquiv A g
          (e (e.symm b)) := e.apply_symm_apply _
      _ = V.specialOrthogonalMatrixPointIsometryEquiv A g b := by
        exact congrArg (V.specialOrthogonalMatrixPointIsometryEquiv A g)
          (e.toLinearEquiv.apply_symm_apply b)
      _ = Matrix.mulVec g.1 b :=
        V.specialOrthogonalMatrixPointIsometryEquiv_apply A g b
  simpa [Matrix.mulVec, dotProduct, b, Pi.single_apply] using congrFun hvec i

/-- The special-orthogonal coordinate transport induced by the supplied
quadratic presentation. -/
def blockToAmbientSpecialOrthogonalGroupEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockSpace hx).specialOrthogonalMatrixGroup A ≃
      V.specialOrthogonalMatrixGroup A where
  toFun g := V.specialOrthogonalMatrixPointToGroup A
    (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx
      ((P.blockSpace hx).specialOrthogonalMatrixPointOfGroup A g))
  invFun g := (P.blockSpace hx).specialOrthogonalMatrixPointToGroup A
    (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx
      (V.specialOrthogonalMatrixPointOfGroup A g))
  left_inv g := by
    change (P.blockSpace hx).specialOrthogonalMatrixPointToGroup A
      (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx
        (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx
          ((P.blockSpace hx).specialOrthogonalMatrixPointOfGroup A g))) = g
    rw [P.ambientToBlockSpecialOrthogonalMatrixPoint_blockToAmbient A hx]
    exact (P.blockSpace hx).specialOrthogonalMatrixPointEquivGroup A
      |>.apply_symm_apply g
  right_inv g := by
    change V.specialOrthogonalMatrixPointToGroup A
      (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx
        (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx
          (V.specialOrthogonalMatrixPointOfGroup A g))) = g
    rw [P.blockToAmbientSpecialOrthogonalMatrixPoint_ambientToBlock A hx]
    exact V.specialOrthogonalMatrixPointEquivGroup A |>.apply_symm_apply g

/-- The special-orthogonal presentation equivalence preserves matrix
multiplication. -/
theorem blockToAmbientSpecialOrthogonalGroupEquiv_map_mul
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g h : (P.blockSpace hx).specialOrthogonalMatrixGroup A) :
    P.blockToAmbientSpecialOrthogonalGroupEquiv A hx (g * h) =
      P.blockToAmbientSpecialOrthogonalGroupEquiv A hx g *
        P.blockToAmbientSpecialOrthogonalGroupEquiv A hx h := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  let e := P.blockToAmbientBaseChangeIsometryEquiv hx A
  let b : Fin n → A := Pi.single j 1
  let gp := (P.blockSpace hx).specialOrthogonalMatrixPointOfGroup A g
  let hp := (P.blockSpace hx).specialOrthogonalMatrixPointOfGroup A h
  let ghp := (P.blockSpace hx).specialOrthogonalMatrixPointOfGroup A (g * h)
  let G := P.blockToAmbientSpecialOrthogonalMatrixPoint A hx gp
  let H := P.blockToAmbientSpecialOrthogonalMatrixPoint A hx hp
  let GH := P.blockToAmbientSpecialOrthogonalMatrixPoint A hx ghp
  have htransport (q : (P.blockSpace hx).specialOrthogonalMatrixGroup A)
      (qp : (P.blockSpace hx).specialOrthogonalMatrixPoint A)
      (hqp : qp = (P.blockSpace hx).specialOrthogonalMatrixPointOfGroup A q)
      (y : Fin n → A) :
      Matrix.mulVec
          (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx qp).1 y =
        e (Matrix.mulVec q.1.1.1 (e.symm y)) := by
    subst qp
    rw [P.blockToAmbientSpecialOrthogonalMatrixPoint_mulVec A hx]
    change e
        ((P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A
          ((P.blockSpace hx).specialOrthogonalMatrixPointOfGroup A q)
          (e.symm y)) = _
    rw [(P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv_apply]
    rfl
  have hHpre :
      Matrix.mulVec h.1.1.1 (e.symm b) =
        e.symm (Matrix.mulVec H.1 b) := by
    calc
      Matrix.mulVec h.1.1.1 (e.symm b) =
          e.symm (e (Matrix.mulVec h.1.1.1 (e.symm b))) :=
        (e.symm_apply_apply _).symm
      _ = e.symm (Matrix.mulVec H.1 b) :=
        congrArg e.symm (htransport h hp rfl b).symm
  have hvec : Matrix.mulVec GH.1 b = Matrix.mulVec (G.1 * H.1) b := by
    calc
      Matrix.mulVec GH.1 b =
          e ((P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A ghp
            (e.symm b)) :=
        P.blockToAmbientSpecialOrthogonalMatrixPoint_mulVec A hx ghp b
      _ = e (Matrix.mulVec (g.1.1.1 * h.1.1.1) (e.symm b)) := by
        rw [(P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv_apply]
        rfl
      _ = e (Matrix.mulVec g.1.1.1
          (Matrix.mulVec h.1.1.1 (e.symm b))) := by
        rw [Matrix.mulVec_mulVec]
      _ = e (Matrix.mulVec g.1.1.1
          (e.symm (Matrix.mulVec H.1 b))) := by
        rw [hHpre]
      _ = Matrix.mulVec G.1 (Matrix.mulVec H.1 b) := by
        exact (htransport g gp rfl (Matrix.mulVec H.1 b)).symm
      _ = Matrix.mulVec (G.1 * H.1) b := by
        rw [Matrix.mulVec_mulVec]
  simpa [blockToAmbientSpecialOrthogonalGroupEquiv, G, H, GH,
    Matrix.mulVec, dotProduct, b, Pi.single_apply] using congrFun hvec i

/-- The special-orthogonal coordinate transport as a multiplicative
equivalence. -/
def blockToAmbientSpecialOrthogonalGroupMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockSpace hx).specialOrthogonalMatrixGroup A ≃*
      V.specialOrthogonalMatrixGroup A where
  toEquiv := P.blockToAmbientSpecialOrthogonalGroupEquiv A hx
  map_mul' := P.blockToAmbientSpecialOrthogonalGroupEquiv_map_mul A hx

/-- Presentation transport on the crossed central-fiber target leaves the
unit coordinate fixed and conjugates only the special-orthogonal coordinate. -/
def blockToAmbientCentralFiberTargetMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (Aˣ × (P.blockSpace hx).specialOrthogonalMatrixGroup A) ≃*
      (Aˣ × V.specialOrthogonalMatrixGroup A) where
  toEquiv := Equiv.prodCongr (Equiv.refl Aˣ)
    (P.blockToAmbientSpecialOrthogonalGroupMulEquiv A hx).toEquiv
  map_mul' y z := by
    apply Prod.ext
    · rfl
    · exact (P.blockToAmbientSpecialOrthogonalGroupMulEquiv A hx).map_mul
        y.2 z.2

/-- The crossed map `(nu, pi)` commutes literally with presentation
transport.  In particular, the similitude coordinate is unchanged. -/
theorem blockToAmbientGeneralSpin_centralFiber_commutes
    (K : Type*) [Field K] [Algebra ℚ K]
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint K) :
    P.blockToAmbientCentralFiberTargetMulEquiv K hx
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom
          (P.blockSpace hx) K z) =
      CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
        (P.blockToAmbientGeneralSpinIntrinsicPoint K hx z) := by
  apply Prod.ext
  · rfl
  · change V.specialOrthogonalMatrixPointToGroup K
        (P.blockToAmbientSpecialOrthogonalMatrixPoint K hx
          ((P.blockSpace hx).specialOrthogonalMatrixPointOfGroup K
            z.matrixGroup)) =
      V.specialOrthogonalMatrixPointToGroup K
        (P.blockToAmbientSpecialOrthogonalMatrixPoint K hx z.matrixPoint)
    rw [show (P.blockSpace hx).specialOrthogonalMatrixPointOfGroup K
        z.matrixGroup = z.matrixPoint from
      (P.blockSpace hx).specialOrthogonalMatrixPointEquivGroup K
        |>.left_inv z.matrixPoint]

/-- The inverse crossed-target transport gives the corresponding reverse
commuting square. -/
theorem ambientToBlockGeneralSpin_centralFiber_commutes
    (K : Type*) [Field K] [Algebra ℚ K]
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : V.CliffordGeneralSpinIntrinsicPoint K) :
    (P.blockToAmbientCentralFiberTargetMulEquiv K hx).symm
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K z) =
      CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom
        (P.blockSpace hx) K
        (P.ambientToBlockGeneralSpinIntrinsicPoint K hx z) := by
  apply (P.blockToAmbientCentralFiberTargetMulEquiv K hx).injective
  rw [P.blockToAmbientGeneralSpin_centralFiber_commutes K hx]
  rw [P.blockToAmbientGeneralSpinIntrinsicPoint_ambientToBlock K hx]
  exact (P.blockToAmbientCentralFiberTargetMulEquiv K hx).apply_symm_apply _

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end

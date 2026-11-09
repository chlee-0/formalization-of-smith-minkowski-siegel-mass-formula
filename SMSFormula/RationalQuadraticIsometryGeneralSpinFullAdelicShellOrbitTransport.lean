import SMSFormula.RationalQuadraticIsometryGeneralSpinTopology
import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellHomogeneousSpace

/-!
# Full-adelic shell orbit transport across a supplied presentation

The represented action of the transported intrinsic `GSpin` point on the
rational diagonal of an anisotropic ambient vector agrees literally with the
native block orbit transported through the existing shell homeomorphism.

This is the exact group/orbit/shell square needed before transporting the
orbit-fiber kernel.  No group or shell measure, chosen representative, new
chart, quotient scalar, cutoff, or Tamagawa theorem is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The represented ambient `GSpin` orbit through the rational diagonal of
`x`, valued in the already defined ambient quadratic shell. -/
def anisotropicRationalAmbientShellOrbitMap
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : V.CliffordGeneralSpinIntrinsicPoint A) :
    V.anisotropicRationalAmbientShell x A := by
  let e := V.specialOrthogonalMatrixPointIsometryEquiv A z.matrixPoint
  let y : Fin n → A := fun i => algebraMap ℚ A (x i)
  refine ⟨Matrix.mulVec z.matrixPoint.1 y, ?_⟩
  change V.commutativeScalarExtensionQuadraticForm A (e y) = _
  rw [e.map_app]
  exact V.commutativeScalarExtensionQuadraticForm_map ℚ (Algebra.ofId ℚ A) x

namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- Conjugated special-orthogonal action commutes literally with the supplied
base-change isometry over every commutative rational algebra. -/
theorem blockToAmbientBaseChangeIsometryEquiv_specialOrthogonal_mulVec
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (g : (P.blockSpace hx).specialOrthogonalMatrixPoint A)
    (y : Fin (m + 1) → A) :
    P.blockToAmbientBaseChangeIsometryEquiv hx A (Matrix.mulVec g.1 y) =
      Matrix.mulVec (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx g).1
        (P.blockToAmbientBaseChangeIsometryEquiv hx A y) := by
  rw [P.blockToAmbientSpecialOrthogonalMatrixPoint_mulVec A hx]
  change _ = P.blockToAmbientBaseChangeIsometryEquiv hx A
    ((P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A g
      ((P.blockToAmbientBaseChangeIsometryEquiv hx A).symm
        (P.blockToAmbientBaseChangeIsometryEquiv hx A y)))
  congr 1
  calc
    Matrix.mulVec g.1 y =
        (P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A g y :=
      ((P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv_apply
        A g y).symm
    _ = (P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A g
        ((P.blockToAmbientBaseChangeIsometryEquiv hx A).symm
          (P.blockToAmbientBaseChangeIsometryEquiv hx A y)) := by
      exact congrArg
        ((P.blockSpace hx).specialOrthogonalMatrixPointIsometryEquiv A g)
        ((P.blockToAmbientBaseChangeIsometryEquiv hx A).symm_apply_apply y).symm

/-- Pointwise form of the exact equivariance square for the full-adelic group
orbit and the native block-to-ambient shell homeomorphism. -/
theorem blockToAmbientShellHomeomorph_fullAdelic_orbit
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup) :
    P.blockToAmbientShellHomeomorph hx RationalAdele
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          P.lowerSpace (V.nativeRationalQuadraticForm x) hx RationalAdele z) =
      V.anisotropicRationalAmbientShellOrbitMap x RationalAdele
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx z) := by
  apply Subtype.ext
  change P.blockToAmbientBaseChangeIsometryEquiv hx RationalAdele
      (Matrix.mulVec z.matrixPoint.1 lastCoordinateVector) =
    Matrix.mulVec
      (P.blockToAmbientSpecialOrthogonalMatrixPoint RationalAdele hx z.matrixPoint).1
      (fun i => algebraMap ℚ RationalAdele (x i))
  rw [← P.blockToAmbientShellHomeomorph_lastCoordinateVector hx RationalAdele]
  exact P.blockToAmbientBaseChangeIsometryEquiv_specialOrthogonal_mulVec
    hx RationalAdele z.matrixPoint lastCoordinateVector

/-- Function equality expressing the complete full-adelic group/orbit/shell
commuting square. -/
theorem blockToAmbientShellHomeomorph_comp_fullAdelicOrbitMap
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.blockToAmbientShellHomeomorph hx RationalAdele ∘
        CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          P.lowerSpace (V.nativeRationalQuadraticForm x) hx RationalAdele =
      V.anisotropicRationalAmbientShellOrbitMap x RationalAdele ∘
        P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx := by
  funext z
  exact P.blockToAmbientShellHomeomorph_fullAdelic_orbit hx z

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

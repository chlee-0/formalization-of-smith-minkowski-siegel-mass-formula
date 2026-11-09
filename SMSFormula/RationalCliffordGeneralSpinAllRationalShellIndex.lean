import SMSFormula.RationalQuadraticIsometryGeneralSpinFullAdelicShellMeasureTransport

/-!
# Section-free index for all nonzero rational shells

Nonisotropic rational vectors are partitioned by their represented nonzero
quadratic value.  The resulting quotient is canonically equivalent to the
subtype of represented nonzero rational norms, and the full nonnegative sum
over vectors is reindexed as the iterated sum over norms and their literal
rational fibers.

For every supplied complement presentation, a fiber of the norm map is also
proved to be one rational intrinsic `GSpin` orbit.  The presentation occurs
only in that orbit-realization theorem; neither the quotient nor its norm
equivalence chooses a representative or a global family of presentations.
No measure, cutoff, all-shell unfolding, or Tamagawa theorem is asserted.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Rational vectors of nonzero quadratic value. -/
abbrev AnisotropicRationalVector (V : RationalQuadraticSpaceMatrix n) :=
  {x : Fin n → ℚ // V.nativeRationalQuadraticForm x ≠ 0}

/-- Two nonisotropic rational vectors represent the same shell exactly when
their rational quadratic values agree. -/
def anisotropicRationalVectorNormSetoid
    (V : RationalQuadraticSpaceMatrix n) :
    Setoid V.AnisotropicRationalVector where
  r x y := V.nativeRationalQuadraticForm x.1 =
    V.nativeRationalQuadraticForm y.1
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rfl
    · intro x y h
      exact h.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz

/-- The section-free quotient of nonisotropic rational vectors by equality
of norm.  The orbit-realization theorem below identifies each class with an
actual rational intrinsic `GSpin` orbit after supplying any complement
presentation at one point. -/
abbrev NonzeroRationalVectorOrbit (V : RationalQuadraticSpaceMatrix n) :=
  Quotient V.anisotropicRationalVectorNormSetoid

/-- Nonzero rational values represented by the ambient quadratic space. -/
def RepresentedNonzeroRationalNorm (V : RationalQuadraticSpaceMatrix n) :=
  {a : ℚ // a ≠ 0 ∧ ∃ x : Fin n → ℚ,
    V.nativeRationalQuadraticForm x = a}

instance anisotropicRationalVectorCountable
    (V : RationalQuadraticSpaceMatrix n) :
    Countable V.AnisotropicRationalVector := by
  infer_instance

instance nonzeroRationalVectorOrbitCountable
    (V : RationalQuadraticSpaceMatrix n) :
    Countable V.NonzeroRationalVectorOrbit := by
  infer_instance

instance representedNonzeroRationalNormCountable
    (V : RationalQuadraticSpaceMatrix n) :
    Countable V.RepresentedNonzeroRationalNorm := by
  apply Function.Injective.countable (f := Subtype.val)
  exact Subtype.val_injective

/-- The represented norm attached to a section-free rational-vector orbit. -/
def nonzeroRationalVectorOrbitNorm
    (V : RationalQuadraticSpaceMatrix n) :
    V.NonzeroRationalVectorOrbit → V.RepresentedNonzeroRationalNorm :=
  Quotient.lift
    (fun x ↦ ⟨V.nativeRationalQuadraticForm x.1, x.2, ⟨x.1, rfl⟩⟩)
    (by
      intro x y hxy
      exact Subtype.ext hxy)

theorem nonzeroRationalVectorOrbitNorm_bijective
    (V : RationalQuadraticSpaceMatrix n) :
    Function.Bijective V.nonzeroRationalVectorOrbitNorm := by
  constructor
  · intro u v huv
    induction u using Quotient.inductionOn with
    | _ x =>
        induction v using Quotient.inductionOn with
        | _ y =>
            apply Quotient.sound
            exact congrArg Subtype.val huv
  · rintro ⟨a, ha, x, hx⟩
    let x' : V.AnisotropicRationalVector := ⟨x, by simpa [hx] using ha⟩
    refine ⟨Quotient.mk V.anisotropicRationalVectorNormSetoid x', ?_⟩
    apply Subtype.ext
    exact hx

/-- The canonical equivalence between the rational orbit quotient and the
subtype of represented nonzero norms.  Its inverse returns only a quotient
class, never a chosen rational vector. -/
def nonzeroRationalVectorOrbitEquivRepresentedNorm
    (V : RationalQuadraticSpaceMatrix n) :
    V.NonzeroRationalVectorOrbit ≃ V.RepresentedNonzeroRationalNorm :=
  Equiv.ofBijective V.nonzeroRationalVectorOrbitNorm
    V.nonzeroRationalVectorOrbitNorm_bijective

/-- The literal rational-vector fiber above a represented nonzero norm. -/
def RepresentedNonzeroRationalNorm.rationalVectorFiber
    (V : RationalQuadraticSpaceMatrix n)
    (a : V.RepresentedNonzeroRationalNorm) :=
  {x : Fin n → ℚ // V.nativeRationalQuadraticForm x = a.1}

/-- Section-free partition of all nonisotropic rational vectors into the
literal fibers of their represented norms. -/
def anisotropicRationalVectorEquivSigmaRepresentedNormFiber
    (V : RationalQuadraticSpaceMatrix n) :
    V.AnisotropicRationalVector ≃
      (a : V.RepresentedNonzeroRationalNorm) ×
        a.rationalVectorFiber V where
  toFun x :=
    ⟨⟨V.nativeRationalQuadraticForm x.1, x.2, ⟨x.1, rfl⟩⟩,
      ⟨x.1, rfl⟩⟩
  invFun p := ⟨p.2.1, by rw [p.2.2]; exact p.1.2.1⟩
  left_inv x := by
    exact Subtype.ext rfl
  right_inv p := by
    rcases p with ⟨⟨a, ha⟩, ⟨x, hx⟩⟩
    change V.nativeRationalQuadraticForm x = a at hx
    cases hx
    rfl

/-- Tonelli-ready reindexing of a nonnegative rational-vector sum by the
literal countable represented-norm index and its rational fibers. -/
theorem tsum_anisotropicRationalVector_eq_representedNorm_fibers
    (V : RationalQuadraticSpaceMatrix n)
    (F : V.AnisotropicRationalVector → ℝ≥0∞) :
    (∑' x, F x) =
      ∑' a : V.RepresentedNonzeroRationalNorm,
        ∑' x : a.rationalVectorFiber V,
          F ((V.anisotropicRationalVectorEquivSigmaRepresentedNormFiber).symm
            ⟨a, x⟩) := by
  let e := V.anisotropicRationalVectorEquivSigmaRepresentedNormFiber
  calc
    (∑' x, F x) = ∑' p, F (e.symm p) := by
      exact (e.symm.tsum_eq F).symm
    _ = ∑' a : V.RepresentedNonzeroRationalNorm,
        ∑' x : a.rationalVectorFiber V, F (e.symm ⟨a, x⟩) := by
      exact ENNReal.tsum_sigma' (fun p ↦ F (e.symm p))

namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- The algebraic group/orbit/shell square over every rational algebra. -/
theorem blockToAmbientShellEquiv_orbit
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A) :
    P.blockToAmbientShellEquiv hx A
        (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
          P.lowerSpace (V.nativeRationalQuadraticForm x) hx A z) =
      V.anisotropicRationalAmbientShellOrbitMap x A
        (P.blockToAmbientGeneralSpinIntrinsicPoint A hx z) := by
  apply Subtype.ext
  change P.blockToAmbientBaseChangeIsometryEquiv hx A
      (Matrix.mulVec z.matrixPoint.1 lastCoordinateVector) =
    Matrix.mulVec
      (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx z.matrixPoint).1
      (fun i ↦ algebraMap ℚ A (x i))
  rw [← P.blockToAmbientShellEquiv_lastCoordinateVector hx A]
  exact P.blockToAmbientBaseChangeIsometryEquiv_specialOrthogonal_mulVec
    hx A z.matrixPoint lastCoordinateVector

/-- Any supplied positive-rank complement presentation realizes the entire
ambient rational-algebra shell as one intrinsic `GSpin` orbit. -/
theorem anisotropicRationalAmbientShellOrbitMap_surjective
    (P : V.AnisotropicComplementPresentation x m)
    [NeZero m] (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [Field A] [CharZero A] [Algebra ℚ A] :
    Function.Surjective (V.anisotropicRationalAmbientShellOrbitMap x A) := by
  intro y
  let yBlock := (P.blockToAmbientShellEquiv hx A).symm y
  obtain ⟨z, hz⟩ :=
    CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_surjective
      P.lowerSpace (V.nativeRationalQuadraticForm x) hx A yBlock
  refine ⟨P.blockToAmbientGeneralSpinIntrinsicPoint A hx z, ?_⟩
  rw [← P.blockToAmbientShellEquiv_orbit hx A z, hz]
  exact (P.blockToAmbientShellEquiv hx A).apply_symm_apply y

/-- Equality of nonzero rational norms is exactly rational intrinsic `GSpin`
orbit equivalence once any complement presentation at the source is supplied.
The public statement chooses no orbit representative. -/
theorem nativeRationalQuadraticForm_eq_iff_exists_generalSpin_mulVec
    (P : V.AnisotropicComplementPresentation x m)
    [NeZero m] (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (y : Fin n → ℚ) :
    V.nativeRationalQuadraticForm y =
        V.nativeRationalQuadraticForm x ↔
      ∃ z : V.CliffordGeneralSpinIntrinsicPoint ℚ,
        Matrix.mulVec z.matrixPoint.1 x = y := by
  constructor
  · intro hy
    let yShell : V.anisotropicRationalAmbientShell x ℚ := ⟨y, by
      change V.nativeRationalQuadraticForm y =
        V.nativeRationalQuadraticForm x
      exact hy⟩
    obtain ⟨z, hz⟩ :=
      P.anisotropicRationalAmbientShellOrbitMap_surjective hx ℚ yShell
    refine ⟨z, ?_⟩
    exact congrArg Subtype.val hz
  · rintro ⟨z, rfl⟩
    exact (V.anisotropicRationalAmbientShellOrbitMap x ℚ z).2

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

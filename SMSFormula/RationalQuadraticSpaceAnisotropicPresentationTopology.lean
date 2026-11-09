import SMSFormula.RationalQuadraticSpaceAnisotropicPresentation

/-!
# Native topology for presentation-parametric anisotropic shell maps

A supplied anisotropic-complement presentation already gives a linear
equivalence on every native finite coordinate carrier.  This file proves that
equivalence and its shell restriction are homeomorphisms for the existing
product and subtype topologies whenever the coefficient algebra is a
topological ring.

The topology is never transported through the presentation.  Continuity is
proved directly by expanding a vector as the finite sum of its standard
coordinate vectors.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}

namespace AnisotropicComplementPresentation

variable (P : V.AnisotropicComplementPresentation x m)

private theorem continuous_linearMap_pi
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {r s : ℕ} (f : (Fin r → A) →ₗ[A] (Fin s → A)) :
    Continuous f := by
  have hfun : (fun y ↦ f y) =
      fun y ↦ ∑ i, y i • f (Pi.single i (1 : A)) := by
    funext y
    calc
      f y = f (∑ i, y i • (Pi.single i (1 : A) : Fin r → A)) := by
        rw [commutativeScalarExtension_single_sum A y]
      _ = ∑ i, y i • f (Pi.single i (1 : A)) := by
        simp
  change Continuous (fun y ↦ f y)
  rw [hfun]
  fun_prop

/-- The scalar-extended block-to-ambient equivalence is continuous for the
native finite product topologies. -/
theorem continuous_blockToAmbientBaseChangeIsometryEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (P.blockToAmbientBaseChangeIsometryEquiv hx A) :=
  continuous_linearMap_pi
    (P.blockToAmbientBaseChangeIsometryEquiv hx A).toLinearEquiv.toLinearMap

/-- The inverse scalar-extended map is continuous for the same native product
topologies. -/
theorem continuous_blockToAmbientBaseChangeIsometryEquiv_symm
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (P.blockToAmbientBaseChangeIsometryEquiv hx A).symm :=
  continuous_linearMap_pi
    (P.blockToAmbientBaseChangeIsometryEquiv hx A).symm.toLinearEquiv.toLinearMap

/-- The supplied presentation gives a homeomorphism between the native block
and ambient coordinate carriers.  Both sides carry their product topologies. -/
def blockToAmbientBaseChangeHomeomorph
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    (Fin (m + 1) → A) ≃ₜ (Fin n → A) where
  toEquiv :=
    (P.blockToAmbientBaseChangeIsometryEquiv hx A).toLinearEquiv.toEquiv
  continuous_toFun :=
    P.continuous_blockToAmbientBaseChangeIsometryEquiv hx A
  continuous_invFun :=
    P.continuous_blockToAmbientBaseChangeIsometryEquiv_symm hx A

@[simp]
theorem blockToAmbientBaseChangeHomeomorph_apply
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (y : Fin (m + 1) → A) :
    P.blockToAmbientBaseChangeHomeomorph hx A y =
      P.blockToAmbientBaseChangeIsometryEquiv hx A y :=
  rfl

/-- Restriction of the native coordinate homeomorphism to the existing block
and ambient shell subtypes. -/
def blockToAmbientShellHomeomorph
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    P.lowerSpace.nonisotropicLastQuadraticShell
        (V.nativeRationalQuadraticForm x) hx A ≃ₜ
      V.anisotropicRationalAmbientShell x A where
  toEquiv := P.blockToAmbientShellEquiv hx A
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact
      (P.continuous_blockToAmbientBaseChangeIsometryEquiv hx A).comp
        continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact
      (P.continuous_blockToAmbientBaseChangeIsometryEquiv_symm hx A).comp
        continuous_subtype_val

@[simp]
theorem coe_blockToAmbientShellHomeomorph
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (y : P.lowerSpace.nonisotropicLastQuadraticShell
      (V.nativeRationalQuadraticForm x) hx A) :
    (P.blockToAmbientShellHomeomorph hx A y).1 =
      P.blockToAmbientBaseChangeIsometryEquiv hx A y :=
  rfl

/-- The native homeomorphism sends the block last-coordinate point to its
certified rational-diagonal image. -/
@[simp]
theorem blockToAmbientShellHomeomorph_lastCoordinateVector
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    (P.blockToAmbientShellHomeomorph hx A
      ⟨lastCoordinateVector,
        P.lowerSpace.lastCoordinateVector_mem_nonisotropicLastQuadraticShell
          (V.nativeRationalQuadraticForm x) hx A⟩).1 =
      fun i ↦ algebraMap ℚ A (x i) :=
  P.blockToAmbientShellEquiv_lastCoordinateVector hx A

/-- The native shell map is measurable for the existing Borel structures. -/
theorem measurable_blockToAmbientShellHomeomorph
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] [MeasurableSpace A]
    [BorelSpace A] [SecondCountableTopology A] :
    Measurable (P.blockToAmbientShellHomeomorph hx A) :=
  (P.blockToAmbientShellHomeomorph hx A).continuous.measurable

/-- The inverse native shell map is measurable for the same Borel
structures. -/
theorem measurable_blockToAmbientShellHomeomorph_symm
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] [MeasurableSpace A]
    [BorelSpace A] [SecondCountableTopology A] :
    Measurable (P.blockToAmbientShellHomeomorph hx A).symm :=
  (P.blockToAmbientShellHomeomorph hx A).symm.continuous.measurable

end AnisotropicComplementPresentation

end RationalQuadraticSpaceMatrix

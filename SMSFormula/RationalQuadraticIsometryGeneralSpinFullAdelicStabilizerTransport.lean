import SMSFormula.RationalQuadraticIsometryGeneralSpinFullAdelicShellOrbitTransport

/-!
# Full-adelic stabilizer transport across a supplied presentation

The ambient stabilizer is defined intrinsically as the `GSpin` subgroup whose
represented special-orthogonal matrix fixes the rational diagonal of the
given anisotropic vector.  The closed orbit square identifies it exactly with
the image of the native complement stabilizer under the existing full-adelic
presentation equivalence.

The restricted equivalence is continuous and the ambient subgroup is closed.
No stabilizer Haar measure, orbit-fiber kernel, quotient or shell measure,
chosen representative, new chart, scalar comparison, cutoff, or Tamagawa
theorem is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance ambientStabilizerTransportInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance ambientStabilizerTransportFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance ambientStabilizerTransportT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

/-- The rational diagonal point in the ambient shell. -/
def anisotropicRationalAmbientShellBasepoint
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    V.anisotropicRationalAmbientShell x A := by
  refine ⟨fun i ↦ algebraMap ℚ A (x i), ?_⟩
  exact V.commutativeScalarExtensionQuadraticForm_map ℚ (Algebra.ofId ℚ A) x

/-- The intrinsic ambient `GSpin` subgroup fixing the rational diagonal of
`x`. -/
def anisotropicRationalAmbientGeneralSpinStabilizerSubgroup
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Subgroup (V.CliffordGeneralSpinIntrinsicPoint A) where
  carrier := {z | Matrix.mulVec z.matrixPoint.1
    (fun i ↦ algebraMap ℚ A (x i)) = fun i ↦ algebraMap ℚ A (x i)}
  one_mem' := by
    change Matrix.mulVec (1 : V.CliffordGeneralSpinIntrinsicPoint A).matrixPoint.1
      (fun i ↦ algebraMap ℚ A (x i)) = fun i ↦ algebraMap ℚ A (x i)
    rw [← CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe]
    rw [CliffordGeneralSpinIntrinsicPoint.one_matrixGroup]
    exact Matrix.one_mulVec _
  mul_mem' := by
    intro g h hg hh
    change Matrix.mulVec (g * h).matrixPoint.1
      (fun i ↦ algebraMap ℚ A (x i)) = fun i ↦ algebraMap ℚ A (x i)
    change Matrix.mulVec g.matrixPoint.1 _ = _ at hg
    change Matrix.mulVec h.matrixPoint.1 _ = _ at hh
    calc
      Matrix.mulVec (g * h).matrixPoint.1
          (fun i ↦ algebraMap ℚ A (x i)) =
          Matrix.mulVec g.matrixPoint.1
            (Matrix.mulVec h.matrixPoint.1
              (fun i ↦ algebraMap ℚ A (x i))) := by
        rw [Matrix.mulVec_mulVec]
        congr 1
      _ = fun i ↦ algebraMap ℚ A (x i) := by rw [hh, hg]
  inv_mem' := by
    intro g hg
    change Matrix.mulVec g⁻¹.matrixPoint.1
      (fun i ↦ algebraMap ℚ A (x i)) = fun i ↦ algebraMap ℚ A (x i)
    change Matrix.mulVec g.matrixPoint.1 _ = _ at hg
    calc
      Matrix.mulVec g⁻¹.matrixPoint.1 (fun i ↦ algebraMap ℚ A (x i)) =
          Matrix.mulVec g⁻¹.matrixPoint.1
            (Matrix.mulVec g.matrixPoint.1 (fun i ↦ algebraMap ℚ A (x i))) :=
        congrArg (Matrix.mulVec g⁻¹.matrixPoint.1) hg.symm
      _ = Matrix.mulVec (g⁻¹ * g).matrixPoint.1
          (fun i ↦ algebraMap ℚ A (x i)) := by
        rw [Matrix.mulVec_mulVec]
        congr 1
      _ = fun i ↦ algebraMap ℚ A (x i) := by
        rw [inv_mul_cancel]
        change Matrix.mulVec
            (1 : V.CliffordGeneralSpinIntrinsicPoint A).matrixPoint.1
          (fun i ↦ algebraMap ℚ A (x i)) = fun i ↦ algebraMap ℚ A (x i)
        rw [← CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe]
        rw [CliffordGeneralSpinIntrinsicPoint.one_matrixGroup]
        exact Matrix.one_mulVec _

/-- Membership in the intrinsic ambient stabilizer is exactly equality of the
ambient shell orbit with the rational-diagonal basepoint. -/
theorem mem_anisotropicRationalAmbientGeneralSpinStabilizerSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n) (x : Fin n → ℚ)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (z : V.CliffordGeneralSpinIntrinsicPoint A) :
    z ∈ V.anisotropicRationalAmbientGeneralSpinStabilizerSubgroup x A ↔
      V.anisotropicRationalAmbientShellOrbitMap x A z =
        V.anisotropicRationalAmbientShellBasepoint x A := by
  change Matrix.mulVec z.matrixPoint.1 _ = _ ↔ _
  rw [Subtype.ext_iff]
  rfl

namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- Presentation transport belongs to the intrinsic ambient stabilizer if
and only if the source belongs to the native complement stabilizer. -/
theorem blockToAmbientFullAdelicGeneralSpin_mem_stabilizer_iff
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup) :
    P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx z ∈
        V.anisotropicRationalAmbientGeneralSpinStabilizerSubgroup
          x RationalAdele ↔
      z ∈ P.lowerSpace.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        (V.nativeRationalQuadraticForm x) hx RationalAdele := by
  rw [V.mem_anisotropicRationalAmbientGeneralSpinStabilizerSubgroup_iff]
  rw [← P.blockToAmbientShellHomeomorph_fullAdelic_orbit hx z]
  rw [show V.anisotropicRationalAmbientShellBasepoint x RationalAdele =
      P.blockToAmbientShellHomeomorph hx RationalAdele
        ⟨lastCoordinateVector,
          P.lowerSpace.lastCoordinateVector_mem_nonisotropicLastQuadraticShell
            (V.nativeRationalQuadraticForm x) hx RationalAdele⟩ by
    apply Subtype.ext
    exact (P.blockToAmbientShellHomeomorph_lastCoordinateVector
      hx RationalAdele).symm]
  rw [(P.blockToAmbientShellHomeomorph hx RationalAdele).injective.eq_iff]
  exact
    CliffordGeneralSpinIntrinsicPoint.fullAdelic_nonisotropicLastShellOrbitMap_eq_last_iff
      P.lowerSpace (V.nativeRationalQuadraticForm x) hx z

/-- The image of the native complement stabilizer is exactly the intrinsic
ambient stabilizer of the rational diagonal. -/
theorem map_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.lowerSpace.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        (V.nativeRationalQuadraticForm x) hx RationalAdele).map
      (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).toMonoidHom =
      V.anisotropicRationalAmbientGeneralSpinStabilizerSubgroup
        x RationalAdele := by
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (P.blockToAmbientFullAdelicGeneralSpin_mem_stabilizer_iff hx z).2 hz
  · intro hg
    let z := (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).symm g
    refine ⟨z, ?_,
      (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).apply_symm_apply g⟩
    apply (P.blockToAmbientFullAdelicGeneralSpin_mem_stabilizer_iff hx z).1
    rw [(P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).apply_symm_apply]
    exact hg

/-- The full-adelic presentation restricted to the exact native and ambient
stabilizers. -/
def blockToAmbientFullAdelicGeneralSpinStabilizerContinuousMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    P.lowerSpace.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        (V.nativeRationalQuadraticForm x) hx RationalAdele ≃ₜ*
      V.anisotropicRationalAmbientGeneralSpinStabilizerSubgroup
        x RationalAdele := by
  let E := P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx
  let e :
      P.lowerSpace.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
          (V.nativeRationalQuadraticForm x) hx RationalAdele ≃
        V.anisotropicRationalAmbientGeneralSpinStabilizerSubgroup
          x RationalAdele := {
    toFun z := ⟨E z.1,
      (P.blockToAmbientFullAdelicGeneralSpin_mem_stabilizer_iff hx z.1).2 z.2⟩
    invFun g := ⟨E.symm g.1,
      (P.blockToAmbientFullAdelicGeneralSpin_mem_stabilizer_iff hx
        (E.symm g.1)).1 (by rw [E.apply_symm_apply]; exact g.2)⟩
    left_inv z := Subtype.ext (E.symm_apply_apply z.1)
    right_inv g := Subtype.ext (E.apply_symm_apply g.1) }
  exact ContinuousMulEquiv.mk'
    { toEquiv := e
      continuous_toFun := Continuous.subtype_mk
        (E.continuous.comp continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk
        (E.symm.continuous.comp continuous_subtype_val) _ }
    (fun g h ↦ Subtype.ext (E.map_mul g.1 h.1))

@[simp]
theorem coe_blockToAmbientFullAdelicGeneralSpinStabilizerContinuousMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (z : P.lowerSpace.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      (V.nativeRationalQuadraticForm x) hx RationalAdele) :
    (P.blockToAmbientFullAdelicGeneralSpinStabilizerContinuousMulEquiv hx z).1 =
      P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx z.1 :=
  rfl

@[simp]
theorem coe_blockToAmbientFullAdelicGeneralSpinStabilizerContinuousMulEquiv_symm
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (g : V.anisotropicRationalAmbientGeneralSpinStabilizerSubgroup
      x RationalAdele) :
    ((P.blockToAmbientFullAdelicGeneralSpinStabilizerContinuousMulEquiv hx).symm
      g).1 =
      (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).symm g.1 :=
  rfl

include P

/-- The intrinsic ambient full-adelic stabilizer is closed whenever the
supplied anisotropic complement presentation is available. -/
theorem isClosed_anisotropicRationalAmbientGeneralSpinStabilizerSubgroup
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    IsClosed (V.anisotropicRationalAmbientGeneralSpinStabilizerSubgroup
      x RationalAdele : Set V.FullAdelicCliffordGeneralSpinGroup) := by
  rw [← map_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    (P := P) hx]
  change IsClosed
    ((P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx) ''
      (P.lowerSpace.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        (V.nativeRationalQuadraticForm x) hx RationalAdele :
          Set (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup))
  exact (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).isClosedMap _
    (P.lowerSpace.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      (V.nativeRationalQuadraticForm x) hx RationalAdele)

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

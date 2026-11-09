import SMSFormula.RationalQuadraticIsometryGeneralSpinFullAdelicStabilizerTransport
import SMSFormula.RationalCliffordGeneralSpinBlockFullAdelicStabilizerHaar
import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellMeasurableWeil

/-!
# Full-adelic orbit-fiber kernel transport across a supplied presentation

The native block-shell kernel is transported through the existing shell and
group homeomorphisms.  Its value on every ambient orbit is then identified
with right-translation of the directly transported ambient stabilizer Haar.
The stabilizer scalar is literally one.

No quotient or shell measure, chosen representative, new chart, cutoff, or
Tamagawa theorem is asserted here.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice
open ProbabilityTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance ambientOrbitFiberKernelTransportInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance ambientOrbitFiberKernelTransportFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance ambientOrbitFiberKernelTransportT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

noncomputable local instance ambientOrbitFiberKernelTransportBlockGroupMeasurableSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    MeasurableSpace (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup :=
  P.lowerSpace.fullAdelicShellMeasurableWeilSourceMeasurableSpace
    (V.nativeRationalQuadraticForm x) hx

noncomputable local instance ambientOrbitFiberKernelTransportBlockGroupBorelSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    BorelSpace (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup :=
  P.lowerSpace.fullAdelicShellMeasurableWeilSourceBorelSpace
    (V.nativeRationalQuadraticForm x) hx

noncomputable local instance ambientOrbitFiberKernelTransportBlockShellMeasurableSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
      (V.nativeRationalQuadraticForm x) hx RationalAdele) :=
  P.lowerSpace.fullAdelicShellMeasurableWeilTargetMeasurableSpace
    (V.nativeRationalQuadraticForm x) hx

noncomputable local instance ambientOrbitFiberKernelTransportBlockShellBorelSpace
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
      (V.nativeRationalQuadraticForm x) hx RationalAdele) :=
  P.lowerSpace.fullAdelicShellMeasurableWeilTargetBorelSpace
    (V.nativeRationalQuadraticForm x) hx

noncomputable local instance ambientOrbitFiberKernelTransportAmbientGroupMeasurableSpace :
    MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance ambientOrbitFiberKernelTransportAmbientGroupBorelSpace :
    BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance ambientOrbitFiberKernelTransportAmbientShellMeasurableSpace :
    MeasurableSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  borel _

noncomputable local instance ambientOrbitFiberKernelTransportAmbientShellBorelSpace :
    BorelSpace (V.anisotropicRationalAmbientShell x RationalAdele) :=
  ⟨rfl⟩

/-- The ambient-shell orbit-fiber kernel obtained from the native kernel by
the certified shell and group presentation homeomorphisms. -/
noncomputable def anisotropicRationalAmbientShellOrbitFiberKernel
    [NeZero m] (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Kernel (V.anisotropicRationalAmbientShell x RationalAdele)
      V.FullAdelicCliffordGeneralSpinGroup :=
  Kernel.map
    (Kernel.comap
      (P.lowerSpace.fullAdelicNonisotropicLastShellOrbitFiberKernel
        (V.nativeRationalQuadraticForm x) hx)
      (P.blockToAmbientShellHomeomorph hx RationalAdele).symm
      (P.blockToAmbientShellHomeomorph hx RationalAdele).symm.continuous.measurable)
    (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)

/-- Pointwise exact square for the native and ambient shell kernels. -/
theorem anisotropicRationalAmbientShellOrbitFiberKernel_apply_homeomorph
    [NeZero m] (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (y : P.lowerSpace.nonisotropicLastQuadraticShell
      (V.nativeRationalQuadraticForm x) hx RationalAdele) :
    P.anisotropicRationalAmbientShellOrbitFiberKernel hx
        (P.blockToAmbientShellHomeomorph hx RationalAdele y) =
      Measure.map
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)
        (P.lowerSpace.fullAdelicNonisotropicLastShellOrbitFiberKernel
          (V.nativeRationalQuadraticForm x) hx y) := by
  rw [anisotropicRationalAmbientShellOrbitFiberKernel,
    Kernel.map_apply _
      (P.measurable_blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx),
    Kernel.comap_apply]
  rw [(P.blockToAmbientShellHomeomorph hx RationalAdele).symm_apply_apply]

/-- The complete presentation square is an equality of kernels. -/
theorem comap_anisotropicRationalAmbientShellOrbitFiberKernel_eq_map
    [NeZero m] (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Kernel.comap
        (P.anisotropicRationalAmbientShellOrbitFiberKernel hx)
        (P.blockToAmbientShellHomeomorph hx RationalAdele)
        (P.blockToAmbientShellHomeomorph hx RationalAdele).continuous.measurable =
      Kernel.map
        (P.lowerSpace.fullAdelicNonisotropicLastShellOrbitFiberKernel
          (V.nativeRationalQuadraticForm x) hx)
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx) := by
  apply Kernel.ext
  intro y
  rw [Kernel.comap_apply, Kernel.map_apply _
    (P.measurable_blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx)]
  exact P.anisotropicRationalAmbientShellOrbitFiberKernel_apply_homeomorph hx y

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

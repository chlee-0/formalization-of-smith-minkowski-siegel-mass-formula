import SMSFormula.RationalIdeleModule
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Continuity of the rational idele module

The finite module is locally constant: the open subgroup of ideles integral
together with their inverses is contained in its kernel.  The full module is
then continuous through the literal real--finite splitting, and so is its
logarithm.  These are the topological inputs for the compact crossed cutoff.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Topology

namespace RationalQuadraticSpaceMatrix

/-- Finite ideles integral together with their inverses. -/
def integralFiniteIdeleUnits : Set RationalFiniteAdeleˣ :=
  {a | (a : RationalFiniteAdele) ∈ integralFiniteAdeleSubring ∧
    ((a⁻¹ : RationalFiniteAdeleˣ) : RationalFiniteAdele) ∈
      integralFiniteAdeleSubring}

theorem isOpen_integralFiniteIdeleUnits : IsOpen integralFiniteIdeleUnits := by
  apply IsOpen.inter
  · exact isOpen_integralFiniteAdeleSubring.preimage Units.continuous_val
  · exact isOpen_integralFiniteAdeleSubring.preimage
      (Units.continuous_val.comp continuous_inv)

theorem one_mem_integralFiniteIdeleUnits :
    (1 : RationalFiniteAdeleˣ) ∈ integralFiniteIdeleUnits := by
  exact ⟨integralFiniteAdeleSubring.one_mem,
    integralFiniteAdeleSubring.one_mem⟩

theorem finiteIdeleModuleNNReal_eq_one_of_mem_integralFiniteIdeleUnits
    (a : RationalFiniteAdeleˣ) (ha : a ∈ integralFiniteIdeleUnits) :
    finiteIdeleModuleNNReal a = 1 := by
  rw [finiteIdeleModuleNNReal_eq_prod_of_eq_one_outside a ∅]
  · simp
  · intro v hv
    apply nnnorm_finiteAdelicUnitHeightOneComponent_eq_one_of_not_mem
    rw [not_mem_finiteIdeleNormSupport_iff]
    exact ⟨ha.1 v, ha.2 v⟩

theorem isLocallyConstant_finiteIdeleModuleNNReal :
    IsLocallyConstant finiteIdeleModuleNNReal := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a
  let U : Set RationalFiniteAdeleˣ :=
    (fun b => a⁻¹ * b) ⁻¹' integralFiniteIdeleUnits
  have hUopen : IsOpen U :=
    isOpen_integralFiniteIdeleUnits.preimage
      (continuous_const.mul continuous_id)
  have haU : a ∈ U := by
    change a⁻¹ * a ∈ integralFiniteIdeleUnits
    simpa using one_mem_integralFiniteIdeleUnits
  filter_upwards [hUopen.mem_nhds haU] with b hb
  have hkernel : finiteIdeleModuleNNReal (a⁻¹ * b) = 1 :=
    finiteIdeleModuleNNReal_eq_one_of_mem_integralFiniteIdeleUnits _ hb
  calc
    finiteIdeleModuleNNReal b =
        finiteIdeleModuleNNReal (a * (a⁻¹ * b)) := by simp
    _ = finiteIdeleModuleNNReal a *
        finiteIdeleModuleNNReal (a⁻¹ * b) :=
      finiteIdeleModuleNNReal_mul _ _
    _ = finiteIdeleModuleNNReal a := by rw [hkernel, mul_one]

theorem continuous_finiteIdeleModuleNNReal :
    Continuous finiteIdeleModuleNNReal :=
  isLocallyConstant_finiteIdeleModuleNNReal.continuous

theorem continuous_rationalIdeleModuleNNReal :
    Continuous rationalIdeleModuleNNReal := by
  unfold rationalIdeleModuleNNReal
  apply Continuous.mul
  · exact (continuous_nnnorm.comp
      (Units.continuous_val.comp
        (continuous_fst.comp
          rationalAdeleUnitsRealFiniteContinuousEquiv.continuous)))
  · exact continuous_finiteIdeleModuleNNReal.comp
      (continuous_snd.comp
        rationalAdeleUnitsRealFiniteContinuousEquiv.continuous)

theorem continuous_rationalIdeleLogModule :
    Continuous rationalIdeleLogModule := by
  unfold rationalIdeleLogModule
  exact (NNReal.continuous_coe.comp
      continuous_rationalIdeleModuleNNReal).log
    (fun a => NNReal.coe_ne_zero.mpr
      (rationalIdeleModuleNNReal_ne_zero a))

end RationalQuadraticSpaceMatrix

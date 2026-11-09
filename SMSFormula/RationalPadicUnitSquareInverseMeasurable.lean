import SMSFormula.RationalPadicUnitSquareAdditiveSubstitution

noncomputable section

open Set Topology MeasureTheory

namespace Rat

variable (prime : ℕ) [Fact prime.Prime]

local instance : MeasurableSpace ℚ_[prime] := borel _
local instance : BorelSpace ℚ_[prime] := ⟨rfl⟩
local instance : MeasurableSpace ℚ_[prime]ˣ := borel _
local instance : BorelSpace ℚ_[prime]ˣ := ⟨rfl⟩

def padicUnitSquareScalarTarget : Set ℚ_[prime] :=
  Units.val '' (unitSquareIdentityChart ℚ_[prime]).target

theorem isOpen_padicUnitSquareScalarTarget : IsOpen (padicUnitSquareScalarTarget prime) :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℚ_[prime])).isOpenMap _
    (unitSquareIdentityChart ℚ_[prime]).open_target

theorem continuousOn_padicUnitSquareScalarInverse :
    ContinuousOn (padicUnitSquareScalarInverse prime) (padicUnitSquareScalarTarget prime) := by
  let chart := unitSquareIdentityChart ℚ_[prime]
  have hnonzero (value : padicUnitSquareScalarTarget prime) : (value : ℚ_[prime]) ≠ 0 := by
    obtain ⟨unit, _, hunit⟩ := value.property
    exact hunit ▸ unit.ne_zero
  let lift : padicUnitSquareScalarTarget prime → chart.target := fun value ↦
    ⟨Units.mk0 (value : ℚ_[prime]) (hnonzero value), by
      obtain ⟨unit, hunit, heq⟩ := value.property
      have hequal : Units.mk0 (value : ℚ_[prime]) (hnonzero value) = unit := Units.ext heq.symm
      rwa [hequal]⟩
  have hembedding := ((IsOpenUnits.isOpenEmbedding_unitsVal (M := ℚ_[prime])).comp
    chart.open_target.isOpenEmbedding_subtypeVal).isEmbedding
  have hlift : Continuous lift := hembedding.continuous_iff.mpr (by
    change Continuous (fun value : padicUnitSquareScalarTarget prime ↦ (value : ℚ_[prime]))
    exact continuous_subtype_val)
  have hinverse : Continuous (fun value : padicUnitSquareScalarTarget prime ↦
      (((chart.toHomeomorphSourceTarget.symm (lift value) : chart.source) : ℚ_[prime]ˣ) : ℚ_[prime])) :=
    Units.continuous_val.comp (continuous_subtype_val.comp
      (chart.toHomeomorphSourceTarget.symm.continuous.comp hlift))
  apply continuousOn_iff_continuous_restrict.mpr
  convert hinverse using 1
  funext value
  simp only [Set.restrict_apply, padicUnitSquareScalarInverse, dif_pos (hnonzero value)]
  rfl

def padicUnitSquareTargetSupportedInverse : ℚ_[prime] → ℚ_[prime] :=
  (padicUnitSquareScalarTarget prime).indicator (padicUnitSquareScalarInverse prime)

theorem measurable_padicUnitSquareTargetSupportedInverse :
    Measurable (padicUnitSquareTargetSupportedInverse prime) := by
  classical
  exact (continuousOn_padicUnitSquareScalarInverse prime).measurable_piecewise
    continuous_const.continuousOn (isOpen_padicUnitSquareScalarTarget prime).measurableSet

theorem padicUnitSquareTargetSupportedInverse_eq {value : ℚ_[prime]}
    (hvalue : value ∈ padicUnitSquareScalarTarget prime) :
    padicUnitSquareTargetSupportedInverse prime value = padicUnitSquareScalarInverse prime value :=
  Set.indicator_of_mem hvalue _

theorem mem_padicUnitSquareScalarAffineTarget_iff
    (offset coefficient : ℚ_[prime]) (hcoefficient : coefficient ≠ 0) (value : ℚ_[prime]) :
    value ∈ (fun unit : ℚ_[prime]ˣ ↦ offset + coefficient * (unit : ℚ_[prime])) ''
      (unitSquareIdentityChart ℚ_[prime]).target ↔
      (value - offset) / coefficient ∈ padicUnitSquareScalarTarget prime := by
  constructor
  · rintro ⟨unit, hunit, rfl⟩
    refine ⟨unit, hunit, ?_⟩
    field_simp
    ring
  · rintro ⟨unit, hunit, heq⟩
    refine ⟨unit, hunit, ?_⟩
    dsimp only
    rw [heq]
    field_simp
    ring

end Rat

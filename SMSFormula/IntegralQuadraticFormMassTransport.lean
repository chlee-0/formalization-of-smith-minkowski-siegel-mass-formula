import SMSFormula.IntegralQuadraticFormGenusMass
import SMSFormula.RationalSpecialOrthogonalMassFormula
import SMSFormula.RationalSpecialOrthogonalNormalizedOrdinaryMass

/-!
# Transparent mass transport through the scaled integral integral model

This is an explicitly transported endpoint.  Its genus, mass, local-product
predicate, and product side are those of `H.latticeOfPolarForm`, which
represents `2Q_H`.  The quadratic form `Q_H` itself is integral; only its
representing symmetric matrix is half-integral.  This is not
the direct local-density formula for `Q_H`.
-/

noncomputable section

open scoped ENNReal

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ} (H : PositiveDefiniteIntegralQuadraticForm n)

/-! ## Finite direct automorphism types -/

noncomputable instance properIsometryGroup_fintype :
    Fintype H.ProperIsometryGroup :=
  Fintype.ofEquiv H.latticeOfPolarForm.ProperIsometryGroup
    H.properIsometryGroupEquivLatticeOfPolarForm.symm

/-- The direct and integral model ordinary automorphism cardinalities agree, after the
literal carrier equivalence has been constructed. -/
theorem isometryGroup_card_eq_latticeOfPolarForm :
    Fintype.card H.IsometryGroup =
      Fintype.card H.latticeOfPolarForm.IsometryGroup :=
  Fintype.card_congr H.isometryGroupEquivLatticeOfPolarForm

/-- The direct and integral model proper automorphism cardinalities agree. -/
theorem properIsometryGroup_card_eq_latticeOfPolarForm :
    Fintype.card H.ProperIsometryGroup =
      Fintype.card H.latticeOfPolarForm.ProperIsometryGroup :=
  Fintype.card_congr H.properIsometryGroupEquivLatticeOfPolarForm

/-! ## Transparently transported genus and mass -/

/-- The genus index set transported from the scaled integral integral model. -/
def polarFormLatticeGenus := H.latticeOfPolarForm.genus

/-- The transported integral model genus is finite by the existing genus
finiteness theorem. -/
theorem polarFormLatticeGenus_finite : H.polarFormLatticeGenus.Finite := by
  exact H.latticeOfPolarForm.genus_finite

/-- The ordinary genus mass of an integral quadratic form `H`, transported from
its scaled integral model: the ordinary genus mass of
`H.latticeOfPolarForm`, the integral lattice representing `2Q_H`.  The
automorphism groups of `H` and its integral model are identified
(`isometryGroup_card_eq_latticeOfPolarForm`), but this definition is not,
by itself, a class sum over a genus of `Q_H`. -/
def transportedOrdinaryGenusMass : ℚ :=
  H.latticeOfPolarForm.ordinaryGenusMass

/-- The direct Q-class sum equals the transported definition.
This is a proved comparison, not definitional equality. -/
theorem ordinaryGenusMass_eq_transportedOrdinaryGenusMass :
    H.ordinaryGenusMass = H.transportedOrdinaryGenusMass :=
  H.ordinaryGenusMass_eq_latticeOfPolarForm

/-- The `ordinaryClassSOStabilizerMass` of the scaled integral model.  That
quantity is indexed by ordinary `O`-genus classes and uses `SO` stabilizers; it
is not the proper-class mass `properClassGenusMass`. -/
def transportedOrdinaryClassSOStabilizerMass : ℚ :=
  H.latticeOfPolarForm.ordinaryClassSOStabilizerMass

/-- The local inverse-product convergence predicate of the scaled integral model. -/
def polarFormLatticeMassLocalInverseProductTendsTo (P : ℝ) : Prop :=
  PositiveDefiniteIntegralLattice.massLocalInverseProductTendsTo
    H.latticeOfPolarForm P

/-- The Schulze--Pillot product side of the scaled integral model. -/
def polarFormLatticeMassFormulaProductSide (P : ℝ) : ℝ :=
  PositiveDefiniteIntegralLattice.massFormulaProductSide
    H.latticeOfPolarForm P

/-! ## Transported numerical endpoint -/

/-- The assembled pre-Tamagawa ordinary-mass identity transported through the
scaled integral model.  The normalized Tamagawa accessor remains symbolic and no
`tau(SO)=2` theorem is used. -/
theorem transportedOrdinaryGenusMassENNReal_eq_inv_realDifferentialMass_mul_inv_two_mul_normalizedTamagawaNumber
    [Nonempty (Fin n)]
    (inst : Fintype H.latticeOfPolarForm.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) :
    ENNReal.ofReal ((H.transportedOrdinaryGenusMass : ℚ) : ℝ) =
      (H.latticeOfPolarForm
          |>.concreteRealSpecialOrthogonalDifferentialMeasure Set.univ)⁻¹ *
        ((2 : ℝ≥0∞)⁻¹ *
          (H.latticeOfPolarForm
            |>.rationalQuadraticSpaceMatrixNormalizedDifferentialMeasurableWeilMeasureData
              inst hP).tamagawaNumberENNReal) := by
  exact H.latticeOfPolarForm
    |>.ordinaryGenusMassENNReal_eq_inv_realDifferentialMass_mul_inv_two_mul_normalizedTamagawaNumber
      inst hP

/-- The current ENNReal mass formula transported through
`latticeOfPolarForm`.  Its product is explicitly the integral model product and
therefore this theorem makes no claim about the direct dyadic density of the integral quadratic
form. -/
theorem transportedOrdinaryGenusMass_eq_polarFormLatticeMassFormulaProductSide_ENNReal
    (hn : 3 ≤ n) {P : ℝ} (hP : 0 < P)
    (hconv : H.polarFormLatticeMassLocalInverseProductTendsTo P) :
    ENNReal.ofReal ((H.transportedOrdinaryGenusMass : ℚ) : ℝ) =
      ENNReal.ofReal (H.polarFormLatticeMassFormulaProductSide P) := by
  exact H.latticeOfPolarForm
    |>.ordinaryGenusMass_eq_massFormulaProductSide_ENNReal
      hn hP hconv

/-- The real mass formula transported through `latticeOfPolarForm`. -/
theorem transportedOrdinaryGenusMass_eq_polarFormLatticeMassFormulaProductSide
    (hn : 3 ≤ n) {P : ℝ} (hP : 0 < P)
    (hconv : H.polarFormLatticeMassLocalInverseProductTendsTo P) :
    ((H.transportedOrdinaryGenusMass : ℚ) : ℝ) =
      H.polarFormLatticeMassFormulaProductSide P := by
  exact H.latticeOfPolarForm
    |>.ordinaryGenusMass_eq_massFormulaProductSide
      hn hP hconv

end PositiveDefiniteIntegralQuadraticForm

end

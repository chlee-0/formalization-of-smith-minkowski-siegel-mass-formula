import SMSFormula.RationalCliffordGeneralSpinHorizontalQuotientScalar
import SMSFormula.PadicSpecialOrthogonalDifferentialFiniteStabilizerVolumeRatio
import SMSFormula.RationalCliffordGeneralSpinHorizontalGoodPlaceLedger
import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderOrbitNormalized

/-!
# The central-fiber scalar `b_L` as a local product

The central-fiber scalar is `b_L(S) = w_SO(X) / (w_GSpin(E'(S)) · ∏_{v∈X} Haar(ℤ_p^×))` with
`X = E'(S) ∪ bad_G`.  Writing `s(v)` for the baseline scale (`1` on the horizontal bad set,
`vol_GSpin(v)⁻¹` elsewhere) and `m(v) = Haar_{ℚ_p^×}(ℤ_p^×)`, it is the finite product

`b_L(S) = ∏_{v ∈ X} β(v)`,  `β(v) := vol_SO(v)⁻¹ · (s(v) · m(v))⁻¹`.

At every odd place off the horizontal bad set and the odd-unimodular bad set, the central factor
`vol_GSpin(v) = m(v) · vol_SO(v)` gives `β(v) = 1`.  Hence `b_L(S) = ∏_{v ∈ T} β(v)` for every finite
`T` containing the horizontal bad set, the dyadic place and the odd-unimodular bad set: `b_L` is a
product of local terms over the genuinely bad places only.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

local instance cflpDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cflpPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The local term `β(v) = vol_SO(v)⁻¹ · (s(v) · m(v))⁻¹` of the central-fiber scalar. -/
def centralFiberLocalTerm (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) : ℝ≥0∞ :=
  (V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹ *
    (V.cliffordGeneralSpinHorizontalBaselineScale v *
      (rationalPadicMathlibHaarToDifferentialScalar v : ℝ≥0∞))⁻¹

/-- The local term is one at a good place. -/
theorem centralFiberLocalTerm_eq_one (V : RationalQuadraticSpaceMatrix n) (hn : 2 ≤ n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvG : v ∉ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (hvOdd : v ∉ V.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hp2 : (Rat.HeightOneSpectrum.primesEquiv v).1 ≠ 2) :
    V.centralFiberLocalTerm v = 1 := by
  have hG := V.padicCliffordGeneralSpinHorizontalIntegralVolume_eq_haar_mul_heightOne_of_two_le hn ∅
    ⟨v, by simpa using hvG⟩ hvOdd hp2
  have hm : (rationalPadicMathlibHaarToDifferentialScalar v : ℝ≥0∞) =
      padicIntegralUnitsHaarMass (Rat.HeightOneSpectrum.primesEquiv v).1 := by
    rw [coe_rationalPadicMathlibHaarToDifferentialScalar]; rfl
  have hH0 : padicIntegralUnitsHaarMass (Rat.HeightOneSpectrum.primesEquiv v).1 ≠ 0 := by
    rw [← hm]; exact ENNReal.coe_ne_zero.mpr (rationalPadicMathlibHaarToDifferentialScalar_ne_zero v)
  have hHt : padicIntegralUnitsHaarMass (Rat.HeightOneSpectrum.primesEquiv v).1 ≠ ⊤ := by
    rw [← hm]; exact ENNReal.coe_ne_top
  have hx0 := V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_zero v
  have hxt := V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_top v
  unfold centralFiberLocalTerm cliffordGeneralSpinHorizontalBaselineScale
  rw [if_neg hvG, hG, hm, ENNReal.mul_inv (Or.inl hH0) (Or.inl hHt), mul_comm _ (padicIntegralUnitsHaarMass _),
    ← mul_assoc, ENNReal.mul_inv_cancel hH0 hHt, one_mul, inv_inv,
    ENNReal.inv_mul_cancel hx0 hxt]

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {r : ℕ}

/-- `b_L(S) = ∏_{v ∈ E'(S) ∪ bad_G} β(v)`. -/
theorem coe_fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar_eq_prod
    (L : PositiveDefiniteIntegralLattice (r + 2)) (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S : ℝ≥0∞) =
      ∏ v ∈ L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
          L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces,
        L.rationalQuadraticSpaceMatrix.centralFiberLocalTerm v := by
  set V := L.rationalQuadraticSpaceMatrix
  set E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  set X := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  rw [coe_fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar]
  simp only
  unfold cliffordGeneralSpinHorizontalCentralExtensionDifferentialCylinderScale
    cliffordGeneralSpinHorizontalCentralExtensionMathlibHaarToDifferentialScalar
    rationalIdeleFiniteExceptionalMathlibHaarToDifferentialScalar
  rw [V.finiteAdelicSpecialOrthogonalBlockWeight_eq_inv_prod,
    V.cliffordGeneralSpinHorizontalRestrictedBlockWeight_eq_prod_scale]
  have hs : ∏ v ∈ E, V.cliffordGeneralSpinHorizontalBaselineScale v =
      ∏ v ∈ X, V.cliffordGeneralSpinHorizontalBaselineScale v := by
    refine Finset.prod_subset Finset.subset_union_left fun v hvX hvE ↦ ?_
    have hvG : v ∈ V.cliffordGeneralSpinHorizontalIntegralBadPlaces := by
      rcases Finset.mem_union.mp hvX with h | h
      · exact absurd h hvE
      · exact h
    unfold cliffordGeneralSpinHorizontalBaselineScale
    rw [if_pos hvG]
  have hm : ((∏ v : {v // v ∈ X}, rationalPadicMathlibHaarToDifferentialScalar v.1 : NNReal) : ℝ≥0∞) =
      ∏ v ∈ X, (rationalPadicMathlibHaarToDifferentialScalar v : ℝ≥0∞) := by
    rw [ENNReal.coe_finset_prod]
    exact Finset.prod_coe_sort X (fun v ↦ (rationalPadicMathlibHaarToDifferentialScalar v : ℝ≥0∞))
  rw [hs, hm, ← Finset.prod_mul_distrib]
  change (∏ v ∈ X, V.heightOnePadicSpecialOrthogonalIntegralVolume v)⁻¹ * _ = _
  rw [ENNReal.prod_inv_distrib (fun i _ j _ _ ↦
      Or.inr (V.heightOnePadicSpecialOrthogonalIntegralVolume_ne_top j)),
    ENNReal.prod_inv_distrib (fun i _ j _ _ ↦
      Or.inr (ENNReal.mul_ne_top (V.cliffordGeneralSpinHorizontalBaselineScale_ne_top j)
        ENNReal.coe_ne_top)), ← Finset.prod_mul_distrib]
  rfl

/-- The central-fiber scalar over any large finite set: for every finite `T` containing the
horizontal bad set, the dyadic place and the odd-unimodular bad set, `b_L(S) = ∏_{v ∈ T} β(v)`. -/
theorem coe_fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar_eq_prod_of_subset
    (L : PositiveDefiniteIntegralLattice (r + 2)) (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    {T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hG : L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces ⊆ T)
    (h2 : rationalIdeleDyadicPlace ∈ T)
    (hOdd : L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces ⊆ T) :
    (L.fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar S : ℝ≥0∞) =
      ∏ v ∈ T, L.rationalQuadraticSpaceMatrix.centralFiberLocalTerm v := by
  set V := L.rationalQuadraticSpaceMatrix
  set X := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
    V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  have hgood : ∀ v, v ∉ V.cliffordGeneralSpinHorizontalIntegralBadPlaces →
      v ≠ rationalIdeleDyadicPlace → v ∉ V.cliffordSpinCandidateOddUnimodularBadPlaces →
      V.centralFiberLocalTerm v = 1 := by
    intro v hvG hv2 hvOdd
    refine V.centralFiberLocalTerm_eq_one (by omega) v hvG hvOdd ?_
    intro hp
    apply hv2
    apply Rat.HeightOneSpectrum.primesEquiv.injective
    change _ = Rat.HeightOneSpectrum.primesEquiv (Rat.HeightOneSpectrum.primesEquiv.symm _)
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext hp
  have hX2 : rationalIdeleDyadicPlace ∈ X :=
    Finset.mem_union_left _ (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces_dyadic S)
  have hXOdd : V.cliffordSpinCandidateOddUnimodularBadPlaces ⊆ X := by
    intro v hv
    refine Finset.mem_union_left _ ?_
    unfold cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces
      cliffordGeneralSpinHorizontalCentralFiberExceptionalPlaces
    exact Finset.mem_union_right _ hv
  rw [coe_fullAdelicInvariantDifferentialCentralFiberToHorizontalScalar_eq_prod,
    Finset.prod_subset (Finset.subset_union_left : X ⊆ X ∪ T),
    ← Finset.prod_subset (Finset.subset_union_right : T ⊆ X ∪ T)]
  · intro v hv hvT
    have hvX : v ∈ X := by
      rcases Finset.mem_union.mp hv with h | h
      · exact h
      · exact absurd h hvT
    exact hgood v (fun h ↦ hvT (hG h)) (fun h ↦ hvT (h ▸ h2)) (fun h ↦ hvT (hOdd h))
  · intro v hv hvX
    have hvT : v ∈ T := by
      rcases Finset.mem_union.mp hv with h | h
      · exact absurd h hvX
      · exact h
    exact hgood v (fun h ↦ hvX (Finset.mem_union_right _ h)) (fun h ↦ hvX (h ▸ hX2))
      (fun h ↦ hvX (hXOdd h))

end PositiveDefiniteIntegralLattice

import SMSFormula.RationalAdeleAdditiveMeasure
import SMSFormula.RationalFiniteAdeleStrongApproximation
import Mathlib.Topology.Covering.Quotient

/-!
# The compact additive quotient of the rational adeles

This file constructs the literal additive quotient `𝔸_ℚ / ℚ` on the
repository's existing rational-adele carrier.  The rational diagonal is
discrete and closed.  Finite strong approximation followed by one integral
archimedean shift proves that the compact standard block `[0,1] × Ẑ` maps
surjectively to the quotient.  The quotient is therefore compact and carries
the Haar probability normalized on its whole carrier.

No quotient section or preferred representative is defined.  The two
endpoints of the closed real interval are immaterial for the compact covering
argument; no disjoint fundamental-domain assertion is made.
-/

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace PositiveDefiniteIntegralLattice

/-! ## The rational diagonal -/

/-- The additive rational diagonal in the literal full rational adeles. -/
def rationalAdeleRationalDiagonalAddSubgroup : AddSubgroup RationalAdele :=
  (algebraMap ℚ RationalAdele).range.toAddSubgroup

/-- The literal additive quotient `𝔸_ℚ / ℚ`. -/
abbrev RationalAdeleModRational :=
  RationalAdele ⧸ rationalAdeleRationalDiagonalAddSubgroup

/-- The canonical quotient map `𝔸_ℚ → 𝔸_ℚ / ℚ`. -/
def rationalAdeleModRationalQuotientMap :
    RationalAdele → RationalAdeleModRational :=
  QuotientAddGroup.mk' rationalAdeleRationalDiagonalAddSubgroup

/-- An open zero-neighborhood meeting the rational diagonal only at zero. -/
def rationalAdeleAdditiveDiagonalZeroNeighborhood : Set RationalAdele :=
  {a | rationalInfiniteAdeleHomeomorphReal a.1 ∈ Ioo (-1 : ℝ) 1 ∧
    a.2 ∈ integralFiniteAdeleSubring}

theorem isOpen_rationalAdeleAdditiveDiagonalZeroNeighborhood :
    IsOpen rationalAdeleAdditiveDiagonalZeroNeighborhood := by
  exact
    (isOpen_Ioo.preimage
      (rationalInfiniteAdeleHomeomorphReal.continuous.comp continuous_fst)).inter
      (isOpen_integralFiniteAdeleSubring.preimage continuous_snd)

private theorem rationalAdele_algebraMap_fst_additiveQuotient (q : ℚ) :
    (algebraMap ℚ RationalAdele q).1 =
      algebraMap ℚ RationalInfiniteAdele q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalInfiniteAdele)) q

private theorem rationalAdele_algebraMap_snd_additiveQuotient (q : ℚ) :
    (algebraMap ℚ RationalAdele q).2 =
      algebraMap ℚ RationalFiniteAdele q := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      ((RingHom.snd RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℚ RationalAdele))
      (algebraMap ℚ RationalFiniteAdele)) q

private theorem rationalInfiniteAdele_algebraMap_equivReal_additiveQuotient
    (q : ℚ) :
    rationalInfiniteAdeleContinuousAddEquivReal
        (algebraMap ℚ RationalInfiniteAdele q) = (q : ℝ) := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      (rationalInfiniteAdeleRingEquivReal.toRingHom.comp
        (algebraMap ℚ RationalInfiniteAdele))
      (algebraMap ℚ ℝ)) q

private theorem rationalInfiniteAdele_algebraMap_homeomorphReal_additiveQuotient
    (q : ℚ) :
    rationalInfiniteAdeleHomeomorphReal
        (algebraMap ℚ RationalInfiniteAdele q) = (q : ℝ) := by
  exact DFunLike.congr_fun
    (RingHom.ext_rat
      (rationalInfiniteAdeleRingEquivReal.toRingHom.comp
        (algebraMap ℚ RationalInfiniteAdele))
      (algebraMap ℚ ℝ)) q

/-- The isolating neighborhood meets the additive rational diagonal only at
zero. -/
theorem algebraMap_mem_rationalAdeleAdditiveDiagonalZeroNeighborhood_iff
    (q : ℚ) :
    algebraMap ℚ RationalAdele q ∈
        rationalAdeleAdditiveDiagonalZeroNeighborhood ↔ q = 0 := by
  constructor
  · rintro ⟨hinf, hfin⟩
    rw [rationalAdele_algebraMap_snd_additiveQuotient] at hfin
    rcases (rational_mem_integralFiniteAdeleSubring_iff q).mp hfin with ⟨z, rfl⟩
    rw [rationalAdele_algebraMap_fst_additiveQuotient,
      rationalInfiniteAdele_algebraMap_homeomorphReal_additiveQuotient] at hinf
    norm_num at hinf
    have hzlow : (-1 : ℤ) < z := by exact_mod_cast hinf.1
    have hzhigh : z < (1 : ℤ) := by exact_mod_cast hinf.2
    have hz : z = 0 := by omega
    simp [hz]
  · rintro rfl
    constructor
    · rw [rationalAdele_algebraMap_fst_additiveQuotient,
        rationalInfiniteAdele_algebraMap_homeomorphReal_additiveQuotient]
      norm_num
    · rw [rationalAdele_algebraMap_snd_additiveQuotient]
      exact (rational_mem_integralFiniteAdeleSubring_iff 0).mpr ⟨0, by simp⟩

noncomputable instance rationalAdeleRationalDiagonalDiscreteTopology :
    DiscreteTopology rationalAdeleRationalDiagonalAddSubgroup := by
  apply discreteTopology_of_isOpen_singleton_zero
  have hopen := isOpen_rationalAdeleAdditiveDiagonalZeroNeighborhood
  have hpre := hopen.preimage
    (continuous_subtype_val : Continuous
      (fun a : rationalAdeleRationalDiagonalAddSubgroup =>
        (a : RationalAdele)))
  rw [show
      (fun a : rationalAdeleRationalDiagonalAddSubgroup =>
        (a : RationalAdele)) ⁻¹'
          rationalAdeleAdditiveDiagonalZeroNeighborhood =
        ({0} : Set rationalAdeleRationalDiagonalAddSubgroup) by
    ext a
    constructor
    · intro ha
      rcases a.2 with ⟨q, hq⟩
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      rw [← hq,
        (algebraMap_mem_rationalAdeleAdditiveDiagonalZeroNeighborhood_iff q).mp
          (by rw [hq]; exact ha), map_zero]
      rfl
    · intro ha
      have ha0 : a = 0 := Set.mem_singleton_iff.mp ha
      subst a
      change (0 : RationalAdele) ∈
        rationalAdeleAdditiveDiagonalZeroNeighborhood
      rw [← map_zero (algebraMap ℚ RationalAdele)]
      exact
        (algebraMap_mem_rationalAdeleAdditiveDiagonalZeroNeighborhood_iff 0).mpr
          rfl] at hpre
  exact hpre

/-- The additive rational diagonal is closed in the full adeles. -/
theorem isClosed_rationalAdeleRationalDiagonalAddSubgroup :
    IsClosed (rationalAdeleRationalDiagonalAddSubgroup : Set RationalAdele) := by
  letI (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
      Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  letI : T2Space RationalInfiniteAdele :=
    rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  letI : T2Space RationalAdele := by
    change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
    infer_instance
  exact AddSubgroup.isClosed_of_discrete

noncomputable instance rationalAdeleRationalDiagonalIsClosed :
    IsClosed (rationalAdeleRationalDiagonalAddSubgroup : Set RationalAdele) :=
  isClosed_rationalAdeleRationalDiagonalAddSubgroup

/-! ## A compact block covers the quotient -/

set_option backward.isDefEq.respectTransparency false in
/-- Every full rational adele has a rational translate in the standard
compact block.  The rational is produced locally in this existence proof and
is not retained as a quotient section. -/
theorem exists_rational_sub_mem_rationalAdeleStandardBlock
    (a : RationalAdele) :
    ∃ q : ℚ, a - algebraMap ℚ RationalAdele q ∈ rationalAdeleStandardBlock := by
  obtain ⟨q, hq⟩ := exists_rational_sub_mem_integralFiniteAdeleSubring a.2
  let x : ℝ := rationalInfiniteAdeleContinuousAddEquivReal a.1 - (q : ℝ)
  let z : ℤ := ⌊x⌋
  refine ⟨q + (z : ℚ), ?_⟩
  rw [rationalAdeleStandardBlock_eq]
  constructor
  · change rationalInfiniteAdeleContinuousAddEquivReal
        ((a - algebraMap ℚ RationalAdele (q + (z : ℚ))).1) ∈ Icc 0 1
    rw [Prod.fst_sub, map_sub,
      rationalAdele_algebraMap_fst_additiveQuotient,
      rationalInfiniteAdele_algebraMap_equivReal_additiveQuotient]
    have hfract : Int.fract x ∈ Icc (0 : ℝ) 1 :=
      ⟨Int.fract_nonneg x, le_of_lt (Int.fract_lt_one x)⟩
    rw [Rat.cast_add, Rat.cast_intCast]
    have heq :
        rationalInfiniteAdeleContinuousAddEquivReal a.1 -
            ((q : ℝ) + (z : ℝ)) = Int.fract x := by
      rw [Int.fract]
      dsimp only [x, z]
      ring
    rw [heq]
    exact hfract
  · change a.2 - (algebraMap ℚ RationalAdele (q + (z : ℚ))).2 ∈
      integralFiniteAdeleSubring
    rw [rationalAdele_algebraMap_snd_additiveQuotient]
    have hz : algebraMap ℚ RationalFiniteAdele (z : ℚ) ∈
        integralFiniteAdeleSubring :=
      (rational_mem_integralFiniteAdeleSubring_iff (z : ℚ)).mpr ⟨z, rfl⟩
    have heq :
        a.2 - algebraMap ℚ RationalFiniteAdele (q + (z : ℚ)) =
          (a.2 - algebraMap ℚ RationalFiniteAdele q) -
            algebraMap ℚ RationalFiniteAdele (z : ℚ) := by
      rw [map_add]
      abel
    rw [heq]
    exact integralFiniteAdeleSubring.sub_mem hq hz

/-- The image of the compact standard block is the whole additive quotient. -/
theorem image_rationalAdeleStandardBlock_quotientMap :
    rationalAdeleModRationalQuotientMap '' rationalAdeleStandardBlock =
      (Set.univ : Set RationalAdeleModRational) := by
  apply Set.eq_univ_of_forall
  intro c
  induction c using Quotient.inductionOn with
  | h a =>
      obtain ⟨q, hq⟩ := exists_rational_sub_mem_rationalAdeleStandardBlock a
      refine ⟨a - algebraMap ℚ RationalAdele q, hq, ?_⟩
      apply QuotientAddGroup.eq.mpr
      change -(a - algebraMap ℚ RationalAdele q) + a ∈
        rationalAdeleRationalDiagonalAddSubgroup
      refine ⟨q, ?_⟩
      simp

/-- The additive quotient is compact because it is the continuous image of
the standard compact adelic block. -/
theorem isCompact_univ_rationalAdeleModRational :
    IsCompact (Set.univ : Set RationalAdeleModRational) := by
  rw [← image_rationalAdeleStandardBlock_quotientMap]
  exact isCompact_rationalAdeleStandardBlock.image
    QuotientAddGroup.continuous_mk

noncomputable instance rationalAdeleModRationalCompactSpace :
    CompactSpace RationalAdeleModRational :=
  ⟨isCompact_univ_rationalAdeleModRational⟩

/-! ## Borel structure and probability Haar -/

noncomputable instance rationalAdeleModRationalMeasurableSpace :
    MeasurableSpace RationalAdeleModRational :=
  borel RationalAdeleModRational

instance rationalAdeleModRationalBorelSpace :
    BorelSpace RationalAdeleModRational :=
  ⟨rfl⟩

theorem rationalAdeleModRationalQuotientMap_measurable :
    Measurable rationalAdeleModRationalQuotientMap :=
  QuotientAddGroup.continuous_mk.measurable

/-- The whole compact quotient as the normalization set for additive Haar. -/
def rationalAdeleModRationalUnivPositiveCompacts :
    PositiveCompacts RationalAdeleModRational where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp

/-- Haar probability on the literal compact additive quotient `𝔸_ℚ / ℚ`. -/
noncomputable def rationalAdeleModRationalProbabilityHaarMeasure :
    Measure RationalAdeleModRational :=
  Measure.addHaarMeasure rationalAdeleModRationalUnivPositiveCompacts

noncomputable instance rationalAdeleModRationalProbabilityHaarMeasure_isHaar :
    Measure.IsAddHaarMeasure rationalAdeleModRationalProbabilityHaarMeasure := by
  unfold rationalAdeleModRationalProbabilityHaarMeasure
  infer_instance

@[simp]
theorem rationalAdeleModRationalProbabilityHaarMeasure_univ :
    rationalAdeleModRationalProbabilityHaarMeasure Set.univ = 1 := by
  simpa [rationalAdeleModRationalProbabilityHaarMeasure,
    rationalAdeleModRationalUnivPositiveCompacts] using
      (Measure.addHaarMeasure_self
        (K₀ := rationalAdeleModRationalUnivPositiveCompacts))

noncomputable instance
    rationalAdeleModRationalProbabilityHaarMeasure_isProbability :
    IsProbabilityMeasure rationalAdeleModRationalProbabilityHaarMeasure :=
  ⟨rationalAdeleModRationalProbabilityHaarMeasure_univ⟩

end PositiveDefiniteIntegralLattice

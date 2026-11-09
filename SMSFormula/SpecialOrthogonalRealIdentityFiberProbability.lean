import SMSFormula.SpecialOrthogonalRealIdentityDifferentialPushforward
import Mathlib.MeasureTheory.Measure.Support

/-!
# Probability measures on identity last-column fibers
-/

open scoped Matrix Matrix.Norms.Operator ENNReal

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

set_option maxHeartbeats 50000
set_option synthInstance.maxHeartbeats 100000

local instance identitySpecialOrthogonalGroupMeasurableSpace_fiberProbability
    (n : ℕ) :
    MeasurableSpace (identitySpecialOrthogonalGroup n) :=
  borel _

local instance identitySpecialOrthogonalGroupBorelSpace_fiberProbability
    (n : ℕ) :
    BorelSpace (identitySpecialOrthogonalGroup n) :=
  ⟨rfl⟩

/-- The exact fiber over a specified last column. -/
def identitySpecialOrthogonalLastColumnFiberAt
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere n) :
    Set (identitySpecialOrthogonalGroup n) :=
  {g | identitySpecialOrthogonalLastColumn n g = x}

theorem isClosed_identitySpecialOrthogonalLastColumnFiberAt
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere n) :
    IsClosed (identitySpecialOrthogonalLastColumnFiberAt n x) :=
  isClosed_eq (continuous_identitySpecialOrthogonalLastColumn n) continuous_const

/-- The block embedding with successor ranks exposed definitionally. -/
def identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom
    (n : ℕ) :
    identitySpecialOrthogonalGroup n →*
      identitySpecialOrthogonalGroup (n + 1) :=
  identitySpecialOrthogonalLastColumnFiberEmbedHom (n + 1)

@[simp]
theorem identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom_apply
    (n : ℕ) (h : identitySpecialOrthogonalGroup n) :
    identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom n h =
      identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1) h :=
  rfl

theorem continuous_identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom
    (n : ℕ) :
    Continuous (identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom n) :=
  continuous_identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1)

/-- A lower-rank element translated into the last-column fiber represented
by `g`. The ambient group is rank `n + 2`; the source is rank `n + 1`. -/
def identitySpecialOrthogonalLastColumnFiberParametrization
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
  identitySpecialOrthogonalGroup n →
      identitySpecialOrthogonalGroup (n + 1) :=
  fun h =>
    g * identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom n h

theorem continuous_identitySpecialOrthogonalLastColumnFiberParametrization
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
  Continuous
      (identitySpecialOrthogonalLastColumnFiberParametrization n g) :=
  continuous_const.mul
    (continuous_identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom n)

theorem identitySpecialOrthogonalLastColumnFiberParametrization_mem
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1))
    (h : identitySpecialOrthogonalGroup n) :
    identitySpecialOrthogonalLastColumnFiberParametrization n g h ∈
      identitySpecialOrthogonalLastColumnFiberAt (n + 1)
        (identitySpecialOrthogonalLastColumn (n + 1) g) := by
  apply identitySpecialOrthogonalLastColumn_mul_of_mem_stabilizer
  exact
    (mem_identitySpecialOrthogonalLastColumnStabilizerSubgroup_iff
      (n + 1)
      (identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1) h)).mpr
      (identitySpecialOrthogonalLastColumnFiberEmbedGroup_mem (n + 1) h)

/-- Probability Haar on the lower-rank group, translated onto the
last-column fiber represented by `g`. -/
def identitySpecialOrthogonalLastColumnFiberProbabilityMeasure
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    Measure (identitySpecialOrthogonalGroup (n + 1)) :=
  Measure.map (identitySpecialOrthogonalLastColumnFiberParametrization n g)
    (identitySpecialOrthogonalProbabilityHaarMeasure n)

theorem identitySpecialOrthogonalLastColumnFiberProbabilityMeasure_univ
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n g Set.univ =
      1 := by
  rw [identitySpecialOrthogonalLastColumnFiberProbabilityMeasure,
    Measure.map_apply
      (continuous_identitySpecialOrthogonalLastColumnFiberParametrization n g).measurable
      MeasurableSet.univ]
  simpa using identitySpecialOrthogonalProbabilityHaarMeasure_univ n

instance identitySpecialOrthogonalLastColumnFiberProbabilityMeasure_instProbability
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    IsProbabilityMeasure
      (identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n g) :=
  ⟨identitySpecialOrthogonalLastColumnFiberProbabilityMeasure_univ n g⟩

theorem identitySpecialOrthogonalLastColumnFiberProbabilityMeasure_compl_fiber_eq_zero
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n g
        (identitySpecialOrthogonalLastColumnFiberAt (n + 1)
          (identitySpecialOrthogonalLastColumn (n + 1) g))ᶜ = 0 := by
  rw [identitySpecialOrthogonalLastColumnFiberProbabilityMeasure,
    Measure.map_apply
      (continuous_identitySpecialOrthogonalLastColumnFiberParametrization n g).measurable
      (isClosed_identitySpecialOrthogonalLastColumnFiberAt
        (n + 1) (identitySpecialOrthogonalLastColumn (n + 1) g)).isOpen_compl.measurableSet]
  have hpreimage :
      identitySpecialOrthogonalLastColumnFiberParametrization n g ⁻¹'
          (identitySpecialOrthogonalLastColumnFiberAt (n + 1)
            (identitySpecialOrthogonalLastColumn (n + 1) g))ᶜ = ∅ := by
    ext h
    simp only [Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_empty_iff_false, iff_false]
    simpa using
      identitySpecialOrthogonalLastColumnFiberParametrization_mem n g h
  rw [hpreimage, measure_empty]

theorem exists_mul_lastColumnFiberEmbedGroup_of_lastColumn_eq
    (n : ℕ) (g k : identitySpecialOrthogonalGroup (n + 1))
    (hcol : identitySpecialOrthogonalLastColumn (n + 1) g =
      identitySpecialOrthogonalLastColumn (n + 1) k) :
    ∃ a : identitySpecialOrthogonalGroup n,
      k = g *
        identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1) a := by
  have hrel :
      QuotientGroup.leftRel
        (identitySpecialOrthogonalLastColumnStabilizerSubgroup (n + 1)) g k :=
    (identitySpecialOrthogonalLastColumn_leftRel_iff (n + 1) g k).mpr hcol
  have hmem :
      g⁻¹ * k ∈
        identitySpecialOrthogonalLastColumnStabilizerSubgroup (n + 1) := by
    simpa only [QuotientGroup.leftRel_apply] using hrel
  let s : identitySpecialOrthogonalLastColumnStabilizerSubgroup (n + 1) :=
    ⟨g⁻¹ * k, hmem⟩
  let a : identitySpecialOrthogonalGroup n :=
    (identitySpecialOrthogonalLastColumnStabilizerContinuousMulEquiv
      (n + 1)).symm s
  refine ⟨a, ?_⟩
  have ha := congrArg Subtype.val
    ((identitySpecialOrthogonalLastColumnStabilizerContinuousMulEquiv
      (n + 1)).apply_symm_apply s)
  change
    identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1) a =
      g⁻¹ * k at ha
  calc
    k = g * (g⁻¹ * k) := by group
    _ = g *
        identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1) a := by
      rw [ha]

theorem identitySpecialOrthogonalLastColumnFiberProbabilityMeasure_mul_embed
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1))
    (a : identitySpecialOrthogonalGroup n) :
    identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n
        (g * identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1) a) =
      identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n g := by
  let f :
      identitySpecialOrthogonalGroup n →
        identitySpecialOrthogonalGroup (n + 1) :=
    identitySpecialOrthogonalLastColumnFiberParametrization n g
  let L : identitySpecialOrthogonalGroup n →
      identitySpecialOrthogonalGroup n :=
    fun h => a * h
  have hf : Measurable f :=
    (continuous_identitySpecialOrthogonalLastColumnFiberParametrization n g).measurable
  have hL : Measurable L := (continuous_const.mul continuous_id).measurable
  have hfun :
      identitySpecialOrthogonalLastColumnFiberParametrization n
          (g * identitySpecialOrthogonalLastColumnFiberEmbedGroup (n + 1) a) =
        f ∘ L := by
    funext h
    simp only [identitySpecialOrthogonalLastColumnFiberParametrization,
      f, L, Function.comp_apply]
    rw [mul_assoc,
      (identitySpecialOrthogonalSuccessorLastColumnFiberEmbedHom n).map_mul]
    rfl
  rw [identitySpecialOrthogonalLastColumnFiberProbabilityMeasure,
    identitySpecialOrthogonalLastColumnFiberProbabilityMeasure, hfun]
  calc
    Measure.map (f ∘ L)
        (identitySpecialOrthogonalProbabilityHaarMeasure n) =
      Measure.map f
        (Measure.map L
          (identitySpecialOrthogonalProbabilityHaarMeasure n)) :=
      (Measure.map_map hf hL).symm
    _ = Measure.map f
        (identitySpecialOrthogonalProbabilityHaarMeasure n) := by
      rw [map_mul_left_eq_self]

theorem identitySpecialOrthogonalLastColumnFiberProbabilityMeasure_eq_of_lastColumn_eq
    (n : ℕ) (g k : identitySpecialOrthogonalGroup (n + 1))
    (hcol : identitySpecialOrthogonalLastColumn (n + 1) g =
      identitySpecialOrthogonalLastColumn (n + 1) k) :
    identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n g =
      identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n k := by
  obtain ⟨a, rfl⟩ :=
    exists_mul_lastColumnFiberEmbedGroup_of_lastColumn_eq n g k hcol
  exact
    (identitySpecialOrthogonalLastColumnFiberProbabilityMeasure_mul_embed
      n g a).symm

/-- The representative-independent probability fiber measure on the
right-coset quotient. No measurability into a space of measures is asserted. -/
def identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure
    (n : ℕ) :
    identitySpecialOrthogonalLastColumnHomogeneousSpace (n + 1) →
      Measure (identitySpecialOrthogonalGroup (n + 1)) :=
  Quotient.lift
    (identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n)
    (fun g k hrel =>
      identitySpecialOrthogonalLastColumnFiberProbabilityMeasure_eq_of_lastColumn_eq
        n g k
        ((identitySpecialOrthogonalLastColumn_leftRel_iff (n + 1) g k).mp
          hrel))

@[simp]
theorem identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure_mk
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure n
        (QuotientGroup.mk g) =
      identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n g :=
  rfl

/-- The set-theoretic family of probability fiber measures indexed by the
unit sphere, transported through the quotient-to-sphere homeomorphism. -/
def identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure
    (n : ℕ) :
    identitySpecialOrthogonalLastColumnSphere (n + 1) →
      Measure (identitySpecialOrthogonalGroup (n + 1)) :=
  fun x =>
    identitySpecialOrthogonalLastColumnQuotientFiberProbabilityMeasure n
      ((identitySpecialOrthogonalLastColumnQuotientHomeomorph
        (n + 1) (Nat.succ_pos n)).symm x)

@[simp]
theorem identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure_lastColumn
    (n : ℕ) (g : identitySpecialOrthogonalGroup (n + 1)) :
    identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure n
        (identitySpecialOrthogonalLastColumn (n + 1) g) =
      identitySpecialOrthogonalLastColumnFiberProbabilityMeasure n g := by
  let H :=
    identitySpecialOrthogonalLastColumnQuotientHomeomorph
      (n + 1) (Nat.succ_pos n)
  have hg :
      H.symm (identitySpecialOrthogonalLastColumn (n + 1) g) =
        QuotientGroup.mk g := by
    apply H.injective
    rw [H.apply_symm_apply]
    exact
      identitySpecialOrthogonalLastColumnQuotientHomeomorph_mk
        (n + 1) (Nat.succ_pos n) g |>.symm
  rw [identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure, hg]
  rfl

theorem identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure_univ
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere (n + 1)) :
    identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure n x
        Set.univ = 1 := by
  obtain ⟨g, rfl⟩ :=
    surjective_identitySpecialOrthogonalLastColumn
      (n + 1) (Nat.succ_pos n) x
  rw [
    identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure_lastColumn,
    identitySpecialOrthogonalLastColumnFiberProbabilityMeasure_univ]

instance identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure_instProbability
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere (n + 1)) :
    IsProbabilityMeasure
      (identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure n x) :=
  ⟨identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure_univ n x⟩

theorem identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure_compl_fiber_eq_zero
    (n : ℕ) (x : identitySpecialOrthogonalLastColumnSphere (n + 1)) :
    identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure n x
        (identitySpecialOrthogonalLastColumnFiberAt (n + 1) x)ᶜ = 0 := by
  obtain ⟨g, rfl⟩ :=
    surjective_identitySpecialOrthogonalLastColumn
      (n + 1) (Nat.succ_pos n) x
  rw [
    identitySpecialOrthogonalLastColumnSphereFiberProbabilityMeasure_lastColumn,
    identitySpecialOrthogonalLastColumnFiberProbabilityMeasure_compl_fiber_eq_zero]

end PositiveDefiniteIntegralLattice

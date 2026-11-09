import SMSFormula.RationalAdeleFourierCharacterSeparation
import Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

noncomputable section

open MeasureTheory BoundedContinuousFunction
open scoped Uniformity

namespace PositiveDefiniteIntegralLattice

local instance : T2Space RationalAdele := by
  letI (place : IsDedekindDomain.HeightOneSpectrum ℤ) :
      Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv place).1) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).2⟩
  letI : T2Space RationalInfiniteAdele := rationalInfiniteAdeleHomeomorphReal.symm.t2Space
  letI : T2Space RationalFiniteAdele := RestrictedProduct.instT2Space
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

theorem polishSpace_rationalAdele : PolishSpace RationalAdele := by
  letI := IsTopologicalAddGroup.rightUniformSpace RationalAdele
  letI : IsUniformAddGroup RationalAdele := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace RationalAdele :=
    IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace
  letI : (𝓤 RationalAdele).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  infer_instance

def rationalAdeleBoundedFourierChar (frequency : RationalAdele) : RationalAdele →ᵇ ℂ where
  toFun value := rationalAdeleFourierChar (frequency * value)
  continuous_toFun := continuous_induced_dom.comp
    (continuous_rationalAdeleFourierChar.comp (continuous_const.mul continuous_id))
  map_bounded' := by
    refine ⟨2, fun left right => ?_⟩
    calc
      dist _ _ ≤ ‖_‖ + ‖_‖ := dist_le_norm_add_norm _ _
      _ = 2 := by simp only [Circle.norm_coe]; norm_num

@[simp]
theorem rationalAdeleBoundedFourierChar_apply (frequency value : RationalAdele) :
    rationalAdeleBoundedFourierChar frequency value =
      rationalAdeleFourierChar (frequency * value) := rfl

@[simp]
theorem rationalAdeleBoundedFourierChar_zero : rationalAdeleBoundedFourierChar 0 = 1 := by
  ext value
  simp

theorem rationalAdeleBoundedFourierChar_add (left right : RationalAdele) :
    rationalAdeleBoundedFourierChar (left + right) =
      rationalAdeleBoundedFourierChar left * rationalAdeleBoundedFourierChar right := by
  ext value
  simp [add_mul, AddChar.map_add_eq_mul]

def rationalAdeleFourierCharMonoidHom :
    Multiplicative RationalAdele →* (RationalAdele →ᵇ ℂ) where
  toFun frequency := rationalAdeleBoundedFourierChar frequency
  map_one' := rationalAdeleBoundedFourierChar_zero
  map_mul' := rationalAdeleBoundedFourierChar_add

def rationalAdeleFourierCharAlgHom :
    AddMonoidAlgebra ℂ RationalAdele →ₐ[ℂ] (RationalAdele →ᵇ ℂ) :=
  AddMonoidAlgebra.lift ℂ (RationalAdele →ᵇ ℂ) RationalAdele rationalAdeleFourierCharMonoidHom

theorem rationalAdeleFourierCharAlgHom_apply
    (polynomial : AddMonoidAlgebra ℂ RationalAdele) (value : RationalAdele) :
    rationalAdeleFourierCharAlgHom polynomial value =
      ∑ frequency ∈ polynomial.support,
        polynomial frequency * (rationalAdeleFourierChar (frequency * value) : ℂ) := by
  classical
  simp only [rationalAdeleFourierCharAlgHom, AddMonoidAlgebra.lift_apply]
  rw [Finsupp.sum_of_support_subset polynomial Set.Subset.rfl]
  · simp only [coe_sum, coe_smul, smul_eq_mul, Finset.sum_apply]
    rfl
  · simp

theorem star_mem_range_rationalAdeleFourierCharAlgHom
    {test : RationalAdele →ᵇ ℂ} (htest : test ∈ rationalAdeleFourierCharAlgHom.range) :
    star test ∈ rationalAdeleFourierCharAlgHom.range := by
  classical
  obtain ⟨polynomial, rfl⟩ := htest
  let conjugate := Finsupp.mapRange star (star_zero _) polynomial
  let negate : RationalAdele ↪ RationalAdele := ⟨Neg.neg, neg_injective⟩
  refine ⟨conjugate.embDomain negate, ?_⟩
  ext value
  change rationalAdeleFourierCharAlgHom (conjugate.embDomain negate) value =
    star (rationalAdeleFourierCharAlgHom polynomial value)
  simp only [rationalAdeleFourierCharAlgHom_apply, Finsupp.support_embDomain,
    Finset.sum_map, Finsupp.embDomain_apply_self, star_sum, star_mul']
  rw [Finsupp.support_mapRange_of_injective (star_zero _) polynomial star_injective]
  simp only [conjugate, negate, Finsupp.mapRange_apply, Function.Embedding.coeFn_mk,
    neg_mul, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj, Complex.star_def]

def rationalAdeleFourierCharAlgebra : StarSubalgebra ℂ (RationalAdele →ᵇ ℂ) where
  toSubalgebra := rationalAdeleFourierCharAlgHom.range
  star_mem' := star_mem_range_rationalAdeleFourierCharAlgHom

theorem rationalAdeleBoundedFourierChar_mem_algebra (frequency : RationalAdele) :
    rationalAdeleBoundedFourierChar frequency ∈ rationalAdeleFourierCharAlgebra := by
  classical
  refine ⟨AddMonoidAlgebra.single frequency 1, ?_⟩
  ext value
  change rationalAdeleFourierCharAlgHom (AddMonoidAlgebra.single frequency 1) value = _
  simp only [rationalAdeleFourierCharAlgHom_apply, AddMonoidAlgebra.single,
    rationalAdeleBoundedFourierChar_apply]
  rw [Finset.sum_eq_single frequency]
  · simp only [Finsupp.single_eq_same, one_mul]
  · simp [Finsupp.single_apply_ne_zero]
  · simp

theorem rationalAdeleFourierCharAlgebra_separatesPoints :
    (rationalAdeleFourierCharAlgebra.map (toContinuousMapStarₐ ℂ)).SeparatesPoints := by
  intro left right hne
  obtain ⟨frequency, hfrequency⟩ := rationalAdele_fourierChar_separatesPoints hne
  use rationalAdeleBoundedFourierChar frequency
  simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
    SetLike.mem_coe, exists_exists_and_eq_and, ne_eq]
  refine ⟨⟨rationalAdeleBoundedFourierChar frequency,
    rationalAdeleBoundedFourierChar_mem_algebra frequency, rfl⟩, ?_⟩
  exact fun heq => hfrequency (Subtype.coe_injective heq)

theorem rationalAdele_measure_eq_of_integral_fourierChar_eq
    {left right : Measure RationalAdele} [IsFiniteMeasure left] [IsFiniteMeasure right]
    (heq : ∀ frequency : RationalAdele,
      ∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) ∂left =
        ∫ value, (rationalAdeleFourierChar (frequency * value) : ℂ) ∂right) : left = right := by
  classical
  letI := polishSpace_rationalAdele
  apply ext_of_forall_mem_subalgebra_integral_eq_of_polish
    rationalAdeleFourierCharAlgebra_separatesPoints
  intro test htest
  obtain ⟨polynomial, rfl⟩ := htest
  change (∫ value, rationalAdeleFourierCharAlgHom polynomial value ∂left) =
    ∫ value, rationalAdeleFourierCharAlgHom polynomial value ∂right
  simp only [rationalAdeleFourierCharAlgHom_apply]
  have hsum (measure : Measure RationalAdele) [IsFiniteMeasure measure] :
      ∫ value, ∑ frequency ∈ polynomial.support,
          polynomial frequency * (rationalAdeleFourierChar (frequency * value) : ℂ) ∂measure =
        ∑ frequency ∈ polynomial.support,
          ∫ value, polynomial frequency *
            (rationalAdeleFourierChar (frequency * value) : ℂ) ∂measure :=
    integral_finset_sum polynomial.support fun frequency _ =>
      (integrable measure (rationalAdeleBoundedFourierChar frequency)).const_mul _
  rw [hsum left, hsum right]
  apply Finset.sum_congr rfl
  intro frequency _
  simp only [integral_const_mul, heq]

end PositiveDefiniteIntegralLattice

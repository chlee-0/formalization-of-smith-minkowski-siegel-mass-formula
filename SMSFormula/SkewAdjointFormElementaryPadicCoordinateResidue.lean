import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceSelectedDepthTranslation
import SMSFormula.PadicSpecialOrthogonalDifferentialBadPrimeFiniteReductionBoundary
import SMSFormula.SkewAdjointPadicMeasureDilation

/-!
# Finite residues in the form-adapted p-adic coordinate lattice

The form-adapted elementary coordinate equivalence identifies its compact-open
integral lattice with a finite product of p-adic integers.  Coordinatewise
reduction modulo `p ^ k` therefore gives a canonical finite carrier whose
fibers are exactly the form-adapted uniform coordinate balls and their
translates.

This module does not identify the residue image of a density-congruence source
with any stabilizer-reduction or associated-bilinear carrier.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : ℕ}

/-- The form-adapted integral coordinate lattice as an additive subgroup. -/
def skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    AddSubgroup
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule where
  carrier := skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet
  zero_mem' := by
    apply (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff
      p F hF hdet 0).2
    intro i
    simp
  add_mem' := by
    intro x y hx hy
    apply (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff
      p F hF hdet (x + y)).2
    have hx' :=
      (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff
        p F hF hdet x).1 hx
    have hy' :=
      (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff
        p F hF hdet y).1 hy
    intro i
    rw [map_add, Pi.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hx' i) (hy' i))
  neg_mem' := by
    intro x hx
    apply (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff
      p F hF hdet (-x)).2
    have hx' :=
      (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff
        p F hF hdet x).1 hx
    intro i
    simpa using hx' i

@[simp]
theorem skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup_coe
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    (skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
        p F hF hdet : Set _) =
      (skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet :
        Set (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :=
  rfl

/-- The form-adapted integral coordinate lattice is additively equivalent to
the finite family of p-adic integer coordinates selected by the
form-elementary basis. -/
def skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup p F hF hdet ≃+
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ_[p]) where
  toFun x i :=
    ⟨skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet x.1 i,
      (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff
        p F hF hdet x.1).1 x.2 i⟩
  invFun z :=
    ⟨(skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet).symm
        (fun i ↦ (z i : ℚ_[p])), by
      apply (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff
        p F hF hdet _).2
      intro i
      simpa using PadicInt.norm_le_one (z i)⟩
  left_inv x := by
    apply Subtype.ext
    apply (skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet).injective
    funext i
    simp
  right_inv z := by
    funext i
    apply PadicInt.ext
    simp
  map_add' x y := by
    funext i
    apply PadicInt.ext
    exact congrFun
      ((skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet).map_add
        x.1 y.1) i

/-- The canonical finite form-coordinate residue carrier at level `k`. -/
abbrev skewAdjointFormElementaryPadicCoordinateResidue
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :=
  Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ZMod (p ^ k)

/-- Coordinatewise reduction of the form-adapted integral coordinate lattice
modulo `p ^ k`. -/
def skewAdjointFormElementaryPadicCoordinateReduction
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup p F hF hdet →+
      skewAdjointFormElementaryPadicCoordinateResidue p k F where
  toFun x i :=
    PadicInt.toZModPow k
      ((skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
        p F hF hdet).toFun x i)
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    have he := congrFun
      ((skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
        p F hF hdet).map_add x y) i
    change
      (skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
          p F hF hdet).toFun (x + y) i =
        (skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
            p F hF hdet).toFun x i +
          (skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
            p F hF hdet).toFun y i at he
    change
      PadicInt.toZModPow k
          ((skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
            p F hF hdet).toFun (x + y) i) = _
    rw [he, map_add, Pi.add_apply]

/-- Every finite form-coordinate residue has an integral lift. -/
theorem skewAdjointFormElementaryPadicCoordinateReduction_surjective
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Function.Surjective
      (skewAdjointFormElementaryPadicCoordinateReduction p k F hF hdet) := by
  intro r
  choose z hz using
    fun i ↦ ZMod.ringHom_surjective (PadicInt.toZModPow k) (r i)
  refine
    ⟨(skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
        p F hF hdet).symm z, ?_⟩
  funext i
  change
    PadicInt.toZModPow k
        ((skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
          p F hF hdet).toFun
          ((skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
            p F hF hdet).symm z) i) = r i
  have he := congrFun
    ((skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
      p F hF hdet).apply_symm_apply z) i
  change
    (skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
      p F hF hdet).toFun
        ((skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
          p F hF hdet).symm z) i = z i at he
  rw [he]
  exact hz i

/-- The level-`k` form-coordinate residue carrier has the expected literal
cardinality. -/
theorem natCard_skewAdjointFormElementaryPadicCoordinateResidue
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) :
    Nat.card (skewAdjointFormElementaryPadicCoordinateResidue p k F) =
      (p ^ k) ^ Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F) := by
  simp [skewAdjointFormElementaryPadicCoordinateResidue,
    Nat.card_eq_fintype_card]

/-- The level-zero form-adapted ball is literally the form-adapted integral
coordinate lattice. -/
theorem skewAdjointFormElementaryPadicUniformCoordinateBall_zero
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointFormElementaryPadicUniformCoordinateBall p 0 F hF hdet =
      (skewAdjointFormElementaryPadicCoordinateLattice p F hF hdet : Set _) := by
  simp [skewAdjointFormElementaryPadicUniformCoordinateBall,
    skewAdjointPadicUniformCoordinateDilation_apply]

/-- The translated form-adapted uniform coordinate ball centered at `x`. -/
def skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (Homeomorph.addLeft (-x)) ⁻¹'
    skewAdjointFormElementaryPadicUniformCoordinateBall p k F hF hdet

theorem mem_skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall_iff
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    y ∈ skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall
        p k F hF hdet x ↔
      y - x ∈ skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet := by
  change
    -x + y ∈ skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet ↔
      y - x ∈ skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet
  rw [sub_eq_add_neg, add_comm]

/-- Vanishing finite residue coordinates are exactly membership in the
level-`k` form-adapted uniform ball. -/
theorem
    mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (x : skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      p F hF hdet) :
    x.1 ∈ skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet ↔
      skewAdjointFormElementaryPadicCoordinateReduction p k F hF hdet x = 0 := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    let yL : skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
        p F hF hdet := ⟨y, hy⟩
    funext i
    have hcoord :
        (skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
            p F hF hdet).toFun x i =
          (p : ℤ_[p]) ^ k *
            (skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
              p F hF hdet).toFun yL i := by
      apply PadicInt.ext
      change
        skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet x.1 i =
          ((p : ℚ_[p]) ^ k) *
            skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet y i
      rw [← hxy]
      simp [skewAdjointPadicUniformCoordinateDilation_apply, smul_eq_mul]
    change PadicInt.toZModPow k
      ((skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
        p F hF hdet).toFun x i) = 0
    rw [hcoord, map_mul]
    have hpzero : PadicInt.toZModPow k ((p : ℤ_[p]) ^ k) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact Ideal.subset_span (Set.mem_singleton _)
    rw [hpzero, zero_mul]
  · intro hx
    have hxcoord : ∀ i,
        PadicInt.toZModPow k
          ((skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
            p F hF hdet).toFun x i) = 0 := by
      intro i
      exact congrFun hx i
    have hxspan : ∀ i,
        (skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
          p F hF hdet).toFun x i ∈
          (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
      intro i
      rw [← PadicInt.ker_toZModPow k, RingHom.mem_ker]
      exact hxcoord i
    choose z hz using fun i ↦ Ideal.mem_span_singleton.mp (hxspan i)
    let yL : skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
        p F hF hdet :=
      (skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
        p F hF hdet).symm z
    refine ⟨yL.1, yL.2, ?_⟩
    apply (skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet).injective
    funext i
    have hzi :
        (skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
            p F hF hdet).toFun x i =
          (p : ℤ_[p]) ^ k * z i := hz i
    have hycoord :
        skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet yL.1 i =
          (z i : ℚ_[p]) := by
      have hy := congrFun
        ((skewAdjointFormElementaryPadicCoordinateLatticeEquivPadicInt
          p F hF hdet).apply_symm_apply z) i
      exact congrArg (fun a : ℤ_[p] ↦ (a : ℚ_[p])) hy
    have hcast := congrArg (fun a : ℤ_[p] ↦ (a : ℚ_[p])) hzi
    change
      skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet x.1 i =
        (p : ℚ_[p]) ^ k * (z i : ℚ_[p]) at hcast
    rw [skewAdjointPadicUniformCoordinateDilation_apply]
    rw [← hycoord] at hcast
    exact
      (congrFun
        ((skewAdjointFormElementaryPadicCoordinateEquiv p F hF hdet).map_smul
          ((p : ℚ_[p]) ^ k) yL.1) i).trans hcast.symm

/-- Equal form-coordinate residues are exactly differences in the
level-`k` form-adapted ball. -/
theorem
    skewAdjointFormElementaryPadicCoordinateReduction_eq_iff_sub_mem_uniformCoordinateBall
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (x y : skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      p F hF hdet) :
    skewAdjointFormElementaryPadicCoordinateReduction p k F hF hdet y =
        skewAdjointFormElementaryPadicCoordinateReduction p k F hF hdet x ↔
      y.1 - x.1 ∈ skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet := by
  let z : skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      p F hF hdet :=
    ⟨y.1 - x.1,
      (skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
        p F hF hdet).sub_mem y.2 x.2⟩
  rw [mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
    p k F hF hdet z]
  change _ = _ ↔
    skewAdjointFormElementaryPadicCoordinateReduction p k F hF hdet z = 0
  rw [show z = y - x by rfl, map_sub, sub_eq_zero]

/-- Fibers of form-coordinate reduction are translated form-adapted balls,
restricted to integral coordinate points. -/
theorem
    skewAdjointFormElementaryPadicCoordinateReduction_eq_iff_mem_translatedUniformCoordinateBall
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (x y : skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      p F hF hdet) :
    skewAdjointFormElementaryPadicCoordinateReduction p k F hF hdet y =
        skewAdjointFormElementaryPadicCoordinateReduction p k F hF hdet x ↔
      y.1 ∈ skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall
        p k F hF hdet x.1 := by
  rw [mem_skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall_iff]
  exact
    skewAdjointFormElementaryPadicCoordinateReduction_eq_iff_sub_mem_uniformCoordinateBall
      p k F hF hdet x y

/-- Every form-adapted level-`k` ball lies in the level-zero integral
coordinate lattice. -/
theorem skewAdjointFormElementaryPadicUniformCoordinateBall_subset_lattice
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    skewAdjointFormElementaryPadicUniformCoordinateBall p k F hF hdet ⊆
      skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
        p F hF hdet := by
  rintro y ⟨z, hz, rfl⟩
  apply (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff
    p F hF hdet _).2
  have hz' :=
    (mem_skewAdjointFormElementaryPadicCoordinateLattice_iff
      p F hF hdet z).1 hz
  intro i
  rw [skewAdjointPadicUniformCoordinateDilation_apply, map_smul,
    Pi.smul_apply, norm_smul]
  have hp : ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (le_of_lt Padic.norm_p_lt_one)
  exact (mul_le_mul hp (hz' i) (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

/-- The zero residue fiber maps to the whole form-adapted level-`k` ball. -/
theorem image_formElementaryCoordinateReduction_preimage_zero
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0) :
    Subtype.val ''
        ((skewAdjointFormElementaryPadicCoordinateReduction
          p k F hF hdet) ⁻¹' {0}) =
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet := by
  ext y
  constructor
  · rintro ⟨yL, hyL, rfl⟩
    exact
      (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
        p k F hF hdet yL).2 hyL
  · intro hy
    have hyL :=
      skewAdjointFormElementaryPadicUniformCoordinateBall_subset_lattice
        p k F hF hdet hy
    let yL : skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
        p F hF hdet := ⟨y, hyL⟩
    refine ⟨yL, ?_, rfl⟩
    exact
      (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_coordinateReduction_eq_zero
        p k F hF hdet yL).1 hy

/-- Every form-coordinate residue fiber over an integral center maps exactly
to its translated form-adapted level-`k` ball. -/
theorem image_formElementaryCoordinateReduction_preimage_singleton
    (p k : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    (x : skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
      p F hF hdet) :
    Subtype.val ''
        ((skewAdjointFormElementaryPadicCoordinateReduction
          p k F hF hdet) ⁻¹'
          {skewAdjointFormElementaryPadicCoordinateReduction
            p k F hF hdet x}) =
      skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall
        p k F hF hdet x.1 := by
  ext y
  constructor
  · rintro ⟨yL, hyL, rfl⟩
    exact
      (skewAdjointFormElementaryPadicCoordinateReduction_eq_iff_mem_translatedUniformCoordinateBall
        p k F hF hdet x yL).1 hyL
  · intro hy
    have hdiff :
        y - x.1 ∈ skewAdjointFormElementaryPadicUniformCoordinateBall
          p k F hF hdet :=
      (mem_skewAdjointFormElementaryPadicTranslatedUniformCoordinateBall_iff
        p k F hF hdet x.1 y).1 hy
    have hdiffL :=
      skewAdjointFormElementaryPadicUniformCoordinateBall_subset_lattice
        p k F hF hdet hdiff
    have hyL :
        y ∈ skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
          p F hF hdet := by
      have hadd :=
        (skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
          p F hF hdet).add_mem hdiffL x.2
      simpa only [sub_add_cancel] using hadd
    let yL : skewAdjointFormElementaryPadicCoordinateLatticeAddSubgroup
        p F hF hdet := ⟨y, hyL⟩
    refine ⟨yL, ?_, rfl⟩
    exact
      (skewAdjointFormElementaryPadicCoordinateReduction_eq_iff_mem_translatedUniformCoordinateBall
        p k F hF hdet x yL).2 hy

end Matrix

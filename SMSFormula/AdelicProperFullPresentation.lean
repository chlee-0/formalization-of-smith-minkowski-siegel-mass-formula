import SMSFormula.AdelicProperFinitePresentation
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Units

/-!
# Concrete real and full-adelic special orthogonal groups

This module adds the algebraic matrix groups needed before stating a
Tamagawa-number theorem. It deliberately does not define Haar measures,
quotient measures, or a real/finite product decomposition.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

open MeasureTheory
open TopologicalSpace
open scoped Matrix

/-- Matrices over a product ring are equivalently pairs of matrices. -/
def matrixProdRingEquiv {ι R S : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] :
    Matrix ι ι (R × S) ≃+* Matrix ι ι R × Matrix ι ι S where
  toFun M :=
    (M.map (RingHom.fst R S), M.map (RingHom.snd R S))
  invFun M i j := (M.1 i j, M.2 i j)
  left_inv M := by
    ext i j <;> rfl
  right_inv M := by
    rcases M with ⟨A, B⟩
    apply Prod.ext
    · ext i j
      rfl
    · ext i j
      rfl
  map_add' A B := by
    apply Prod.ext <;> ext i j <;> simp
  map_mul' A B := by
    apply Prod.ext
    · ext i j
      change (RingHom.fst R S) (∑ x, A i x * B x j) =
        ∑ x, (RingHom.fst R S) (A i x) * (RingHom.fst R S) (B x j)
      simp
    · ext i j
      change (RingHom.snd R S) (∑ x, A i x * B x j) =
        ∑ x, (RingHom.snd R S) (A i x) * (RingHom.snd R S) (B x j)
      simp

/-- General linear groups over a product ring split into the product of the
two general linear groups. -/
def generalLinearGroupProdEquiv {ι R S : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] :
    GL ι (R × S) ≃* GL ι R × GL ι S :=
  (Units.mapEquiv
    (matrixProdRingEquiv (ι := ι) (R := R) (S := S)).toMulEquiv).trans
      MulEquiv.prodUnits

/-- The matrix product-ring equivalence is a homeomorphism for the product
topologies. -/
def matrixProdHomeomorph {ι R S : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] :
    Matrix ι ι (R × S) ≃ₜ Matrix ι ι R × Matrix ι ι S where
  toEquiv := (matrixProdRingEquiv (ι := ι) (R := R) (S := S)).toEquiv
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_pi fun i => continuous_pi fun j =>
        continuous_fst.comp ((continuous_apply j).comp (continuous_apply i))
    · exact continuous_pi fun i => continuous_pi fun j =>
        continuous_snd.comp ((continuous_apply j).comp (continuous_apply i))
  continuous_invFun := by
    exact continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).prodMk
        ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))

/-- The matrix product-ring equivalence as a continuous multiplicative
equivalence. -/
def matrixProdContinuousMulEquiv {ι R S : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] :
    Matrix ι ι (R × S) ≃ₜ* Matrix ι ι R × Matrix ι ι S :=
  ContinuousMulEquiv.mk'
    (matrixProdHomeomorph (ι := ι) (R := R) (S := S)) (by
      intro A B
      exact (matrixProdRingEquiv (ι := ι) (R := R) (S := S)).map_mul A B)

/-- Units in a product of topological monoids are continuously equivalent to
the product of the two unit groups. -/
def prodUnitsContinuousMulEquiv {M N : Type*}
    [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N] :
    (M × N)ˣ ≃ₜ* Mˣ × Nˣ :=
  ContinuousMulEquiv.mk' Homeomorph.prodUnits (by
    intro x y
    exact MulEquiv.prodUnits.map_mul x y)

/-- General linear groups over a product topological ring split continuously
into the product of the two general linear groups. -/
def generalLinearGroupProdContinuousEquiv {ι R S : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] :
    GL ι (R × S) ≃ₜ* GL ι R × GL ι S :=
  (Units.mapContinuousMulEquiv
    (matrixProdContinuousMulEquiv (ι := ι) (R := R) (S := S))).trans
      prodUnitsContinuousMulEquiv

/-- The product of two continuous multiplicative equivalences. -/
def prodContinuousMulEquiv {A B C D : Type*}
    [Mul A] [Mul B] [Mul C] [Mul D]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D]
    (e : A ≃ₜ* B) (f : C ≃ₜ* D) : A × C ≃ₜ* B × D :=
  ContinuousMulEquiv.mk'
    (Homeomorph.prodCongr e.toHomeomorph f.toHomeomorph) (by
      intro x y
      exact Prod.ext (e.map_mul x.1 y.1) (f.map_mul x.2 y.2))

/-- The infinite adele ring of `ℚ`. -/
abbrev RationalInfiniteAdele := NumberField.InfiniteAdeleRing ℚ

/-- The full adele ring of `ℚ`, presented using the Dedekind domain `ℤ`. -/
abbrev RationalAdele := NumberField.AdeleRing ℤ ℚ

/-! ## Real special orthogonal group -/

/-- The concrete real orthogonal matrix group attached to `L`. -/
def realOrthogonalMatrixSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup (Matrix (Fin n) (Fin n) ℝ)ˣ :=
  formPreservingMatrixSubgroup L.pairingMatrix_real

/-- The concrete carrier of `O(L)(ℝ)`. -/
abbrev ConcreteRealOrthogonalGroup (L : PositiveDefiniteIntegralLattice n) :=
  L.realOrthogonalMatrixSubgroup

/-- The determinant-one subgroup of the concrete real orthogonal group. -/
def realSpecialOrthogonalMatrixSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup L.ConcreteRealOrthogonalGroup :=
  specialFormPreservingMatrixSubgroup L.pairingMatrix_real

/-- The concrete carrier of `SO(L)(ℝ)`. -/
abbrev ConcreteRealSpecialOrthogonalGroup (L : PositiveDefiniteIntegralLattice n) :=
  L.realSpecialOrthogonalMatrixSubgroup

@[simp]
theorem mem_realSpecialOrthogonalMatrixSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteRealOrthogonalGroup) :
    g ∈ L.realSpecialOrthogonalMatrixSubgroup ↔ g.1.1.det = 1 :=
  mem_specialFormPreservingMatrixSubgroup_iff L.pairingMatrix_real g

/-! ## Compactness of the real groups -/

set_option maxHeartbeats 800000 in
private lemma exists_pos_quadratic_lower_bound
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ c > 0, ∀ v : Fin n → ℝ,
      c * (∑ i, v i ^ 2) ≤ v ⬝ᵥ A.mulVec v := by
  by_cases hn : n = 0
  · subst hn
    exact ⟨1, by norm_num, by intro v; simp⟩
  · have h_cont_pos_def : ∃ c > 0, ∀ v : Fin n → ℝ,
        (∑ i, v i ^ 2) = 1 → v ⬝ᵥ A.mulVec v ≥ c := by
      have h_compact : IsCompact
          {v : Fin n → ℝ | (∑ i, v i ^ 2) = 1} := by
        refine Metric.isCompact_iff_isClosed_bounded.mpr ?_
        exact ⟨isClosed_eq
            (continuous_finset_sum _ fun _ _ =>
              Continuous.pow (continuous_apply _) _)
            continuous_const,
          isBounded_iff_forall_norm_le.mpr ⟨1, by
            rintro v (hv : ∑ i, v i ^ 2 = 1)
            exact pi_norm_le_iff_of_nonneg (by norm_num) |>.2 fun i => by
              simpa [hv] using Real.abs_le_sqrt
                (Finset.single_le_sum (fun i _ => sq_nonneg (v i))
                  (Finset.mem_univ i))⟩⟩
      have h_least : ∃ c ∈ Set.image
          (fun v : Fin n → ℝ => v ⬝ᵥ A.mulVec v)
          {v : Fin n → ℝ | (∑ i, v i ^ 2) = 1},
          ∀ y ∈ Set.image (fun v : Fin n → ℝ => v ⬝ᵥ A.mulVec v)
            {v : Fin n → ℝ | (∑ i, v i ^ 2) = 1}, c ≤ y := by
        apply_rules [IsCompact.exists_isLeast, h_compact]
        · exact h_compact.image <| Continuous.dotProduct continuous_id' <|
            Continuous.matrix_mulVec continuous_const continuous_id'
        · exact ⟨_, ⟨fun i => if i = ⟨0, Nat.pos_of_ne_zero hn⟩ then 1 else 0,
            by norm_num, rfl⟩⟩
      obtain ⟨c, hc₁, hc₂⟩ := h_least
      use c
      have hpos := hA.2
      simp_all +decide [Finsupp.sum_fintype, dotProduct, Matrix.mulVec]
      obtain ⟨x, hx₁, hx₂⟩ := hc₁
      specialize hpos (show Finsupp.equivFunOnFinite.symm x ≠ 0 from by
        intro h
        simp_all +decide [Finsupp.ext_iff])
      simp_all +decide [mul_assoc, Finset.mul_sum _ _ _]
    obtain ⟨c, hc₀, hc⟩ := h_cont_pos_def
    use c
    refine ⟨hc₀, fun v => ?_⟩
    by_cases hv : v = 0
    · simp_all +decide
    · convert mul_le_mul_of_nonneg_right
          (hc (fun i => v i / Real.sqrt (∑ i, v i ^ 2)) ?_)
          (show 0 ≤ ∑ i, v i ^ 2 from
            Finset.sum_nonneg fun _ _ => sq_nonneg _) using 1
      · simp +decide [div_eq_inv_mul, Matrix.mulVec, dotProduct,
          Finset.mul_sum _ _ _, mul_comm, mul_left_comm]
        simp +decide [← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul,
          ← sq, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _]
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt <| lt_of_le_of_ne
          (Finset.sum_nonneg fun _ _ => sq_nonneg _) <| Ne.symm <| by
            contrapose! hv
            ext i
            simp_all +decide [Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg]),
          mul_one]
      · norm_num [div_pow,
          Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _]
        rw [← Finset.sum_div, div_self <| ne_of_gt <| lt_of_le_of_ne
          (Finset.sum_nonneg fun _ _ => sq_nonneg _) <| Ne.symm <| by
            contrapose! hv
            ext i
            simp_all +decide [Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg]]

private def realFormPreservingMatrixSet (L : PositiveDefiniteIntegralLattice n) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {M | Mᵀ * L.pairingMatrix_real * M = L.pairingMatrix_real}

private lemma isClosed_realFormPreservingMatrixSet (L : PositiveDefiniteIntegralLattice n) :
    IsClosed L.realFormPreservingMatrixSet := by
  exact isClosed_eq
    ((continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul
      continuous_id)
    continuous_const

set_option maxHeartbeats 800000 in
private lemma realFormPreservingMatrixSet_subset_compactBox
    (L : PositiveDefiniteIntegralLattice n) :
    ∃ B : ℝ, L.realFormPreservingMatrixSet ⊆ (Set.Icc (-B) B).matrix := by
  obtain ⟨c, hcpos, hc⟩ :=
    exists_pos_quadratic_lower_bound L.pairingMatrix_real L.form_posDef
  let C := ∑ i, ∑ j, |L.pairingMatrix_real i j|
  let B := Real.sqrt (C / c)
  refine ⟨B, ?_⟩
  intro M hM
  rw [Set.mem_matrix]
  intro i j
  have hCnonneg : 0 ≤ C := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsq : M i j ^ 2 ≤ C / c := by
    rw [le_div_iff₀ hcpos]
    calc
      M i j ^ 2 * c = c * M i j ^ 2 := mul_comm _ _
      _ ≤ c * (∑ k, M k j ^ 2) :=
        mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun k _ => sq_nonneg (M k j))
            (Finset.mem_univ i)) hcpos.le
      _ ≤ (fun v : Fin n → ℝ => v ⬝ᵥ L.pairingMatrix_real.mulVec v)
          (fun k => M k j) := hc _
      _ = L.pairingMatrix_real j j := by
        have hentry := congrArg (fun A => A j j) hM
        have hsymm : L.pairingMatrix_real.IsSymm := L.form_symm.map _
        simpa [realFormPreservingMatrixSet, Matrix.mul_apply, Matrix.mulVec,
          dotProduct, pow_two, hsymm.apply, mul_comm, mul_left_comm, mul_assoc]
          using hentry
      _ ≤ C := by
        calc
          L.pairingMatrix_real j j ≤ |L.pairingMatrix_real j j| := le_abs_self _
          _ ≤ ∑ k, |L.pairingMatrix_real j k| := by
            exact Finset.single_le_sum
              (s := Finset.univ)
              (f := fun k => |L.pairingMatrix_real j k|)
              (fun k _ => abs_nonneg _)
              (Finset.mem_univ j)
          _ ≤ C := by
            exact Finset.single_le_sum
              (s := Finset.univ)
              (f := fun k => ∑ l, |L.pairingMatrix_real k l|)
              (fun k _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
              (Finset.mem_univ j)
  have habs : |M i j| ≤ B := by
    apply Real.abs_le_sqrt
    simpa [B] using hsq
  exact ⟨neg_le_of_abs_le habs, le_of_abs_le habs⟩

private lemma isCompact_realFormPreservingMatrixSet (L : PositiveDefiniteIntegralLattice n) :
    IsCompact L.realFormPreservingMatrixSet := by
  obtain ⟨B, hsubset⟩ := L.realFormPreservingMatrixSet_subset_compactBox
  exact isCompact_Icc.matrix.of_isClosed_subset
    L.isClosed_realFormPreservingMatrixSet hsubset

private abbrev RawRealOrthogonalGroup (L : PositiveDefiniteIntegralLattice n) :=
  L.realFormPreservingMatrixSet

private noncomputable instance rawRealOrthogonalGroupCompactSpace
    (L : PositiveDefiniteIntegralLattice n) : CompactSpace L.RawRealOrthogonalGroup :=
  isCompact_iff_compactSpace.mp L.isCompact_realFormPreservingMatrixSet

private lemma realFormPreservingMatrix_isUnit (L : PositiveDefiniteIntegralLattice n)
    {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M ∈ L.realFormPreservingMatrixSet) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  have h := congrArg Matrix.det hM
  have hA := L.form_posDef.det_pos.ne'
  simp only [Matrix.det_mul, Matrix.det_transpose, hdet, zero_mul] at h
  exact hA h.symm

private noncomputable def rawRealOrthogonalToOrthogonal
    (L : PositiveDefiniteIntegralLattice n) :
    L.RawRealOrthogonalGroup → L.ConcreteRealOrthogonalGroup := fun M =>
  let hunit := L.realFormPreservingMatrix_isUnit M.property
  ⟨hunit.unit, by
    change hunit.unit.1ᵀ * L.pairingMatrix_real * hunit.unit.1 = L.pairingMatrix_real
    simpa only [hunit.unit_spec] using M.property⟩

private lemma rawRealOrthogonalToOrthogonal_inverse_val
    (L : PositiveDefiniteIntegralLattice n) (M : L.RawRealOrthogonalGroup) :
    ↑((L.rawRealOrthogonalToOrthogonal M).1⁻¹) =
      L.pairingMatrix_real⁻¹ * M.1ᵀ * L.pairingMatrix_real := by
  let A := L.pairingMatrix_real
  let N := A⁻¹ * M.1ᵀ * A
  have hAunit : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp L.form_posDef.isUnit
  have hleft : N * M.1 = 1 := by
    calc
      N * M.1 = A⁻¹ * (M.1ᵀ * A * M.1) := by
        simp [N, Matrix.mul_assoc]
      _ = A⁻¹ * A := by rw [M.property]
      _ = 1 := Matrix.nonsing_inv_mul A hAunit
  change ↑((L.rawRealOrthogonalToOrthogonal M).1⁻¹) = N
  symm
  have hval : M.1 = (L.rawRealOrthogonalToOrthogonal M).1.1 := by
    simp [rawRealOrthogonalToOrthogonal]
  have hright : M.1 *
      (↑((L.rawRealOrthogonalToOrthogonal M).1⁻¹) :
        Matrix (Fin n) (Fin n) ℝ) = 1 := by
    rw [hval]
    exact congrArg Units.val
      (mul_inv_cancel (L.rawRealOrthogonalToOrthogonal M).1)
  calc
    N = N * 1 := by rw [Matrix.mul_one]
    _ = N * (M.1 *
        (↑((L.rawRealOrthogonalToOrthogonal M).1⁻¹) :
          Matrix (Fin n) (Fin n) ℝ)) := by
      rw [hright]
    _ = (N * M.1) *
        (↑((L.rawRealOrthogonalToOrthogonal M).1⁻¹) :
          Matrix (Fin n) (Fin n) ℝ) := by
      exact (Matrix.mul_assoc _ _ _).symm
    _ = (↑((L.rawRealOrthogonalToOrthogonal M).1⁻¹) :
        Matrix (Fin n) (Fin n) ℝ) := by rw [hleft, Matrix.one_mul]

private lemma continuous_rawRealOrthogonalToOrthogonal
    (L : PositiveDefiniteIntegralLattice n) :
    Continuous L.rawRealOrthogonalToOrthogonal := by
  apply continuous_induced_rng.mpr
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val
  · change Continuous (fun M =>
        (↑((L.rawRealOrthogonalToOrthogonal M).1⁻¹) :
          Matrix (Fin n) (Fin n) ℝ))
    rw [show (fun M => (↑((L.rawRealOrthogonalToOrthogonal M).1⁻¹) :
          Matrix (Fin n) (Fin n) ℝ)) =
        fun M => L.pairingMatrix_real⁻¹ * M.1ᵀ * L.pairingMatrix_real from by
      funext M
      exact L.rawRealOrthogonalToOrthogonal_inverse_val M]
    exact
      (continuous_const.matrix_mul continuous_subtype_val.matrix_transpose).matrix_mul
        continuous_const

private lemma surjective_rawRealOrthogonalToOrthogonal
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Surjective L.rawRealOrthogonalToOrthogonal := by
  intro g
  let M : L.RawRealOrthogonalGroup := ⟨g.1.1, g.2⟩
  refine ⟨M, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change (L.rawRealOrthogonalToOrthogonal M).1.1 = g.1.1
  simp [rawRealOrthogonalToOrthogonal, M]

/-- The real orthogonal group of a positive-definite integral lattice is
compact. -/
noncomputable instance concreteRealOrthogonalGroupCompactSpace
    (L : PositiveDefiniteIntegralLattice n) : CompactSpace L.ConcreteRealOrthogonalGroup := by
  apply isCompact_univ_iff.mp
  have hrange : Set.range L.rawRealOrthogonalToOrthogonal = Set.univ :=
    Set.eq_univ_iff_forall.mpr fun g =>
      L.surjective_rawRealOrthogonalToOrthogonal g
  rw [← hrange]
  simpa only [Set.image_univ] using
    isCompact_univ.image L.continuous_rawRealOrthogonalToOrthogonal

/-- The real special orthogonal group is closed in the real orthogonal
group. -/
theorem isClosed_realSpecialOrthogonalMatrixSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    IsClosed (L.realSpecialOrthogonalMatrixSubgroup :
      Set L.ConcreteRealOrthogonalGroup) := by
  have hset :
      (L.realSpecialOrthogonalMatrixSubgroup :
        Set L.ConcreteRealOrthogonalGroup) =
        {g : L.ConcreteRealOrthogonalGroup | g.1.1.det = 1} := by
    ext g
    exact L.mem_realSpecialOrthogonalMatrixSubgroup_iff g
  rw [hset]
  exact isClosed_eq
    ((Units.continuous_val.comp continuous_subtype_val).matrix_det)
    continuous_const

/-- The real special orthogonal group of a positive-definite integral lattice
is compact. -/
noncomputable instance concreteRealSpecialOrthogonalGroupCompactSpace
    (L : PositiveDefiniteIntegralLattice n) :
    CompactSpace L.ConcreteRealSpecialOrthogonalGroup := by
  apply isCompact_univ_iff.mp
  have h := L.isClosed_realSpecialOrthogonalMatrixSubgroup
    |>.isClosedEmbedding_subtypeVal.isCompact_preimage isCompact_univ
  simpa only [Set.preimage_univ] using h

/-! ## Normalized Haar measure on the real group -/

/-- The real special orthogonal group carries its inherited Borel measurable
space. -/
instance concreteRealSpecialOrthogonalGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.ConcreteRealSpecialOrthogonalGroup :=
  borel L.ConcreteRealSpecialOrthogonalGroup

instance concreteRealSpecialOrthogonalGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace L.ConcreteRealSpecialOrthogonalGroup :=
  ⟨rfl⟩

/-- The whole compact real special orthogonal group, bundled as the
normalization set for Haar measure. -/
def realSpecialOrthogonalUnivPositiveCompacts
    (L : PositiveDefiniteIntegralLattice n) :
    PositiveCompacts L.ConcreteRealSpecialOrthogonalGroup where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp

/-- Haar measure on `SO(L)(ℝ)`, normalized to give the whole compact group
mass one. This is not the differential-form gauge measure. -/
noncomputable def concreteRealSpecialOrthogonalNormalizedHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    Measure L.ConcreteRealSpecialOrthogonalGroup :=
  Measure.haarMeasure L.realSpecialOrthogonalUnivPositiveCompacts

instance concreteRealSpecialOrthogonalNormalizedHaarMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.IsMulLeftInvariant
      L.concreteRealSpecialOrthogonalNormalizedHaarMeasure := by
  unfold concreteRealSpecialOrthogonalNormalizedHaarMeasure
  infer_instance

/-- The normalized Haar measure of the whole real special orthogonal group is
one. -/
theorem concreteRealSpecialOrthogonalNormalizedHaarMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) :
    L.concreteRealSpecialOrthogonalNormalizedHaarMeasure Set.univ = 1 := by
  exact Measure.haarMeasure_self

instance concreteRealSpecialOrthogonalNormalizedHaarMeasure_isFiniteMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    IsFiniteMeasure L.concreteRealSpecialOrthogonalNormalizedHaarMeasure :=
  ⟨by rw [L.concreteRealSpecialOrthogonalNormalizedHaarMeasure_univ]
      exact ENNReal.one_lt_top⟩

set_option synthInstance.maxHeartbeats 200000 in
instance concreteRealSpecialOrthogonalNormalizedHaarMeasure_isSigmaFinite
    (L : PositiveDefiniteIntegralLattice n) :
    SigmaFinite L.concreteRealSpecialOrthogonalNormalizedHaarMeasure := by
  infer_instance

/-! ## Infinite-adelic special orthogonal group -/

/-- The form matrix of `L`, transported to the infinite adeles of `ℚ`. -/
def infiniteAdelicFormMatrix (L : PositiveDefiniteIntegralLattice n) :
    Matrix (Fin n) (Fin n) RationalInfiniteAdele :=
  L.pairingMatrix.map (algebraMap ℤ RationalInfiniteAdele)

/-- The concrete infinite-adelic orthogonal matrix group attached to `L`. -/
def infiniteAdelicOrthogonalMatrixSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup (Matrix (Fin n) (Fin n) RationalInfiniteAdele)ˣ :=
  formPreservingMatrixSubgroup L.infiniteAdelicFormMatrix

/-- The concrete carrier of `O(L)(A_∞)`. -/
abbrev ConcreteInfiniteAdelicOrthogonalGroup (L : PositiveDefiniteIntegralLattice n) :=
  L.infiniteAdelicOrthogonalMatrixSubgroup

/-- The determinant-one infinite-adelic orthogonal subgroup. -/
def infiniteAdelicSpecialOrthogonalMatrixSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup L.ConcreteInfiniteAdelicOrthogonalGroup :=
  specialFormPreservingMatrixSubgroup L.infiniteAdelicFormMatrix

/-- The concrete carrier of `SO(L)(A_∞)`. -/
abbrev ConcreteInfiniteAdelicSpecialOrthogonalGroup (L : PositiveDefiniteIntegralLattice n) :=
  L.infiniteAdelicSpecialOrthogonalMatrixSubgroup

@[simp]
theorem mem_infiniteAdelicOrthogonalMatrixSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g : (Matrix (Fin n) (Fin n) RationalInfiniteAdele)ˣ) :
    g ∈ L.infiniteAdelicOrthogonalMatrixSubgroup ↔
      g.1ᵀ * L.infiniteAdelicFormMatrix * g.1 =
        L.infiniteAdelicFormMatrix :=
  Iff.rfl

@[simp]
theorem mem_infiniteAdelicSpecialOrthogonalMatrixSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteInfiniteAdelicOrthogonalGroup) :
    g ∈ L.infiniteAdelicSpecialOrthogonalMatrixSubgroup ↔ g.1.1.det = 1 :=
  mem_specialFormPreservingMatrixSubgroup_iff L.infiniteAdelicFormMatrix g

/-! ## Algebraic identification of the infinite and real factors -/

/-- The unique rational infinite completion is the real field. -/
def rationalInfiniteAdeleRingEquivReal : RationalInfiniteAdele ≃+* ℝ := by
  letI : Unique (NumberField.InfinitePlace ℚ) :=
    { default := Rat.infinitePlace
      uniq := fun v => Subsingleton.elim v Rat.infinitePlace }
  exact
    (RingEquiv.piUnique
      (fun v : NumberField.InfinitePlace ℚ ↦ v.Completion)).trans
        (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace)

/-- The rational infinite-adele equivalence transports the infinite form
matrix to the concrete real form matrix. -/
theorem infiniteAdelicFormMatrix_map_equivReal (L : PositiveDefiniteIntegralLattice n) :
    L.infiniteAdelicFormMatrix.map rationalInfiniteAdeleRingEquivReal =
      L.pairingMatrix_real := by
  apply Matrix.ext
  intro i j
  change
    rationalInfiniteAdeleRingEquivReal
        (algebraMap ℤ RationalInfiniteAdele (L.pairingMatrix i j)) =
      algebraMap ℤ ℝ (L.pairingMatrix i j)
  exact DFunLike.congr_fun
    (RingHom.ext_int
      (rationalInfiniteAdeleRingEquivReal.toRingHom.comp
        (algebraMap ℤ RationalInfiniteAdele))
      (algebraMap ℤ ℝ))
    (L.pairingMatrix i j)

/-- The ambient general linear groups over the rational infinite adeles and
the reals are algebraically equivalent. -/
def infiniteAdelicGeneralLinearGroupEquivReal (_L : PositiveDefiniteIntegralLattice n) :
    GL (Fin n) RationalInfiniteAdele ≃* GL (Fin n) ℝ :=
  Units.mapEquiv
    (rationalInfiniteAdeleRingEquivReal.mapMatrix (m := Fin n)).toMulEquiv

/-- Mapping entries through the rational infinite-adele equivalence sends
infinite-adelic special orthogonal matrices to real ones. -/
def infiniteAdelicSpecialOrthogonalToRealHom (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteInfiniteAdelicSpecialOrthogonalGroup →*
      L.ConcreteRealSpecialOrthogonalGroup where
  toFun g := by
    let mapped := L.infiniteAdelicGeneralLinearGroupEquivReal g.1.1
    have hForm : mapped ∈ L.realOrthogonalMatrixSubgroup := by
      change mapped.1ᵀ * L.pairingMatrix_real * mapped.1 = L.pairingMatrix_real
      have hmapped := congrArg
        rationalInfiniteAdeleRingEquivReal.mapMatrix g.1.2
      simp only [map_mul, RingEquiv.mapMatrix_apply, Matrix.transpose_map,
        L.infiniteAdelicFormMatrix_map_equivReal] at hmapped
      simpa [mapped, infiniteAdelicGeneralLinearGroupEquivReal] using hmapped
    have hgdet : g.1.1.1.det = 1 :=
      (L.mem_infiniteAdelicSpecialOrthogonalMatrixSubgroup_iff g.1).mp g.2
    have hDet : mapped.1.det = 1 := by
      have hmap := congrArg Units.val
        (Matrix.GeneralLinearGroup.map_det
          (f := rationalInfiniteAdeleRingEquivReal.toRingHom) g.1.1)
      simpa [mapped, infiniteAdelicGeneralLinearGroupEquivReal, hgdet] using hmap
    exact
      ⟨⟨mapped, hForm⟩,
        (L.mem_realSpecialOrthogonalMatrixSubgroup_iff
          ⟨mapped, hForm⟩).2 hDet⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact L.infiniteAdelicGeneralLinearGroupEquivReal.map_one
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    exact L.infiniteAdelicGeneralLinearGroupEquivReal.map_mul g.1.1 h.1.1

/-- The entrywise map from infinite-adelic to real special orthogonal matrices
is bijective. -/
theorem infiniteAdelicSpecialOrthogonalToRealHom_bijective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Bijective L.infiniteAdelicSpecialOrthogonalToRealHom := by
  constructor
  · intro g h heq
    apply Subtype.ext
    apply Subtype.ext
    apply L.infiniteAdelicGeneralLinearGroupEquivReal.injective
    exact congrArg (fun z ↦ z.1.1) heq
  · intro y
    let E := L.infiniteAdelicGeneralLinearGroupEquivReal
    let G : GL (Fin n) RationalInfiniteAdele := E.symm y.1.1
    have hGL : E G = y.1.1 := E.apply_symm_apply _
    have hMatrix :
        G.1.map rationalInfiniteAdeleRingEquivReal = y.1.1.1 := by
      exact congrArg Units.val hGL
    have hForm :
        G.1ᵀ * L.infiniteAdelicFormMatrix * G.1 =
          L.infiniteAdelicFormMatrix := by
      apply rationalInfiniteAdeleRingEquivReal.mapMatrix.injective
      simp only [map_mul, RingEquiv.mapMatrix_apply, Matrix.transpose_map,
        L.infiniteAdelicFormMatrix_map_equivReal]
      rw [hMatrix]
      exact y.1.2
    have hDet : G.1.det = 1 := by
      apply rationalInfiniteAdeleRingEquivReal.injective
      calc
        rationalInfiniteAdeleRingEquivReal G.1.det =
            (G.1.map rationalInfiniteAdeleRingEquivReal).det :=
          RingHom.map_det rationalInfiniteAdeleRingEquivReal.toRingHom G.1
        _ = y.1.1.1.det := congrArg Matrix.det hMatrix
        _ = 1 :=
          (L.mem_realSpecialOrthogonalMatrixSubgroup_iff y.1).mp y.2
        _ = rationalInfiniteAdeleRingEquivReal 1 := by simp
    let gOrth : L.ConcreteInfiniteAdelicOrthogonalGroup := ⟨G, hForm⟩
    let gSpecial : L.ConcreteInfiniteAdelicSpecialOrthogonalGroup :=
      ⟨gOrth,
        (L.mem_infiniteAdelicSpecialOrthogonalMatrixSubgroup_iff gOrth).2 hDet⟩
    refine ⟨gSpecial, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hGL

/-- The rational infinite-adelic special orthogonal group is algebraically
the concrete real special orthogonal group. -/
def infiniteAdelicSpecialOrthogonalGroupEquivReal (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteInfiniteAdelicSpecialOrthogonalGroup ≃*
      L.ConcreteRealSpecialOrthogonalGroup :=
  MulEquiv.ofBijective L.infiniteAdelicSpecialOrthogonalToRealHom
    L.infiniteAdelicSpecialOrthogonalToRealHom_bijective

/-! ## Topological identification of the infinite and real factors -/

/-- The algebraic identification of the unique rational infinite completion
with `ℝ`, bundled as a homeomorphism. -/
def rationalInfiniteAdeleHomeomorphReal : RationalInfiniteAdele ≃ₜ ℝ := by
  letI : Unique (NumberField.InfinitePlace ℚ) :=
    { default := Rat.infinitePlace
      uniq := fun v => Subsingleton.elim v Rat.infinitePlace }
  exact
    (Homeomorph.piUnique
      (fun v : NumberField.InfinitePlace ℚ ↦ v.Completion)).trans
        (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
          Rat.isReal_infinitePlace).toHomeomorph

@[simp]
theorem rationalInfiniteAdeleHomeomorphReal_apply (x : RationalInfiniteAdele) :
    rationalInfiniteAdeleHomeomorphReal x =
      rationalInfiniteAdeleRingEquivReal x :=
  rfl

/-- Entrywise application of the rational infinite-adele homeomorphism is a
continuous multiplicative equivalence of square matrix rings. -/
def rationalInfiniteAdeleMatrixContinuousMulEquivReal :
    Matrix (Fin n) (Fin n) RationalInfiniteAdele ≃ₜ*
      Matrix (Fin n) (Fin n) ℝ :=
  ContinuousMulEquiv.mk'
    (Homeomorph.piCongrRight fun _ =>
      Homeomorph.piCongrRight fun _ => rationalInfiniteAdeleHomeomorphReal)
    (by
      intro A B
      ext i j
      change rationalInfiniteAdeleRingEquivReal ((A * B) i j) =
        ∑ x, rationalInfiniteAdeleRingEquivReal (A i x) *
          rationalInfiniteAdeleRingEquivReal (B x j)
      simp [Matrix.mul_apply])

/-- The ambient general-linear equivalence between the rational infinite
adeles and `ℝ` is a topological group equivalence. -/
def infiniteAdelicGeneralLinearGroupContinuousEquivReal
    (_L : PositiveDefiniteIntegralLattice n) :
    GL (Fin n) RationalInfiniteAdele ≃ₜ* GL (Fin n) ℝ :=
  Units.mapContinuousMulEquiv rationalInfiniteAdeleMatrixContinuousMulEquivReal

/-- The algebraic equivalence `SO(L)(A_∞) ≃ SO(L)(ℝ)` is a topological group
equivalence. -/
def infiniteAdelicSpecialOrthogonalGroupContinuousEquivReal
    (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteInfiniteAdelicSpecialOrthogonalGroup ≃ₜ*
      L.ConcreteRealSpecialOrthogonalGroup where
  toMulEquiv := L.infiniteAdelicSpecialOrthogonalGroupEquivReal
  continuous_toFun := by
    exact ((L.infiniteAdelicGeneralLinearGroupContinuousEquivReal.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    refine (L.infiniteAdelicGeneralLinearGroupContinuousEquivReal.symm.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).congr ?_
    intro y
    symm
    apply L.infiniteAdelicGeneralLinearGroupContinuousEquivReal.injective
    change L.infiniteAdelicGeneralLinearGroupContinuousEquivReal
        (L.infiniteAdelicSpecialOrthogonalGroupEquivReal.symm y).1.1 =
      L.infiniteAdelicGeneralLinearGroupContinuousEquivReal
        (L.infiniteAdelicGeneralLinearGroupContinuousEquivReal.symm y.1.1)
    calc
      _ = y.1.1 := congrArg (fun z => z.1.1)
        (L.infiniteAdelicSpecialOrthogonalGroupEquivReal.apply_symm_apply y)
      _ = _ :=
        (L.infiniteAdelicGeneralLinearGroupContinuousEquivReal.apply_symm_apply
          y.1.1).symm

/-! ## Full-adelic special orthogonal group -/

/-- The form matrix of `L`, transported from `ℤ` to the full adeles of `ℚ`. -/
def fullAdelicFormMatrix (L : PositiveDefiniteIntegralLattice n) :
    Matrix (Fin n) (Fin n) RationalAdele :=
  L.pairingMatrix.map (algebraMap ℤ RationalAdele)

/-- The concrete full-adelic orthogonal matrix group attached to `L`. -/
def fullAdelicOrthogonalMatrixSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup (Matrix (Fin n) (Fin n) RationalAdele)ˣ :=
  formPreservingMatrixSubgroup L.fullAdelicFormMatrix

/-- The concrete carrier of `O(L)(A)`. -/
abbrev ConcreteFullAdelicOrthogonalGroup (L : PositiveDefiniteIntegralLattice n) :=
  L.fullAdelicOrthogonalMatrixSubgroup

@[simp]
theorem mem_fullAdelicOrthogonalMatrixSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n)
    (g : (Matrix (Fin n) (Fin n) RationalAdele)ˣ) :
    g ∈ L.fullAdelicOrthogonalMatrixSubgroup ↔
      g.1ᵀ * L.fullAdelicFormMatrix * g.1 = L.fullAdelicFormMatrix :=
  Iff.rfl

/-- The determinant-one subgroup of the full-adelic orthogonal group. -/
def fullAdelicSpecialOrthogonalMatrixSubgroup (L : PositiveDefiniteIntegralLattice n) :
    Subgroup L.ConcreteFullAdelicOrthogonalGroup :=
  specialFormPreservingMatrixSubgroup L.fullAdelicFormMatrix

/-- The concrete carrier of `SO(L)(A)`. -/
abbrev ConcreteFullAdelicSpecialOrthogonalGroup (L : PositiveDefiniteIntegralLattice n) :=
  L.fullAdelicSpecialOrthogonalMatrixSubgroup

@[simp]
theorem mem_fullAdelicSpecialOrthogonalMatrixSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (g : L.ConcreteFullAdelicOrthogonalGroup) :
    g ∈ L.fullAdelicSpecialOrthogonalMatrixSubgroup ↔ g.1.1.det = 1 :=
  mem_specialFormPreservingMatrixSubgroup_iff L.fullAdelicFormMatrix g

/-- The infinite projection of the full-adelic form matrix. -/
theorem fullAdelicFormMatrix_map_fst (L : PositiveDefiniteIntegralLattice n) :
    L.fullAdelicFormMatrix.map
      (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) =
        L.infiniteAdelicFormMatrix := by
  ext i j
  rfl

/-- The finite projection of the full-adelic form matrix. -/
theorem fullAdelicFormMatrix_map_snd (L : PositiveDefiniteIntegralLattice n) :
    L.fullAdelicFormMatrix.map
      (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) =
        L.finiteAdelicFormMatrix := by
  apply Matrix.ext
  intro i j
  change
    (RingHom.snd RationalInfiniteAdele RationalFiniteAdele)
        (algebraMap ℤ RationalAdele (L.pairingMatrix i j)) =
      algebraMap ℤ RationalFiniteAdele (L.pairingMatrix i j)
  exact DFunLike.congr_fun
    (RingHom.ext_int
      ((RingHom.snd RationalInfiniteAdele RationalFiniteAdele).comp
        (algebraMap ℤ RationalAdele))
      (algebraMap ℤ RationalFiniteAdele))
    (L.pairingMatrix i j)

/-- The ambient general linear group over the full rational adeles splits
into its infinite and finite factors. -/
def fullAdelicGeneralLinearGroupProdEquiv (_L : PositiveDefiniteIntegralLattice n) :
    GL (Fin n) RationalAdele ≃*
      GL (Fin n) RationalInfiniteAdele × GL (Fin n) RationalFiniteAdele :=
  generalLinearGroupProdEquiv

/-- The ambient full-adelic general-linear product equivalence is a
topological group equivalence. -/
def fullAdelicGeneralLinearGroupProdContinuousEquiv (_L : PositiveDefiniteIntegralLattice n) :
    GL (Fin n) RationalAdele ≃ₜ*
      GL (Fin n) RationalInfiniteAdele × GL (Fin n) RationalFiniteAdele :=
  generalLinearGroupProdContinuousEquiv

@[simp]
theorem fullAdelicGeneralLinearGroupProdEquiv_apply_fst
    (L : PositiveDefiniteIntegralLattice n) (g : GL (Fin n) RationalAdele) :
    ((L.fullAdelicGeneralLinearGroupProdEquiv g).1 :
        Matrix (Fin n) (Fin n) RationalInfiniteAdele) =
      g.1.map (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) :=
  rfl

@[simp]
theorem fullAdelicGeneralLinearGroupProdEquiv_apply_snd
    (L : PositiveDefiniteIntegralLattice n) (g : GL (Fin n) RationalAdele) :
    ((L.fullAdelicGeneralLinearGroupProdEquiv g).2 :
        Matrix (Fin n) (Fin n) RationalFiniteAdele) =
      g.1.map (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Projection of a full-adelic special orthogonal matrix to its infinite and
finite special orthogonal components. -/
def fullAdelicSpecialOrthogonalToProdHom (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteFullAdelicSpecialOrthogonalGroup →*
      L.ConcreteInfiniteAdelicSpecialOrthogonalGroup ×
        L.ConcreteFiniteAdelicSpecialOrthogonalGroup where
  toFun g := by
    let gInf := Matrix.GeneralLinearGroup.map
      (n := Fin n)
      (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) g.1.1
    let gFin := Matrix.GeneralLinearGroup.map
      (n := Fin n)
      (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) g.1.1
    have hInfForm : gInf ∈ L.infiniteAdelicOrthogonalMatrixSubgroup := by
      rw [L.mem_infiniteAdelicOrthogonalMatrixSubgroup_iff]
      have hmapped := congrArg
        (RingHom.fst RationalInfiniteAdele RationalFiniteAdele).mapMatrix g.1.2
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map,
        L.fullAdelicFormMatrix_map_fst] at hmapped
      simpa [gInf] using hmapped
    have hFinForm : gFin ∈ L.finiteAdelicOrthogonalMatrixSubgroup := by
      rw [L.mem_finiteAdelicOrthogonalMatrixSubgroup_iff]
      have hmapped := congrArg
        (RingHom.snd RationalInfiniteAdele RationalFiniteAdele).mapMatrix g.1.2
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map,
        L.fullAdelicFormMatrix_map_snd] at hmapped
      simpa [gFin] using hmapped
    have hgdet : g.1.1.1.det = 1 :=
      (L.mem_fullAdelicSpecialOrthogonalMatrixSubgroup_iff g.1).mp g.2
    have hInfDet : gInf.1.det = 1 := by
      change ((RingHom.fst RationalInfiniteAdele RationalFiniteAdele).mapMatrix
        g.1.1.1).det = 1
      rw [← RingHom.map_det, hgdet, map_one]
    have hFinDet : gFin.1.det = 1 := by
      change ((RingHom.snd RationalInfiniteAdele RationalFiniteAdele).mapMatrix
        g.1.1.1).det = 1
      rw [← RingHom.map_det, hgdet, map_one]
    exact
      (⟨⟨gInf, hInfForm⟩,
          (L.mem_infiniteAdelicSpecialOrthogonalMatrixSubgroup_iff
            ⟨gInf, hInfForm⟩).2 hInfDet⟩,
        ⟨⟨gFin, hFinForm⟩,
          (L.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff
            ⟨gFin, hFinForm⟩).2 hFinDet⟩)
  map_one' := by
    apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext
    · exact Matrix.GeneralLinearGroup.map_one
        (n := Fin n)
        (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)
    · exact Matrix.GeneralLinearGroup.map_one
        (n := Fin n)
        (RingHom.snd RationalInfiniteAdele RationalFiniteAdele)
  map_mul' g h := by
    apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext
    · exact Matrix.GeneralLinearGroup.map_mul
        (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) g.1.1 h.1.1
    · exact Matrix.GeneralLinearGroup.map_mul
        (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) g.1.1 h.1.1

set_option backward.isDefEq.respectTransparency false in
/-- The component projection on full-adelic special orthogonal matrices is
bijective. -/
theorem fullAdelicSpecialOrthogonalToProdHom_bijective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Bijective L.fullAdelicSpecialOrthogonalToProdHom := by
  constructor
  · intro g h heq
    apply Subtype.ext
    apply Subtype.ext
    apply L.fullAdelicGeneralLinearGroupProdEquiv.injective
    apply Prod.ext
    · exact congrArg (fun z ↦ z.1.1.1) heq
    · exact congrArg (fun z ↦ z.2.1.1) heq
  · intro y
    let E := L.fullAdelicGeneralLinearGroupProdEquiv
    let G : GL (Fin n) RationalAdele := E.symm (y.1.1.1, y.2.1.1)
    have hcomponents : E G = (y.1.1.1, y.2.1.1) := E.apply_symm_apply _
    have hInfGL :
        Matrix.GeneralLinearGroup.map
            (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) G =
          y.1.1.1 := by
      exact congrArg Prod.fst hcomponents
    have hFinGL :
        Matrix.GeneralLinearGroup.map
            (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) G =
          y.2.1.1 := by
      exact congrArg Prod.snd hcomponents
    have hInfMatrix :
        G.1.map (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) =
          y.1.1.1.1 := by
      exact congrArg Units.val hInfGL
    have hFinMatrix :
        G.1.map (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) =
          y.2.1.1.1 := by
      exact congrArg Units.val hFinGL
    have hFullForm :
        G.1ᵀ * L.fullAdelicFormMatrix * G.1 = L.fullAdelicFormMatrix := by
      apply (matrixProdRingEquiv
        (ι := Fin n) (R := RationalInfiniteAdele)
        (S := RationalFiniteAdele)).injective
      apply Prod.ext
      · change (RingHom.fst RationalInfiniteAdele RationalFiniteAdele).mapMatrix
            (G.1ᵀ * L.fullAdelicFormMatrix * G.1) =
          (RingHom.fst RationalInfiniteAdele RationalFiniteAdele).mapMatrix
            L.fullAdelicFormMatrix
        rw [map_mul, map_mul]
        change (G.1ᵀ).map (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) *
              L.fullAdelicFormMatrix.map
                (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) *
              G.1.map (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) =
            L.fullAdelicFormMatrix.map
              (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)
        rw [Matrix.transpose_map, L.fullAdelicFormMatrix_map_fst, hInfMatrix]
        exact y.1.1.2
      · change (RingHom.snd RationalInfiniteAdele RationalFiniteAdele).mapMatrix
            (G.1ᵀ * L.fullAdelicFormMatrix * G.1) =
          (RingHom.snd RationalInfiniteAdele RationalFiniteAdele).mapMatrix
            L.fullAdelicFormMatrix
        rw [map_mul, map_mul]
        change (G.1ᵀ).map (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) *
              L.fullAdelicFormMatrix.map
                (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) *
              G.1.map (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) =
            L.fullAdelicFormMatrix.map
              (RingHom.snd RationalInfiniteAdele RationalFiniteAdele)
        rw [Matrix.transpose_map, L.fullAdelicFormMatrix_map_snd, hFinMatrix]
        exact y.2.1.2
    have hFullDet : G.1.det = 1 := by
      apply Prod.ext
      · calc
          G.1.det.1 =
              (G.1.map
                (RingHom.fst RationalInfiniteAdele RationalFiniteAdele)).det :=
            RingHom.map_det
              (RingHom.fst RationalInfiniteAdele RationalFiniteAdele) G.1
          _ = y.1.1.1.1.det := congrArg Matrix.det hInfMatrix
          _ = 1 :=
            (L.mem_infiniteAdelicSpecialOrthogonalMatrixSubgroup_iff y.1.1).mp
              y.1.2
      · calc
          G.1.det.2 =
              (G.1.map
                (RingHom.snd RationalInfiniteAdele RationalFiniteAdele)).det :=
            RingHom.map_det
              (RingHom.snd RationalInfiniteAdele RationalFiniteAdele) G.1
          _ = y.2.1.1.1.det := congrArg Matrix.det hFinMatrix
          _ = 1 :=
            (L.mem_finiteAdelicSpecialOrthogonalMatrixSubgroup_iff y.2.1).mp
              y.2.2
    let gOrth : L.ConcreteFullAdelicOrthogonalGroup := ⟨G, hFullForm⟩
    let gSpecial : L.ConcreteFullAdelicSpecialOrthogonalGroup :=
      ⟨gOrth,
        (L.mem_fullAdelicSpecialOrthogonalMatrixSubgroup_iff gOrth).2 hFullDet⟩
    refine ⟨gSpecial, ?_⟩
    apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext
    · exact hInfGL
    · exact hFinGL

/-- The full-adelic special orthogonal group is the product of its infinite
and finite adelic factors. -/
def fullAdelicSpecialOrthogonalGroupProdEquiv (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteFullAdelicSpecialOrthogonalGroup ≃*
      L.ConcreteInfiniteAdelicSpecialOrthogonalGroup ×
        L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
  MulEquiv.ofBijective L.fullAdelicSpecialOrthogonalToProdHom
    L.fullAdelicSpecialOrthogonalToProdHom_bijective

/-- The algebraic splitting of the full-adelic special orthogonal group is a
topological group equivalence. -/
def fullAdelicSpecialOrthogonalGroupProdContinuousEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteFullAdelicSpecialOrthogonalGroup ≃ₜ*
      L.ConcreteInfiniteAdelicSpecialOrthogonalGroup ×
        L.ConcreteFiniteAdelicSpecialOrthogonalGroup where
  toMulEquiv := L.fullAdelicSpecialOrthogonalGroupProdEquiv
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (((L.fullAdelicGeneralLinearGroupProdContinuousEquiv.continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val)).fst).subtype_mk _).subtype_mk _
    · exact (((L.fullAdelicGeneralLinearGroupProdContinuousEquiv.continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val)).snd).subtype_mk _).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    let componentVals := fun y :
        L.ConcreteInfiniteAdelicSpecialOrthogonalGroup ×
          L.ConcreteFiniteAdelicSpecialOrthogonalGroup =>
      (y.1.1.1, y.2.1.1)
    have hcomponentVals : Continuous componentVals := by
      apply Continuous.prodMk
      · exact (continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst
      · exact (continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd
    refine (L.fullAdelicGeneralLinearGroupProdContinuousEquiv.symm.continuous.comp
      hcomponentVals).congr ?_
    intro y
    symm
    apply L.fullAdelicGeneralLinearGroupProdContinuousEquiv.injective
    change L.fullAdelicGeneralLinearGroupProdContinuousEquiv
        (L.fullAdelicSpecialOrthogonalGroupProdEquiv.symm y).1.1 =
      L.fullAdelicGeneralLinearGroupProdContinuousEquiv
        (L.fullAdelicGeneralLinearGroupProdContinuousEquiv.symm (componentVals y))
    calc
      _ = componentVals y := congrArg (fun z => (z.1.1.1, z.2.1.1))
        (L.fullAdelicSpecialOrthogonalGroupProdEquiv.apply_symm_apply y)
      _ = _ :=
        (L.fullAdelicGeneralLinearGroupProdContinuousEquiv.apply_symm_apply
          (componentVals y)).symm

/-- The full-adelic special orthogonal group splits topologically into its
concrete real and finite-adelic factors. -/
def fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
    (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteFullAdelicSpecialOrthogonalGroup ≃ₜ*
      L.ConcreteRealSpecialOrthogonalGroup ×
        L.ConcreteFiniteAdelicSpecialOrthogonalGroup :=
  L.fullAdelicSpecialOrthogonalGroupProdContinuousEquiv.trans
    (prodContinuousMulEquiv
      L.infiniteAdelicSpecialOrthogonalGroupContinuousEquivReal
      (ContinuousMulEquiv.refl _))

/-! ## Reference Haar measure on the full adelic group -/

/-- The reference product Haar measure on the real and finite-adelic factors.
Both factors use mass-one compact normalizations; this is not the
Tamagawa measure induced by a rational invariant differential. -/
noncomputable def concreteRealFiniteSpecialOrthogonalReferenceHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    Measure (L.ConcreteRealSpecialOrthogonalGroup ×
      L.ConcreteFiniteAdelicSpecialOrthogonalGroup) :=
  L.concreteRealSpecialOrthogonalNormalizedHaarMeasure.prod
    L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure

instance concreteRealFiniteSpecialOrthogonalReferenceHaarMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.IsMulLeftInvariant
      L.concreteRealFiniteSpecialOrthogonalReferenceHaarMeasure := by
  unfold concreteRealFiniteSpecialOrthogonalReferenceHaarMeasure
  letI : Measure.IsMulLeftInvariant
      L.concreteRealSpecialOrthogonalNormalizedHaarMeasure :=
    concreteRealSpecialOrthogonalNormalizedHaarMeasure_isMulLeftInvariant L
  letI : Measure.IsMulLeftInvariant
      L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure :=
    concreteFiniteAdelicSpecialOrthogonalHaarMeasure_isMulLeftInvariant L
  letI : SigmaFinite
      L.concreteRealSpecialOrthogonalNormalizedHaarMeasure :=
    concreteRealSpecialOrthogonalNormalizedHaarMeasure_isSigmaFinite L
  letI : Measure.IsHaarMeasure
      L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure := by
    unfold concreteFiniteAdelicSpecialOrthogonalHaarMeasure
    infer_instance
  letI : SigmaFinite
      L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure := by
    infer_instance
  exact Measure.prod.instIsMulLeftInvariant

instance concreteRealFiniteSpecialOrthogonalReferenceHaarMeasure_isSigmaFinite
    (L : PositiveDefiniteIntegralLattice n) :
    SigmaFinite L.concreteRealFiniteSpecialOrthogonalReferenceHaarMeasure := by
  unfold concreteRealFiniteSpecialOrthogonalReferenceHaarMeasure
  letI : SigmaFinite
      L.concreteRealSpecialOrthogonalNormalizedHaarMeasure :=
    concreteRealSpecialOrthogonalNormalizedHaarMeasure_isSigmaFinite L
  letI : Measure.IsHaarMeasure
      L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure := by
    unfold concreteFiniteAdelicSpecialOrthogonalHaarMeasure
    infer_instance
  letI : SigmaFinite
      L.concreteFiniteAdelicSpecialOrthogonalHaarMeasure := by
    infer_instance
  exact Measure.prod.instSigmaFinite

/-- The full adelic special orthogonal group carries its inherited Borel
measurable space. -/
instance concreteFullAdelicSpecialOrthogonalGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableSpace L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  borel L.ConcreteFullAdelicSpecialOrthogonalGroup

instance concreteFullAdelicSpecialOrthogonalGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice n) :
    BorelSpace L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  ⟨rfl⟩

/-- The reference Haar measure on the full adelic group, transported from the
real/finite product normalization. -/
noncomputable def concreteFullAdelicSpecialOrthogonalReferenceHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) :
    Measure L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  Measure.map
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm
    L.concreteRealFiniteSpecialOrthogonalReferenceHaarMeasure

/-- The real/finite splitting pushes the full reference measure back to the
product of the two normalized factor measures. -/
theorem concreteFullAdelicSpecialOrthogonalReferenceHaarMeasure_map_eq
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.map L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        L.concreteFullAdelicSpecialOrthogonalReferenceHaarMeasure =
      L.concreteRealFiniteSpecialOrthogonalReferenceHaarMeasure := by
  rw [concreteFullAdelicSpecialOrthogonalReferenceHaarMeasure,
    Measure.map_map]
  · simp
  · exact L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
      |>.continuous.measurable
  · exact L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm
      |>.continuous.measurable

instance concreteFullAdelicSpecialOrthogonalReferenceHaarMeasure_isSigmaFinite
    (L : PositiveDefiniteIntegralLattice n) :
    SigmaFinite L.concreteFullAdelicSpecialOrthogonalReferenceHaarMeasure := by
  unfold concreteFullAdelicSpecialOrthogonalReferenceHaarMeasure
  letI : SigmaFinite
      L.concreteRealFiniteSpecialOrthogonalReferenceHaarMeasure :=
    concreteRealFiniteSpecialOrthogonalReferenceHaarMeasure_isSigmaFinite L
  exact L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm
    |>.toHomeomorph.toMeasurableEquiv.sigmaFinite_map

instance concreteFullAdelicSpecialOrthogonalReferenceHaarMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) :
    Measure.IsMulLeftInvariant
      L.concreteFullAdelicSpecialOrthogonalReferenceHaarMeasure := by
  unfold concreteFullAdelicSpecialOrthogonalReferenceHaarMeasure
  letI : Measure.IsMulLeftInvariant
      L.concreteRealFiniteSpecialOrthogonalReferenceHaarMeasure :=
    concreteRealFiniteSpecialOrthogonalReferenceHaarMeasure_isMulLeftInvariant L
  exact isMulLeftInvariant_map
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.toMulHom
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.continuous.measurable
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.symm.surjective

/-- The full-adelic form matrix is the diagonal image of the rational form
matrix. -/
theorem fullAdelicFormMatrix_eq_map_rationalFormMatrix
    (L : PositiveDefiniteIntegralLattice n) :
    L.fullAdelicFormMatrix =
      L.rationalFormMatrix.map (algebraMap ℚ RationalAdele) := by
  ext i j
  simp [fullAdelicFormMatrix, rationalFormMatrix]

/-- The diagonal homomorphism from rational orthogonal matrices to the
full-adelic orthogonal group. -/
def rationalOrthogonalFullAdelicDiagonalHom (L : PositiveDefiniteIntegralLattice n) :
    L.rationalOrthogonalMatrixSubgroup →*
      L.ConcreteFullAdelicOrthogonalGroup where
  toFun g := by
    let mapped := Matrix.GeneralLinearGroup.map
      (n := Fin n) (algebraMap ℚ RationalAdele) g.1
    refine ⟨mapped, ?_⟩
    rw [L.mem_fullAdelicOrthogonalMatrixSubgroup_iff,
      L.fullAdelicFormMatrix_eq_map_rationalFormMatrix]
    have hmapped := congrArg
      (fun M ↦ M.map (algebraMap ℚ RationalAdele)) g.2
    simpa [mapped, Matrix.map_mul, Matrix.transpose_map] using hmapped
  map_one' := by
    apply Subtype.ext
    exact Matrix.GeneralLinearGroup.map_one
      (n := Fin n) (algebraMap ℚ RationalAdele)
  map_mul' g h := by
    apply Subtype.ext
    exact Matrix.GeneralLinearGroup.map_mul
      (n := Fin n) (algebraMap ℚ RationalAdele) g.1 h.1

@[simp]
theorem rationalOrthogonalFullAdelicDiagonalHom_apply_matrix
    (L : PositiveDefiniteIntegralLattice n) (g : L.rationalOrthogonalMatrixSubgroup) :
    (L.rationalOrthogonalFullAdelicDiagonalHom g).1.1 =
      g.1.1.map (algebraMap ℚ RationalAdele) := by
  rfl

/-- The rational diagonal embedding restricted to determinant-one matrices. -/
def rationalSpecialOrthogonalFullAdelicDiagonalHom (L : PositiveDefiniteIntegralLattice n) :
    L.rationalSpecialOrthogonalMatrixSubgroup →*
      L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  (L.rationalOrthogonalFullAdelicDiagonalHom.restrict
      L.rationalSpecialOrthogonalMatrixSubgroup).codRestrict
    L.fullAdelicSpecialOrthogonalMatrixSubgroup (by
      intro g
      rw [L.mem_fullAdelicSpecialOrthogonalMatrixSubgroup_iff]
      have hdet : g.1.1.1.det = 1 :=
        (L.mem_rationalSpecialOrthogonalMatrixSubgroup_iff g.1).mp g.2
      change
        (Matrix.GeneralLinearGroup.map
          (algebraMap ℚ RationalAdele) g.1.1).1.det = 1
      have hmap := congrArg Units.val
        (Matrix.GeneralLinearGroup.map_det
          (f := algebraMap ℚ RationalAdele) g.1.1)
      simpa [hdet] using hmap)

@[simp]
theorem rationalSpecialOrthogonalFullAdelicDiagonalHom_apply
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.rationalSpecialOrthogonalMatrixSubgroup) :
    (L.rationalSpecialOrthogonalFullAdelicDiagonalHom g).1 =
      L.rationalOrthogonalFullAdelicDiagonalHom g.1 :=
  rfl

/-- The diagonal rational `SO(L)(ℚ)` subgroup inside `SO(L)(A)`. -/
def rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
    (L : PositiveDefiniteIntegralLattice n) :
    Subgroup L.ConcreteFullAdelicSpecialOrthogonalGroup :=
  L.rationalSpecialOrthogonalFullAdelicDiagonalHom.range

end PositiveDefiniteIntegralLattice

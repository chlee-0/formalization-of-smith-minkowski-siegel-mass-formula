import SMSFormula.QuadraticComplement
import SMSFormula.RationalIsotropy

/-!
# Matrix congruence and isotropy

This module contains the matrix-congruence API used by the direct
Hasse--Minkowski proof and by the adelic files.
-/

noncomputable section

open scoped Matrix

namespace Matrix

variable {n : ℕ}

/-- Two square matrices are congruent when an invertible change of basis
transports the first to the second. -/
def IsCongruent {R : Type*} [CommRing R]
    (A B : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ T : GL (Fin n) R, T.1ᵀ * A * T.1 = B

namespace IsCongruent

theorem refl {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) : A.IsCongruent A := by
  refine ⟨1, ?_⟩
  simp

theorem symm {R : Type*} [CommRing R]
    {A B : Matrix (Fin n) (Fin n) R}
    (h : A.IsCongruent B) : B.IsCongruent A := by
  rcases h with ⟨T, hT⟩
  refine ⟨T⁻¹, ?_⟩
  have hleft : (T⁻¹).1ᵀ * T.1ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    have hval : T.1 * (T⁻¹).1 = 1 := by
      change (T * T⁻¹).1 = 1
      simp
    rw [hval]
    simp
  have hright : T.1 * (T⁻¹).1 = 1 := by
    change (T * T⁻¹).1 = 1
    simp
  calc
    (T⁻¹).1ᵀ * B * (T⁻¹).1 =
        (T⁻¹).1ᵀ * (T.1ᵀ * A * T.1) * (T⁻¹).1 := by rw [hT]
    _ = ((T⁻¹).1ᵀ * T.1ᵀ) * A * (T.1 * (T⁻¹).1) := by
      simp only [Matrix.mul_assoc]
    _ = A := by rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]

theorem trans {R : Type*} [CommRing R]
    {A B C : Matrix (Fin n) (Fin n) R}
    (hAB : A.IsCongruent B) (hBC : B.IsCongruent C) :
    A.IsCongruent C := by
  rcases hAB with ⟨T, hT⟩
  rcases hBC with ⟨U, hU⟩
  refine ⟨T * U, ?_⟩
  change (T.1 * U.1)ᵀ * A * (T.1 * U.1) = C
  rw [Matrix.transpose_mul]
  calc
    (U.1ᵀ * T.1ᵀ) * A * (T.1 * U.1) =
        U.1ᵀ * (T.1ᵀ * A * T.1) * U.1 := by
      simp only [Matrix.mul_assoc]
    _ = C := by rw [hT, hU]

theorem map {R S : Type*} [CommRing R] [CommRing S]
    {A B : Matrix (Fin n) (Fin n) R}
    (h : A.IsCongruent B) (f : R →+* S) :
    (A.map f).IsCongruent (B.map f) := by
  rcases h with ⟨T, hT⟩
  refine ⟨Matrix.GeneralLinearGroup.map f T, ?_⟩
  have hmap := congrArg (fun M ↦ M.map f) hT
  simpa [Matrix.map_mul, Matrix.transpose_map] using hmap

end IsCongruent

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The quadratic value of a leading Gram block splits into its head term and
the quadratic value of the tail coordinates. -/
theorem gramQuadraticValue_finSuccGramBlock
    {K : Type*} [Field K] (c : K)
    (A : Matrix (Fin n) (Fin n) K) (x : Fin (n + 1) → K) :
    gramQuadraticValue (finSuccGramBlock c A) x =
      c * x 0 ^ 2 + gramQuadraticValue A (fun i ↦ x i.succ) := by
  simp [gramQuadraticValue, finSuccGramBlock, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, pow_two]
  ring_nf

/-- Scaling a vector scales its Gram quadratic value by the square of the
scalar. -/
theorem gramQuadraticValue_smul_vector
    {K : Type*} [Field K] (A : Matrix (Fin n) (Fin n) K)
    (r : K) (x : Fin n → K) :
    gramQuadraticValue A (r • x) = r ^ 2 * gramQuadraticValue A x := by
  simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Finset.mul_sum]
  ring_nf

/-- Two binary Gram forms represent the same scalar. -/
def BinaryCommonRepresents
    {K : Type*} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) (c : K) : Prop :=
  (∃ u : Fin 2 → K, gramQuadraticValue A u = c) ∧
    ∃ v : Fin 2 → K, gramQuadraticValue B v = c

/-- A common represented value remains common after multiplication by a
square. -/
theorem BinaryCommonRepresents.sq_mul
    {K : Type*} [Field K]
    {A B : Matrix (Fin 2) (Fin 2) K} {c : K}
    (hcommon : BinaryCommonRepresents A B c) (s : K) :
    BinaryCommonRepresents A B (s ^ 2 * c) := by
  rcases hcommon with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  refine ⟨⟨s • u, ?_⟩, ⟨s • v, ?_⟩⟩
  · rw [gramQuadraticValue_smul_vector, hu]
  · rw [gramQuadraticValue_smul_vector, hv]

/-- A binary and a ternary Gram form represent the same scalar. -/
def BinaryTernaryCommonRepresents
    {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K)
    (B : Matrix (Fin 3) (Fin 3) K) (c : K) : Prop :=
  (∃ u : Fin 2 → K, gramQuadraticValue A u = c) ∧
    ∃ v : Fin 3 → K, gramQuadraticValue B v = c

/-- A common binary--ternary represented value remains common after
multiplication by a square. -/
theorem BinaryTernaryCommonRepresents.sq_mul
    {K : Type*} [Field K]
    {A : Matrix (Fin 2) (Fin 2) K}
    {B : Matrix (Fin 3) (Fin 3) K} {c : K}
    (hcommon : BinaryTernaryCommonRepresents A B c) (s : K) :
    BinaryTernaryCommonRepresents A B (s ^ 2 * c) := by
  rcases hcommon with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  refine ⟨⟨s • u, ?_⟩, ⟨s • v, ?_⟩⟩
  · rw [gramQuadraticValue_smul_vector, hu]
  · rw [gramQuadraticValue_smul_vector, hv]

/-- A value represented by `A` gives an isotropic vector after adjoining a
leading line with the negative of that value. -/
theorem gramIsotropic_finSuccGramBlock_of_exists_value
    {K : Type*} [Field K] (c : K)
    (A : Matrix (Fin n) (Fin n) K)
    (hrep : ∃ v : Fin n → K, gramQuadraticValue A v = c) :
    GramIsotropic (finSuccGramBlock (-c) A) := by
  obtain ⟨v, hv⟩ := hrep
  refine ⟨Fin.cases 1 v, ?_, ?_⟩
  · intro hzero
    have h := congrFun hzero 0
    simp at h
  · rw [gramQuadraticValue_finSuccGramBlock]
    simp [hv]

/-- An isotropic vector for a one-line extension either has zero head and
exposes an isotropic tail, or has nonzero head and rescales to a vector of the
represented value. -/
theorem gramIsotropic_or_exists_value_of_finSuccGramBlock
    {K : Type*} [Field K] (c : K)
    (A : Matrix (Fin n) (Fin n) K)
    (hiso : GramIsotropic (finSuccGramBlock (-c) A)) :
    GramIsotropic A ∨ ∃ v : Fin n → K, gramQuadraticValue A v = c := by
  obtain ⟨x, hx, hvalue⟩ := hiso
  rw [gramQuadraticValue_finSuccGramBlock] at hvalue
  by_cases hhead : x 0 = 0
  · left
    refine ⟨fun i ↦ x i.succ, ?_, ?_⟩
    · intro htail
      apply hx
      funext i
      refine Fin.cases hhead (fun j ↦ ?_) i
      exact congrFun htail j
    · simpa [hhead] using hvalue
  · right
    refine ⟨(x 0)⁻¹ • (fun i ↦ x i.succ), ?_⟩
    rw [gramQuadraticValue_smul_vector]
    have htail : gramQuadraticValue A (fun i ↦ x i.succ) = c * x 0 ^ 2 := by
      linear_combination hvalue
    rw [htail]
    field_simp [hhead]

/-- If the tail form is anisotropic, adjoining a line of weight `-c` is
isotropic exactly when the tail represents `c`. -/
theorem gramIsotropic_finSuccGramBlock_iff_exists_value_of_anisotropic
    {K : Type*} [Field K] (c : K)
    (A : Matrix (Fin n) (Fin n) K) (hA : ¬ GramIsotropic A) :
    GramIsotropic (finSuccGramBlock (-c) A) ↔
      ∃ v : Fin n → K, gramQuadraticValue A v = c := by
  constructor
  · intro hiso
    rcases gramIsotropic_or_exists_value_of_finSuccGramBlock c A hiso with
      htail | hrep
    · exact (hA htail).elim
    · exact hrep
  · exact gramIsotropic_finSuccGramBlock_of_exists_value c A

/-- A generic difference block is isotropic exactly when one side is
isotropic or the two sides represent a common nonzero value. -/
theorem gramIsotropic_differenceGramBlock_iff
    {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) K) (B : Matrix (Fin n) (Fin n) K) :
    GramIsotropic (differenceGramBlock A B) ↔
      GramIsotropic A ∨ GramIsotropic B ∨
        ∃ c : K, c ≠ 0 ∧
          (∃ u : Fin m → K, gramQuadraticValue A u = c) ∧
          ∃ v : Fin n → K, gramQuadraticValue B v = c := by
  constructor
  · rintro ⟨x, hx, hvalue⟩
    let u : Fin m → K := fun i ↦ x (Fin.castAdd n i)
    let v : Fin n → K := fun i ↦ x (Fin.natAdd m i)
    have huv : gramQuadraticValue A u = gramQuadraticValue B v := by
      rw [gramQuadraticValue_differenceGramBlock] at hvalue
      change gramQuadraticValue A u - gramQuadraticValue B v = 0 at hvalue
      linear_combination hvalue
    by_cases hu : u = 0
    · right
      left
      refine ⟨v, ?_, ?_⟩
      · intro hv
        apply hx
        rw [← differenceGramVector_split x]
        change differenceGramVector u v = 0
        rw [hu, hv]
        funext i
        simp [differenceGramVector]
      · rw [hu] at huv
        simpa [gramQuadraticValue] using huv.symm
    · by_cases hv : v = 0
      · left
        refine ⟨u, hu, ?_⟩
        rw [hv] at huv
        simpa [gramQuadraticValue] using huv
      · by_cases hc : gramQuadraticValue A u = 0
        · left
          exact ⟨u, hu, hc⟩
        · right
          right
          exact ⟨gramQuadraticValue A u, hc, ⟨u, rfl⟩, ⟨v, huv.symm⟩⟩
  · rintro (hA | hB | hcommon)
    · rcases hA with ⟨u, hu, hvalue⟩
      refine ⟨differenceGramVector u 0, ?_, ?_⟩
      · intro hx
        apply hu
        funext i
        have := congrFun hx (Fin.castAdd n i)
        simpa using this
      · rw [gramQuadraticValue_differenceGramBlock]
        simpa [gramQuadraticValue] using hvalue
    · rcases hB with ⟨v, hv, hvalue⟩
      refine ⟨differenceGramVector 0 v, ?_, ?_⟩
      · intro hx
        apply hv
        funext i
        have := congrFun hx (Fin.natAdd m i)
        simpa using this
      · rw [gramQuadraticValue_differenceGramBlock]
        simpa [gramQuadraticValue] using hvalue
    · rcases hcommon with ⟨c, hc, ⟨u, hu⟩, ⟨v, hv⟩⟩
      refine ⟨differenceGramVector u v, ?_, ?_⟩
      · intro hx
        apply hc
        rw [← hu]
        have hu0 : u = 0 := by
          funext i
          have := congrFun hx (Fin.castAdd n i)
          simpa using this
        simp [hu0, gramQuadraticValue]
      · rw [gramQuadraticValue_differenceGramBlock]
        simp [hu, hv]

/-- The difference of two binary forms is isotropic exactly when one binary
form is isotropic or the two forms represent a common nonzero value. -/
theorem gramIsotropic_binaryPairDifferenceGramBlock_iff
    {K : Type*} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) :
    GramIsotropic (binaryPairDifferenceGramBlock A B) ↔
      GramIsotropic A ∨ GramIsotropic B ∨
        ∃ c : K, c ≠ 0 ∧
          (∃ u : Fin 2 → K, gramQuadraticValue A u = c) ∧
          ∃ v : Fin 2 → K, gramQuadraticValue B v = c := by
  have finTwo_eta (w : Fin 2 → K) : ![w 0, w 1] = w := by
    funext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨x, hx, hvalue⟩
    let u : Fin 2 → K := ![x 0, x 1]
    let v : Fin 2 → K := ![x 2, x 3]
    have huv : gramQuadraticValue A u = gramQuadraticValue B v := by
      rw [gramQuadraticValue_binaryPairDifferenceGramBlock] at hvalue
      change gramQuadraticValue A u - gramQuadraticValue B v = 0 at hvalue
      linear_combination hvalue
    by_cases hu : u = 0
    · right
      left
      refine ⟨v, ?_, ?_⟩
      · intro hv
        apply hx
        funext i
        fin_cases i
        · exact congrFun hu 0
        · exact congrFun hu 1
        · exact congrFun hv 0
        · exact congrFun hv 1
      · rw [hu] at huv
        simpa [gramQuadraticValue] using huv.symm
    · by_cases hv : v = 0
      · left
        refine ⟨u, hu, ?_⟩
        rw [hv] at huv
        simpa [gramQuadraticValue] using huv
      · by_cases hc : gramQuadraticValue A u = 0
        · left
          exact ⟨u, hu, hc⟩
        · right
          right
          exact ⟨gramQuadraticValue A u, hc, ⟨u, rfl⟩, ⟨v, huv.symm⟩⟩
  · rintro (hA | hB | hcommon)
    · rcases hA with ⟨u, hu, hvalue⟩
      refine ⟨![u 0, u 1, 0, 0], ?_, ?_⟩
      · intro hx
        apply hu
        funext i
        fin_cases i
        · exact congrFun hx 0
        · exact congrFun hx 1
      · rw [gramQuadraticValue_binaryPairDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1] -
          gramQuadraticValue B ![0, 0] = 0
        rw [finTwo_eta]
        change gramQuadraticValue A u - gramQuadraticValue B 0 = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hB with ⟨v, hv, hvalue⟩
      refine ⟨![0, 0, v 0, v 1], ?_, ?_⟩
      · intro hx
        apply hv
        funext i
        fin_cases i
        · exact congrFun hx 2
        · exact congrFun hx 3
      · rw [gramQuadraticValue_binaryPairDifferenceGramBlock]
        change gramQuadraticValue A ![0, 0] -
          gramQuadraticValue B ![v 0, v 1] = 0
        rw [finTwo_eta]
        change gramQuadraticValue A 0 - gramQuadraticValue B v = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hcommon with ⟨c, hc, ⟨u, hu⟩, ⟨v, hv⟩⟩
      refine ⟨![u 0, u 1, v 0, v 1], ?_, ?_⟩
      · intro hx
        apply hc
        rw [← hu]
        have hu0 : u = 0 := by
          funext i
          fin_cases i
          · exact congrFun hx 0
          · exact congrFun hx 1
        simp [hu0, gramQuadraticValue]
      · rw [gramQuadraticValue_binaryPairDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1] -
          gramQuadraticValue B ![v 0, v 1] = 0
        rw [finTwo_eta, finTwo_eta, hu, hv]
        simp

/-- Matrix congruence transports represented values from the first form to
the second. -/
theorem exists_gramQuadraticValue_eq_of_isCongruent
    {K : Type*} [Field K] {A B : Matrix (Fin n) (Fin n) K}
    (hAB : A.IsCongruent B) (c : K)
    (hA : ∃ v : Fin n → K, gramQuadraticValue A v = c) :
    ∃ v : Fin n → K, gramQuadraticValue B v = c := by
  rcases hA with ⟨v, hv⟩
  rcases hAB.symm with ⟨T, hT⟩
  refine ⟨T.1 *ᵥ v, ?_⟩
  rw [gramQuadraticValue_mulVec_of_congr B A T hT v, hv]

/-- Congruent Gram matrices represent the same values. -/
theorem exists_gramQuadraticValue_eq_iff_of_isCongruent
    {K : Type*} [Field K] {A B : Matrix (Fin n) (Fin n) K}
    (hAB : A.IsCongruent B) (c : K) :
    (∃ v : Fin n → K, gramQuadraticValue A v = c) ↔
      ∃ v : Fin n → K, gramQuadraticValue B v = c :=
  ⟨exists_gramQuadraticValue_eq_of_isCongruent hAB c,
    exists_gramQuadraticValue_eq_of_isCongruent hAB.symm c⟩

private lemma mulVec_ne_zero_of_generalLinear
    {K : Type*} [Field K] (T : GL (Fin n) K) {v : Fin n → K}
    (hv : v ≠ 0) : T.1 *ᵥ v ≠ 0 := by
  intro hzero
  apply hv
  have hinv : (T⁻¹).1 * T.1 = 1 := by
    change (T⁻¹ * T).1 = 1
    simp
  calc
    v = ((T⁻¹).1 * T.1) *ᵥ v := by rw [hinv]; simp
    _ = (T⁻¹).1 *ᵥ (T.1 *ᵥ v) :=
      (Matrix.mulVec_mulVec v (T⁻¹).1 T.1).symm
    _ = 0 := by rw [hzero]; simp

private theorem gramIsotropic_of_isCongruent_right
    {K : Type*} [Field K]
    {A B : Matrix (Fin n) (Fin n) K}
    (hAB : A.IsCongruent B) (hB : GramIsotropic B) :
    GramIsotropic A := by
  rcases hAB with ⟨T, hT⟩
  rcases hB with ⟨v, hv, hvalue⟩
  refine ⟨T.1 *ᵥ v, mulVec_ne_zero_of_generalLinear T hv, ?_⟩
  rw [gramQuadraticValue_mulVec_of_congr A B T hT v, hvalue]

/-- Matrix congruence transports Gram isotropy from the first form to the
second. -/
theorem gramIsotropic_of_isCongruent
    {K : Type*} [Field K]
    {A B : Matrix (Fin n) (Fin n) K}
    (hAB : A.IsCongruent B) (hA : GramIsotropic A) :
    GramIsotropic B :=
  gramIsotropic_of_isCongruent_right hAB.symm hA

/-- Congruent Gram matrices are isotropic simultaneously. -/
theorem gramIsotropic_iff_of_isCongruent
    {K : Type*} [Field K]
    {A B : Matrix (Fin n) (Fin n) K}
    (hAB : A.IsCongruent B) :
    GramIsotropic A ↔ GramIsotropic B :=
  ⟨gramIsotropic_of_isCongruent hAB,
    gramIsotropic_of_isCongruent hAB.symm⟩

/-- A nonsingular symmetric Gram matrix diagonalizes with nonzero entries,
and the resulting diagonal form is isotropic exactly when the original form
is isotropic. -/
theorem exists_gramMatrix_congr_diagonal_gramIsotropic_iff
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ (d : Fin n → K) (P : GL (Fin n) K),
      (∀ i, d i ≠ 0) ∧
        P.1ᵀ * A * P.1 = Matrix.diagonal d ∧
        (GramIsotropic A ↔ GramIsotropic (Matrix.diagonal d)) := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det hchar
  exact ⟨d, P, hd, hP,
    gramIsotropic_iff_of_isCongruent ⟨P, hP⟩⟩

/-- A nonsingular isotropic binary diagonal form over a field of
characteristic not two represents every scalar. -/
theorem exists_binaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hiso : GramIsotropic (Matrix.diagonal ![a, b])) (c : K) :
    ∃ v : Fin 2 → K, gramQuadraticValue (Matrix.diagonal ![a, b]) v = c := by
  obtain ⟨s, hs⟩ :=
    (binaryDiagonal_gramIsotropic_iff_isSquare_neg_div a b ha hb).mp hiso
  have hbrel : b = -a * s ^ 2 := by
    field_simp [ha] at hs
    linear_combination -hs
  have hs0 : s ≠ 0 := by
    intro hs0
    subst s
    apply hb
    simpa using hbrel
  let u : K := c / a
  let x : K := (u + 1) / 2
  let y : K := (1 - u) / (2 * s)
  refine ⟨![x, y], ?_⟩
  simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    x, y, u]
  rw [hbrel]
  field_simp [ha, hs0, Ring.two_ne_zero hchar]
  ring

/-- Every nonsingular symmetric isotropic binary Gram matrix over a field of
characteristic not two represents every scalar. -/
theorem exists_binary_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (hiso : GramIsotropic A) (c : K) :
    ∃ v : Fin 2 → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP, hiso_iff⟩ :=
    exists_gramMatrix_congr_diagonal_gramIsotropic_iff
      A hA_symm hA_det hchar
  have hd_eq : d = ![d 0, d 1] := by
    funext i
    fin_cases i <;> rfl
  have hdiagonal : GramIsotropic (Matrix.diagonal ![d 0, d 1]) := by
    rw [← hd_eq]
    exact hiso_iff.mp hiso
  have hrep : ∃ v : Fin 2 → K,
      gramQuadraticValue (Matrix.diagonal d) v = c := by
    rw [hd_eq]
    exact exists_binaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
      hchar (d 0) (d 1) (hd 0) (hd 1) hdiagonal c
  exact (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) c).mpr hrep

/-- A nonsingular isotropic ternary diagonal form over a field of
characteristic not two represents every scalar. -/
theorem exists_ternaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (hiso : GramIsotropic (Matrix.diagonal ![a, b, d])) (c : K) :
    ∃ v : Fin 3 → K,
      gramQuadraticValue (Matrix.diagonal ![a, b, d]) v = c := by
  obtain ⟨x, hx, hvalue⟩ := hiso
  have hcoords : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    funext i
    fin_cases i <;> simp_all
  have hvalue' : x 0 * (a * x 0) + x 1 * (b * x 1) +
      x 2 * (d * x 2) = 0 := by
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      using hvalue
  rcases hcoords with hx0 | hx1 | hx2
  · let r : K := (c - a) / (2 * a * x 0)
    refine ⟨![r * x 0 + 1, r * x 1, r * x 2], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    calc
      _ = r ^ 2 * (x 0 * (a * x 0) + x 1 * (b * x 1) +
          x 2 * (d * x 2)) + 2 * a * x 0 * r + a := by ring
      _ = 2 * a * x 0 * r + a := by rw [hvalue']; ring
      _ = c := by
        have hden : 2 * a * x 0 ≠ 0 :=
          mul_ne_zero (mul_ne_zero (Ring.two_ne_zero hchar) ha) hx0
        dsimp [r]
        field_simp [hden]
        field_simp [Ring.two_ne_zero hchar]
        ring
  · let r : K := (c - b) / (2 * b * x 1)
    refine ⟨![r * x 0, r * x 1 + 1, r * x 2], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    calc
      _ = r ^ 2 * (x 0 * (a * x 0) + x 1 * (b * x 1) +
          x 2 * (d * x 2)) + 2 * b * x 1 * r + b := by ring
      _ = 2 * b * x 1 * r + b := by rw [hvalue']; ring
      _ = c := by
        have hden : 2 * b * x 1 ≠ 0 :=
          mul_ne_zero (mul_ne_zero (Ring.two_ne_zero hchar) hb) hx1
        dsimp [r]
        field_simp [hden]
        field_simp [Ring.two_ne_zero hchar]
        ring
  · let r : K := (c - d) / (2 * d * x 2)
    refine ⟨![r * x 0, r * x 1, r * x 2 + 1], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    calc
      _ = r ^ 2 * (x 0 * (a * x 0) + x 1 * (b * x 1) +
          x 2 * (d * x 2)) + 2 * d * x 2 * r + d := by ring
      _ = 2 * d * x 2 * r + d := by rw [hvalue']; ring
      _ = c := by
        have hden : 2 * d * x 2 ≠ 0 :=
          mul_ne_zero (mul_ne_zero (Ring.two_ne_zero hchar) hd) hx2
        dsimp [r]
        field_simp [hden]
        field_simp [Ring.two_ne_zero hchar]
        ring

/-- Every nonsingular symmetric isotropic ternary Gram matrix over a field of
characteristic not two represents every scalar. -/
theorem exists_ternary_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (A : Matrix (Fin 3) (Fin 3) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (hiso : GramIsotropic A) (c : K) :
    ∃ v : Fin 3 → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP, hiso_iff⟩ :=
    exists_gramMatrix_congr_diagonal_gramIsotropic_iff
      A hA_symm hA_det hchar
  have hd_eq : d = ![d 0, d 1, d 2] := by
    funext i
    fin_cases i <;> rfl
  have hdiagonal : GramIsotropic
      (Matrix.diagonal ![d 0, d 1, d 2]) := by
    rw [← hd_eq]
    exact hiso_iff.mp hiso
  have hrep : ∃ v : Fin 3 → K,
      gramQuadraticValue (Matrix.diagonal d) v = c := by
    rw [hd_eq]
    exact exists_ternaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
      hchar (d 0) (d 1) (d 2) (hd 0) (hd 1) (hd 2) hdiagonal c
  exact (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) c).mpr hrep

/-- A nonsingular isotropic quaternary diagonal form over a field of
characteristic not two represents every scalar. -/
theorem exists_quaternaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (a b d e : K) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hiso : GramIsotropic (Matrix.diagonal ![a, b, d, e])) (c : K) :
    ∃ v : Fin 4 → K,
      gramQuadraticValue (Matrix.diagonal ![a, b, d, e]) v = c := by
  obtain ⟨x, hx, hvalue⟩ := hiso
  have hvalue' : x 0 * (a * x 0) + x 1 * (b * x 1) +
      x 2 * (d * x 2) + x 3 * (e * x 3) = 0 := by
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      using hvalue
  by_cases hx0 : x 0 ≠ 0
  · let r : K := (c - a) / (2 * a * x 0)
    refine ⟨![r * x 0 + 1, r * x 1, r * x 2, r * x 3], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    calc
      _ = r ^ 2 * (x 0 * (a * x 0) + x 1 * (b * x 1) +
          x 2 * (d * x 2) + x 3 * (e * x 3)) +
          2 * a * x 0 * r + a := by ring
      _ = 2 * a * x 0 * r + a := by rw [hvalue']; ring
      _ = c := by
        have hden : 2 * a * x 0 ≠ 0 :=
          mul_ne_zero (mul_ne_zero (Ring.two_ne_zero hchar) ha) hx0
        dsimp [r]
        field_simp [hden]
        field_simp [Ring.two_ne_zero hchar]
        ring
  · have htail_ne : ![x 1, x 2, x 3] ≠ (0 : Fin 3 → K) := by
      intro htail
      apply hx
      funext i
      fin_cases i
      · exact not_ne_iff.mp hx0
      · exact congrFun htail 0
      · exact congrFun htail 1
      · exact congrFun htail 2
    have htail_value : gramQuadraticValue
        (Matrix.diagonal ![b, d, e]) ![x 1, x 2, x 3] = 0 := by
      simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three]
      rw [not_ne_iff.mp hx0] at hvalue'
      simpa using hvalue'
    obtain ⟨v, hv⟩ :=
      exists_ternaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
        hchar b d e hb hd he ⟨![x 1, x 2, x 3], htail_ne, htail_value⟩ c
    refine ⟨![0, v 0, v 1, v 2], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] using hv

/-- Every nonsingular symmetric isotropic quaternary Gram matrix over a field
of characteristic not two represents every scalar. -/
theorem exists_quaternary_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (hiso : GramIsotropic A) (c : K) :
    ∃ v : Fin 4 → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP, hiso_iff⟩ :=
    exists_gramMatrix_congr_diagonal_gramIsotropic_iff
      A hA_symm hA_det hchar
  have hd_eq : d = ![d 0, d 1, d 2, d 3] := by
    funext i
    fin_cases i <;> rfl
  have hdiagonal : GramIsotropic
      (Matrix.diagonal ![d 0, d 1, d 2, d 3]) := by
    rw [← hd_eq]
    exact hiso_iff.mp hiso
  have hrep : ∃ v : Fin 4 → K,
      gramQuadraticValue (Matrix.diagonal d) v = c := by
    rw [hd_eq]
    exact exists_quaternaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
      hchar (d 0) (d 1) (d 2) (d 3)
        (hd 0) (hd 1) (hd 2) (hd 3) hdiagonal c
  exact (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) c).mpr hrep

/-- A nonsingular isotropic quinary diagonal form over a field of
characteristic not two represents every scalar. -/
theorem exists_quinaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (a b d e f : K) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (he : e ≠ 0) (hf : f ≠ 0)
    (hiso : GramIsotropic (Matrix.diagonal ![a, b, d, e, f])) (c : K) :
    ∃ v : Fin 5 → K,
      gramQuadraticValue (Matrix.diagonal ![a, b, d, e, f]) v = c := by
  obtain ⟨x, hx, hvalue⟩ := hiso
  have hvalue' : x 0 * (a * x 0) + x 1 * (b * x 1) +
      x 2 * (d * x 2) + x 3 * (e * x 3) + x 4 * (f * x 4) = 0 := by
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
      using hvalue
  by_cases hx0 : x 0 ≠ 0
  · let r : K := (c - a) / (2 * a * x 0)
    refine ⟨![r * x 0 + 1, r * x 1, r * x 2, r * x 3, r * x 4], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    calc
      _ = r ^ 2 * (x 0 * (a * x 0) + x 1 * (b * x 1) +
          x 2 * (d * x 2) + x 3 * (e * x 3) + x 4 * (f * x 4)) +
          2 * a * x 0 * r + a := by ring
      _ = 2 * a * x 0 * r + a := by rw [hvalue']; ring
      _ = c := by
        have hden : 2 * a * x 0 ≠ 0 :=
          mul_ne_zero (mul_ne_zero (Ring.two_ne_zero hchar) ha) hx0
        dsimp [r]
        field_simp [hden]
        field_simp [Ring.two_ne_zero hchar]
        ring
  · have htail_ne : ![x 1, x 2, x 3, x 4] ≠ (0 : Fin 4 → K) := by
      intro htail
      apply hx
      funext i
      fin_cases i
      · exact not_ne_iff.mp hx0
      · exact congrFun htail 0
      · exact congrFun htail 1
      · exact congrFun htail 2
      · exact congrFun htail 3
    have htail_value : gramQuadraticValue
        (Matrix.diagonal ![b, d, e, f]) ![x 1, x 2, x 3, x 4] = 0 := by
      simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four]
      rw [not_ne_iff.mp hx0] at hvalue'
      simpa using hvalue'
    obtain ⟨v, hv⟩ :=
      exists_quaternaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
        hchar b d e f hb hd he hf
          ⟨![x 1, x 2, x 3, x 4], htail_ne, htail_value⟩ c
    refine ⟨![0, v 0, v 1, v 2, v 3], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] using hv

/-- Every nonsingular symmetric isotropic quinary Gram matrix over a field
of characteristic not two represents every scalar. -/
theorem exists_quinary_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (A : Matrix (Fin 5) (Fin 5) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (hiso : GramIsotropic A) (c : K) :
    ∃ v : Fin 5 → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP, hiso_iff⟩ :=
    exists_gramMatrix_congr_diagonal_gramIsotropic_iff
      A hA_symm hA_det hchar
  have hd_eq : d = ![d 0, d 1, d 2, d 3, d 4] := by
    funext i
    fin_cases i <;> rfl
  have hdiagonal : GramIsotropic
      (Matrix.diagonal ![d 0, d 1, d 2, d 3, d 4]) := by
    rw [← hd_eq]
    exact hiso_iff.mp hiso
  have hrep : ∃ v : Fin 5 → K,
      gramQuadraticValue (Matrix.diagonal d) v = c := by
    rw [hd_eq]
    exact exists_quinaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
      hchar (d 0) (d 1) (d 2) (d 3) (d 4)
        (hd 0) (hd 1) (hd 2) (hd 3) (hd 4) hdiagonal c
  exact (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) c).mpr hrep

/-- A nonsingular isotropic sextenary diagonal form over a field of
characteristic not two represents every scalar. -/
theorem exists_sextenaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (a b d e f g : K) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (he : e ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0)
    (hiso : GramIsotropic (Matrix.diagonal ![a, b, d, e, f, g])) (c : K) :
    ∃ v : Fin 6 → K,
      gramQuadraticValue (Matrix.diagonal ![a, b, d, e, f, g]) v = c := by
  obtain ⟨x, hx, hvalue⟩ := hiso
  have hvalue' : x 0 * (a * x 0) + x 1 * (b * x 1) +
      x 2 * (d * x 2) + x 3 * (e * x 3) + x 4 * (f * x 4) +
      x 5 * (g * x 5) = 0 := by
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
      using hvalue
  by_cases hx0 : x 0 ≠ 0
  · let r : K := (c - a) / (2 * a * x 0)
    refine ⟨![r * x 0 + 1, r * x 1, r * x 2, r * x 3, r * x 4,
      r * x 5], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
    calc
      _ = r ^ 2 * (x 0 * (a * x 0) + x 1 * (b * x 1) +
          x 2 * (d * x 2) + x 3 * (e * x 3) + x 4 * (f * x 4) +
          x 5 * (g * x 5)) + 2 * a * x 0 * r + a := by ring
      _ = 2 * a * x 0 * r + a := by rw [hvalue']; ring
      _ = c := by
        have hden : 2 * a * x 0 ≠ 0 :=
          mul_ne_zero (mul_ne_zero (Ring.two_ne_zero hchar) ha) hx0
        dsimp [r]
        field_simp [hden]
        field_simp [Ring.two_ne_zero hchar]
        ring
  · have htail_ne : ![x 1, x 2, x 3, x 4, x 5] ≠
        (0 : Fin 5 → K) := by
      intro htail
      apply hx
      funext i
      fin_cases i
      · exact not_ne_iff.mp hx0
      · exact congrFun htail 0
      · exact congrFun htail 1
      · exact congrFun htail 2
      · exact congrFun htail 3
      · exact congrFun htail 4
    have htail_value : gramQuadraticValue
        (Matrix.diagonal ![b, d, e, f, g]) ![x 1, x 2, x 3, x 4, x 5] = 0 := by
      simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
        Fin.sum_univ_five]
      rw [not_ne_iff.mp hx0] at hvalue'
      simpa using hvalue'
    obtain ⟨v, hv⟩ :=
      exists_quinaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
        hchar b d e f g hb hd he hf hg
          ⟨![x 1, x 2, x 3, x 4, x 5], htail_ne, htail_value⟩ c
    refine ⟨![0, v 0, v 1, v 2, v 3, v 4], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_five] using hv

/-- Every nonsingular symmetric isotropic sextenary Gram matrix over a field
of characteristic not two represents every scalar. -/
theorem exists_sextenary_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (A : Matrix (Fin 6) (Fin 6) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (hiso : GramIsotropic A) (c : K) :
    ∃ v : Fin 6 → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP, hiso_iff⟩ :=
    exists_gramMatrix_congr_diagonal_gramIsotropic_iff
      A hA_symm hA_det hchar
  have hd_eq : d = ![d 0, d 1, d 2, d 3, d 4, d 5] := by
    funext i
    fin_cases i <;> rfl
  have hdiagonal : GramIsotropic
      (Matrix.diagonal ![d 0, d 1, d 2, d 3, d 4, d 5]) := by
    rw [← hd_eq]
    exact hiso_iff.mp hiso
  have hrep : ∃ v : Fin 6 → K,
      gramQuadraticValue (Matrix.diagonal d) v = c := by
    rw [hd_eq]
    exact exists_sextenaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
      hchar (d 0) (d 1) (d 2) (d 3) (d 4) (d 5)
        (hd 0) (hd 1) (hd 2) (hd 3) (hd 4) (hd 5) hdiagonal c
  exact (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) c).mpr hrep

/-- A nonsingular isotropic septenary diagonal form over a field of
characteristic not two represents every scalar. -/
theorem exists_septenaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (a b d e f g k : K) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (he : e ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0) (hk : k ≠ 0)
    (hiso : GramIsotropic (Matrix.diagonal ![a, b, d, e, f, g, k])) (c : K) :
    ∃ v : Fin 7 → K,
      gramQuadraticValue (Matrix.diagonal ![a, b, d, e, f, g, k]) v = c := by
  obtain ⟨x, hx, hvalue⟩ := hiso
  have hvalue' : x 0 * (a * x 0) + x 1 * (b * x 1) +
      x 2 * (d * x 2) + x 3 * (e * x 3) + x 4 * (f * x 4) +
      x 5 * (g * x 5) + x 6 * (k * x 6) = 0 := by
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_seven]
      using hvalue
  by_cases hx0 : x 0 ≠ 0
  · let r : K := (c - a) / (2 * a * x 0)
    refine ⟨![r * x 0 + 1, r * x 1, r * x 2, r * x 3, r * x 4,
      r * x 5, r * x 6], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_seven]
    calc
      _ = r ^ 2 * (x 0 * (a * x 0) + x 1 * (b * x 1) +
          x 2 * (d * x 2) + x 3 * (e * x 3) + x 4 * (f * x 4) +
          x 5 * (g * x 5) + x 6 * (k * x 6)) +
          2 * a * x 0 * r + a := by ring
      _ = 2 * a * x 0 * r + a := by rw [hvalue']; ring
      _ = c := by
        have hden : 2 * a * x 0 ≠ 0 :=
          mul_ne_zero (mul_ne_zero (Ring.two_ne_zero hchar) ha) hx0
        dsimp [r]
        field_simp [hden]
        field_simp [Ring.two_ne_zero hchar]
        ring
  · have htail_ne : ![x 1, x 2, x 3, x 4, x 5, x 6] ≠
        (0 : Fin 6 → K) := by
      intro htail
      apply hx
      funext i
      fin_cases i
      · exact not_ne_iff.mp hx0
      · exact congrFun htail 0
      · exact congrFun htail 1
      · exact congrFun htail 2
      · exact congrFun htail 3
      · exact congrFun htail 4
      · exact congrFun htail 5
    have htail_value : gramQuadraticValue
        (Matrix.diagonal ![b, d, e, f, g, k])
          ![x 1, x 2, x 3, x 4, x 5, x 6] = 0 := by
      simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
        Fin.sum_univ_six]
      rw [not_ne_iff.mp hx0] at hvalue'
      simpa using hvalue'
    obtain ⟨v, hv⟩ :=
      exists_sextenaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
        hchar b d e f g k hb hd he hf hg hk
          ⟨![x 1, x 2, x 3, x 4, x 5, x 6], htail_ne, htail_value⟩ c
    refine ⟨![0, v 0, v 1, v 2, v 3, v 4, v 5], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_seven]
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_six] using hv

/-- Every nonsingular symmetric isotropic septenary Gram matrix over a field
of characteristic not two represents every scalar. -/
theorem exists_septenary_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (A : Matrix (Fin 7) (Fin 7) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (hiso : GramIsotropic A) (c : K) :
    ∃ v : Fin 7 → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP, hiso_iff⟩ :=
    exists_gramMatrix_congr_diagonal_gramIsotropic_iff
      A hA_symm hA_det hchar
  have hd_eq : d = ![d 0, d 1, d 2, d 3, d 4, d 5, d 6] := by
    funext i
    fin_cases i <;> rfl
  have hdiagonal : GramIsotropic
      (Matrix.diagonal ![d 0, d 1, d 2, d 3, d 4, d 5, d 6]) := by
    rw [← hd_eq]
    exact hiso_iff.mp hiso
  have hrep : ∃ v : Fin 7 → K,
      gramQuadraticValue (Matrix.diagonal d) v = c := by
    rw [hd_eq]
    exact exists_septenaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
      hchar (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6)
        (hd 0) (hd 1) (hd 2) (hd 3) (hd 4) (hd 5) (hd 6) hdiagonal c
  exact (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) c).mpr hrep

/-- A nonsingular isotropic octonary diagonal form over a field of
characteristic not two represents every scalar. -/
theorem exists_octonaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (a b d e f g k l : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hf : f ≠ 0) (hg : g ≠ 0) (hk : k ≠ 0) (hl : l ≠ 0)
    (hiso : GramIsotropic (Matrix.diagonal ![a, b, d, e, f, g, k, l]))
    (c : K) :
    ∃ v : Fin 8 → K,
      gramQuadraticValue
        (Matrix.diagonal ![a, b, d, e, f, g, k, l]) v = c := by
  obtain ⟨x, hx, hvalue⟩ := hiso
  have hvalue' : x 0 * (a * x 0) + x 1 * (b * x 1) +
      x 2 * (d * x 2) + x 3 * (e * x 3) + x 4 * (f * x 4) +
      x 5 * (g * x 5) + x 6 * (k * x 6) + x 7 * (l * x 7) = 0 := by
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
      using hvalue
  by_cases hx0 : x 0 ≠ 0
  · let r : K := (c - a) / (2 * a * x 0)
    refine ⟨![r * x 0 + 1, r * x 1, r * x 2, r * x 3, r * x 4,
      r * x 5, r * x 6, r * x 7], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
    calc
      _ = r ^ 2 * (x 0 * (a * x 0) + x 1 * (b * x 1) +
          x 2 * (d * x 2) + x 3 * (e * x 3) + x 4 * (f * x 4) +
          x 5 * (g * x 5) + x 6 * (k * x 6) + x 7 * (l * x 7)) +
          2 * a * x 0 * r + a := by ring
      _ = 2 * a * x 0 * r + a := by rw [hvalue']; ring
      _ = c := by
        have hden : 2 * a * x 0 ≠ 0 :=
          mul_ne_zero (mul_ne_zero (Ring.two_ne_zero hchar) ha) hx0
        dsimp [r]
        field_simp [hden]
        field_simp [Ring.two_ne_zero hchar]
        ring
  · have htail_ne : ![x 1, x 2, x 3, x 4, x 5, x 6, x 7] ≠
        (0 : Fin 7 → K) := by
      intro htail
      apply hx
      funext i
      fin_cases i
      · exact not_ne_iff.mp hx0
      · exact congrFun htail 0
      · exact congrFun htail 1
      · exact congrFun htail 2
      · exact congrFun htail 3
      · exact congrFun htail 4
      · exact congrFun htail 5
      · exact congrFun htail 6
    have htail_value : gramQuadraticValue
        (Matrix.diagonal ![b, d, e, f, g, k, l])
          ![x 1, x 2, x 3, x 4, x 5, x 6, x 7] = 0 := by
      simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
        Fin.sum_univ_seven]
      rw [not_ne_iff.mp hx0] at hvalue'
      simpa using hvalue'
    obtain ⟨v, hv⟩ :=
      exists_septenaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
        hchar b d e f g k l hb hd he hf hg hk hl
          ⟨![x 1, x 2, x 3, x 4, x 5, x 6, x 7], htail_ne, htail_value⟩ c
    refine ⟨![0, v 0, v 1, v 2, v 3, v 4, v 5, v 6], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_eight]
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_seven] using hv

/-- Every nonsingular symmetric isotropic octonary Gram matrix over a field
of characteristic not two represents every scalar. -/
theorem exists_octonary_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (A : Matrix (Fin 8) (Fin 8) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (hiso : GramIsotropic A) (c : K) :
    ∃ v : Fin 8 → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP, hiso_iff⟩ :=
    exists_gramMatrix_congr_diagonal_gramIsotropic_iff
      A hA_symm hA_det hchar
  have hd_eq : d = ![d 0, d 1, d 2, d 3, d 4, d 5, d 6, d 7] := by
    funext i
    fin_cases i <;> rfl
  have hdiagonal : GramIsotropic
      (Matrix.diagonal ![d 0, d 1, d 2, d 3, d 4, d 5, d 6, d 7]) := by
    rw [← hd_eq]
    exact hiso_iff.mp hiso
  have hrep : ∃ v : Fin 8 → K,
      gramQuadraticValue (Matrix.diagonal d) v = c := by
    rw [hd_eq]
    exact exists_octonaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
      hchar (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6) (d 7)
        (hd 0) (hd 1) (hd 2) (hd 3) (hd 4) (hd 5) (hd 6) (hd 7)
        hdiagonal c
  exact (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) c).mpr hrep

/-- A nonsingular isotropic nonary diagonal form over a field of
characteristic not two represents every scalar. -/
theorem exists_nonaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (a b d e f g k l m : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hf : f ≠ 0) (hg : g ≠ 0) (hk : k ≠ 0) (hl : l ≠ 0) (hm : m ≠ 0)
    (hiso : GramIsotropic (Matrix.diagonal ![a, b, d, e, f, g, k, l, m]))
    (c : K) :
    ∃ v : Fin 9 → K,
      gramQuadraticValue
        (Matrix.diagonal ![a, b, d, e, f, g, k, l, m]) v = c := by
  have sum_univ_nine (z : Fin 9 → K) :
      ∑ i, z i = z 0 + z 1 + z 2 + z 3 + z 4 + z 5 + z 6 + z 7 + z 8 := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_eight]
    rfl
  obtain ⟨x, hx, hvalue⟩ := hiso
  have hvalue' : x 0 * (a * x 0) + x 1 * (b * x 1) +
      x 2 * (d * x 2) + x 3 * (e * x 3) + x 4 * (f * x 4) +
      x 5 * (g * x 5) + x 6 * (k * x 6) + x 7 * (l * x 7) +
      x 8 * (m * x 8) = 0 := by
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct, sum_univ_nine]
      using hvalue
  by_cases hx0 : x 0 ≠ 0
  · let r : K := (c - a) / (2 * a * x 0)
    refine ⟨![r * x 0 + 1, r * x 1, r * x 2, r * x 3, r * x 4,
      r * x 5, r * x 6, r * x 7, r * x 8], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, sum_univ_nine]
    calc
      _ = r ^ 2 * (x 0 * (a * x 0) + x 1 * (b * x 1) +
          x 2 * (d * x 2) + x 3 * (e * x 3) + x 4 * (f * x 4) +
          x 5 * (g * x 5) + x 6 * (k * x 6) + x 7 * (l * x 7) +
          x 8 * (m * x 8)) + 2 * a * x 0 * r + a := by ring
      _ = 2 * a * x 0 * r + a := by rw [hvalue']; ring
      _ = c := by
        have hden : 2 * a * x 0 ≠ 0 :=
          mul_ne_zero (mul_ne_zero (Ring.two_ne_zero hchar) ha) hx0
        dsimp [r]
        field_simp [hden]
        field_simp [Ring.two_ne_zero hchar]
        ring
  · have htail_ne : ![x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] ≠
        (0 : Fin 8 → K) := by
      intro htail
      apply hx
      funext i
      fin_cases i
      · exact not_ne_iff.mp hx0
      · exact congrFun htail 0
      · exact congrFun htail 1
      · exact congrFun htail 2
      · exact congrFun htail 3
      · exact congrFun htail 4
      · exact congrFun htail 5
      · exact congrFun htail 6
      · exact congrFun htail 7
    have htail_value : gramQuadraticValue
        (Matrix.diagonal ![b, d, e, f, g, k, l, m])
          ![x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] = 0 := by
      simp [gramQuadraticValue, Matrix.mulVec, dotProduct,
        Fin.sum_univ_eight]
      rw [not_ne_iff.mp hx0] at hvalue'
      simpa using hvalue'
    obtain ⟨v, hv⟩ :=
      exists_octonaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
        hchar b d e f g k l m hb hd he hf hg hk hl hm
          ⟨![x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8],
            htail_ne, htail_value⟩ c
    refine ⟨![0, v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7], ?_⟩
    simp [gramQuadraticValue, Matrix.mulVec, dotProduct, sum_univ_nine]
    simpa [gramQuadraticValue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_eight] using hv

/-- Every nonsingular symmetric isotropic nonary Gram matrix over a field
of characteristic not two represents every scalar. -/
theorem exists_nonary_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] (A : Matrix (Fin 9) (Fin 9) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (hiso : GramIsotropic A) (c : K) :
    ∃ v : Fin 9 → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP, hiso_iff⟩ :=
    exists_gramMatrix_congr_diagonal_gramIsotropic_iff
      A hA_symm hA_det hchar
  have hd_eq : d = ![d 0, d 1, d 2, d 3, d 4, d 5, d 6, d 7, d 8] := by
    funext i
    fin_cases i <;> rfl
  have hdiagonal : GramIsotropic
      (Matrix.diagonal ![d 0, d 1, d 2, d 3, d 4, d 5, d 6, d 7, d 8]) := by
    rw [← hd_eq]
    exact hiso_iff.mp hiso
  have hrep : ∃ v : Fin 9 → K,
      gramQuadraticValue (Matrix.diagonal d) v = c := by
    rw [hd_eq]
    exact exists_nonaryDiagonal_gramQuadraticValue_eq_of_gramIsotropic
      hchar (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) (d 6) (d 7) (d 8)
        (hd 0) (hd 1) (hd 2) (hd 3) (hd 4) (hd 5) (hd 6) (hd 7) (hd 8)
        hdiagonal c
  exact (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) c).mpr hrep

private lemma dotProduct_mulVec_comm_of_isSymm
    {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA_symm : A.IsSymm)
    (x y : Fin n → K) :
    x ⬝ᵥ A *ᵥ y = y ⬝ᵥ A *ᵥ x := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  calc
    (∑ i, ∑ j, x i * (A i j * y j)) =
        ∑ j, ∑ i, x i * (A i j * y j) := Finset.sum_comm
    _ = ∑ i, ∑ j, y i * (A i j * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hA_symm.apply j i]
      ring

private lemma gramQuadraticValue_add_smul
    {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA_symm : A.IsSymm)
    (x y : Fin n → K) (r : K) :
    gramQuadraticValue A (y + r • x) =
      gramQuadraticValue A y + 2 * r * (y ⬝ᵥ A *ᵥ x) +
        r ^ 2 * gramQuadraticValue A x := by
  simp only [gramQuadraticValue, Matrix.mulVec_add, Matrix.mulVec_smul,
    add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  rw [dotProduct_mulVec_comm_of_isSymm A hA_symm x y]
  ring

/-- Every nonsingular symmetric isotropic Gram matrix over a field of
characteristic not two represents every scalar, in arbitrary dimension. -/
theorem exists_gramQuadraticValue_eq_of_gramIsotropic
    {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) (hiso : GramIsotropic A) (c : K) :
    ∃ v : Fin n → K, gramQuadraticValue A v = c := by
  rcases hiso with ⟨x, hx, hvalue⟩
  have hAx : A *ᵥ x ≠ 0 := by
    intro hzero
    exact hx (Matrix.eq_zero_of_mulVec_eq_zero hA_det hzero)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hAx
  have hi' : (A *ᵥ x) i ≠ 0 := by simpa using hi
  let y : Fin n → K := Pi.single i 1
  let r : K := (c - gramQuadraticValue A y) / (2 * (A *ᵥ x) i)
  refine ⟨y + r • x, ?_⟩
  rw [gramQuadraticValue_add_smul A hA_symm, hvalue]
  have hpair : y ⬝ᵥ A *ᵥ x = (A *ᵥ x) i := by simp [y]
  rw [hpair]
  dsimp only [r]
  field_simp [Ring.two_ne_zero hchar, hi']
  ring

/-- Every positive-dimensional nonsingular symmetric Gram matrix over a field
of characteristic not two represents some nonzero scalar. -/
theorem exists_gramQuadraticValue_eq_ne_zero
    {K : Type*} [Field K] {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ c : K, c ≠ 0 ∧ ∃ v : Fin n → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det hchar
  let i : Fin n := ⟨0, Nat.pos_of_neZero n⟩
  refine ⟨d i, hd i, ?_⟩
  apply (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) (d i)).mpr
  refine ⟨Pi.single i 1, ?_⟩
  classical
  simp only [gramQuadraticValue, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  · intro j _ hji
    simp [Pi.single_apply, hji]
  · simp

/-- For positive-dimensional nonsingular symmetric forms, isotropy of the
generic difference block is equivalent to representing one common nonzero
scalar. -/
theorem gramIsotropic_differenceGramBlock_iff_exists_common_value
    {K : Type*} [Field K] {m n : ℕ} [NeZero m] [NeZero n]
    (A : Matrix (Fin m) (Fin m) K) (B : Matrix (Fin n) (Fin n) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    GramIsotropic (differenceGramBlock A B) ↔
      ∃ c : K, c ≠ 0 ∧
        (∃ u : Fin m → K, gramQuadraticValue A u = c) ∧
        ∃ v : Fin n → K, gramQuadraticValue B v = c := by
  constructor
  · intro hiso
    rcases (gramIsotropic_differenceGramBlock_iff A B).mp hiso with
      hA | hB | hcommon
    · obtain ⟨c, hc, hBrep⟩ :=
        exists_gramQuadraticValue_eq_ne_zero B hB_symm hB_det hchar
      exact ⟨c, hc,
        exists_gramQuadraticValue_eq_of_gramIsotropic
          A hA_symm hA_det hchar hA c,
        hBrep⟩
    · obtain ⟨c, hc, hArep⟩ :=
        exists_gramQuadraticValue_eq_ne_zero A hA_symm hA_det hchar
      exact ⟨c, hc, hArep,
        exists_gramQuadraticValue_eq_of_gramIsotropic
          B hB_symm hB_det hchar hB c⟩
    · exact hcommon
  · intro hcommon
    exact (gramIsotropic_differenceGramBlock_iff A B).mpr
      (Or.inr (Or.inr hcommon))

/-- Every nonsingular symmetric Gram matrix in characteristic not two is
congruent to a generic difference block obtained by splitting one
diagonalization at `m`; the congruence preserves Gram isotropy. -/
theorem exists_gramMatrix_congr_differenceGramBlock_gramIsotropic_iff
    {K : Type*} [Field K] {m n : ℕ}
    (M : Matrix (Fin (m + n)) (Fin (m + n)) K)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ (A : Matrix (Fin m) (Fin m) K)
      (B : Matrix (Fin n) (Fin n) K) (P : GL (Fin (m + n)) K),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
        P.1ᵀ * M * P.1 = differenceGramBlock A B ∧
        (GramIsotropic M ↔ GramIsotropic (differenceGramBlock A B)) := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal M hM_symm hM_det hchar
  let A : Matrix (Fin m) (Fin m) K :=
    Matrix.diagonal (fun i ↦ d (Fin.castAdd n i))
  let B : Matrix (Fin n) (Fin n) K :=
    Matrix.diagonal (fun i ↦ -d (Fin.natAdd m i))
  have hblock : Matrix.diagonal d = differenceGramBlock A B := by
    exact (differenceGramBlock_diagonal_split d).symm
  have hcongr : P.1ᵀ * M * P.1 = differenceGramBlock A B := hP.trans hblock
  refine ⟨A, B, P, ?_, ?_, ?_, ?_, hcongr, ?_⟩
  · simp [A]
  · simp only [A, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hd _
  · simp [B]
  · simp only [B, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ neg_ne_zero.mpr (hd _)
  · exact gramIsotropic_iff_of_isCongruent ⟨P, hcongr⟩

/-- Every nonsingular symmetric binary Gram matrix in characteristic not two
represents some nonzero scalar. -/
theorem exists_binary_gramQuadraticValue_eq_ne_zero
    {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 2) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ c : K, c ≠ 0 ∧
      ∃ v : Fin 2 → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det hchar
  refine ⟨d 0, hd 0, ?_⟩
  apply (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) (d 0)).mpr
  refine ⟨![1, 0], ?_⟩
  simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- For nonsingular symmetric binary forms, isotropy of their difference
block is equivalent to representing one common nonzero scalar. -/
theorem gramIsotropic_binaryPairDifferenceGramBlock_iff_exists_common_value
    {K : Type*} [Field K] (A B : Matrix (Fin 2) (Fin 2) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    GramIsotropic (binaryPairDifferenceGramBlock A B) ↔
      ∃ c : K, c ≠ 0 ∧
        (∃ u : Fin 2 → K, gramQuadraticValue A u = c) ∧
        ∃ v : Fin 2 → K, gramQuadraticValue B v = c := by
  constructor
  · intro hiso
    rcases (gramIsotropic_binaryPairDifferenceGramBlock_iff A B).mp hiso with
      hA | hB | hcommon
    · obtain ⟨c, hc, hBrep⟩ :=
        exists_binary_gramQuadraticValue_eq_ne_zero B hB_symm hB_det hchar
      exact ⟨c, hc,
        exists_binary_gramQuadraticValue_eq_of_gramIsotropic
          A hA_symm hA_det hchar hA c,
        hBrep⟩
    · obtain ⟨c, hc, hArep⟩ :=
        exists_binary_gramQuadraticValue_eq_ne_zero A hA_symm hA_det hchar
      exact ⟨c, hc, hArep,
        exists_binary_gramQuadraticValue_eq_of_gramIsotropic
          B hB_symm hB_det hchar hB c⟩
    · exact hcommon
  · intro hcommon
    exact (gramIsotropic_binaryPairDifferenceGramBlock_iff A B).mpr
      (Or.inr (Or.inr hcommon))

/-- Every nonsingular symmetric rank-four Gram matrix in characteristic not
two is congruent to a difference block of two nonsingular symmetric binary
forms, with Gram isotropy preserved. -/
theorem exists_gramMatrix_congr_binaryPairDifferenceGramBlock_gramIsotropic_iff
    {K : Type*} [Field K]
    (M : Matrix (Fin 4) (Fin 4) K)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ (A B : Matrix (Fin 2) (Fin 2) K) (P : GL (Fin 4) K),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
        P.1ᵀ * M * P.1 = binaryPairDifferenceGramBlock A B ∧
        (GramIsotropic M ↔
          GramIsotropic (binaryPairDifferenceGramBlock A B)) := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal M hM_symm hM_det hchar
  let A : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![d 0, d 1]
  let B : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![-d 2, -d 3]
  have hblock : Matrix.diagonal d = binaryPairDifferenceGramBlock A B := by
    change Matrix.diagonal d = differenceGramBlock
      (Matrix.diagonal ![d 0, d 1]) (Matrix.diagonal ![-d 2, -d 3])
    calc
      Matrix.diagonal d = differenceGramBlock
          (Matrix.diagonal (fun i : Fin 2 ↦ d (Fin.castAdd 2 i)))
          (Matrix.diagonal (fun i : Fin 2 ↦ -d (Fin.natAdd 2 i))) :=
        (differenceGramBlock_diagonal_split (m := 2) (n := 2) d).symm
      _ = differenceGramBlock (Matrix.diagonal ![d 0, d 1])
          (Matrix.diagonal ![-d 2, -d 3]) := by
        congr 3 <;> funext i <;> fin_cases i <;> rfl
  have hcongr : P.1ᵀ * M * P.1 = binaryPairDifferenceGramBlock A B :=
    hP.trans hblock
  refine ⟨A, B, P, ?_, ?_, ?_, ?_, hcongr, ?_⟩
  · simp [A]
  · simp [A, Matrix.det_diagonal, Fin.prod_univ_two, hd]
  · simp [B]
  · simp [B, Matrix.det_diagonal, Fin.prod_univ_two, hd]
  · exact gramIsotropic_iff_of_isCongruent ⟨P, hcongr⟩

/-- The difference of a binary and a ternary form is isotropic exactly when
one side is isotropic or the two forms represent a common nonzero value. -/
theorem gramIsotropic_binaryTernaryDifferenceGramBlock_iff
    {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) (B : Matrix (Fin 3) (Fin 3) K) :
    GramIsotropic (binaryTernaryDifferenceGramBlock A B) ↔
      GramIsotropic A ∨ GramIsotropic B ∨
        ∃ c : K, c ≠ 0 ∧
          (∃ u : Fin 2 → K, gramQuadraticValue A u = c) ∧
          ∃ v : Fin 3 → K, gramQuadraticValue B v = c := by
  have finTwo_eta (w : Fin 2 → K) : ![w 0, w 1] = w := by
    funext i
    fin_cases i <;> rfl
  have finThree_eta (w : Fin 3 → K) : ![w 0, w 1, w 2] = w := by
    funext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨x, hx, hvalue⟩
    let u : Fin 2 → K := ![x 0, x 1]
    let v : Fin 3 → K := ![x 2, x 3, x 4]
    have huv : gramQuadraticValue A u = gramQuadraticValue B v := by
      rw [gramQuadraticValue_binaryTernaryDifferenceGramBlock] at hvalue
      change gramQuadraticValue A u - gramQuadraticValue B v = 0 at hvalue
      linear_combination hvalue
    by_cases hu : u = 0
    · right
      left
      refine ⟨v, ?_, ?_⟩
      · intro hv
        apply hx
        funext i
        fin_cases i
        · exact congrFun hu 0
        · exact congrFun hu 1
        · exact congrFun hv 0
        · exact congrFun hv 1
        · exact congrFun hv 2
      · rw [hu] at huv
        simpa [gramQuadraticValue] using huv.symm
    · by_cases hv : v = 0
      · left
        refine ⟨u, hu, ?_⟩
        rw [hv] at huv
        simpa [gramQuadraticValue] using huv
      · by_cases hc : gramQuadraticValue A u = 0
        · left
          exact ⟨u, hu, hc⟩
        · right
          right
          exact ⟨gramQuadraticValue A u, hc, ⟨u, rfl⟩, ⟨v, huv.symm⟩⟩
  · rintro (hA | hB | hcommon)
    · rcases hA with ⟨u, hu, hvalue⟩
      refine ⟨![u 0, u 1, 0, 0, 0], ?_, ?_⟩
      · intro hx
        apply hu
        funext i
        fin_cases i
        · exact congrFun hx 0
        · exact congrFun hx 1
      · rw [gramQuadraticValue_binaryTernaryDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1] -
          gramQuadraticValue B ![0, 0, 0] = 0
        rw [finTwo_eta]
        change gramQuadraticValue A u - gramQuadraticValue B 0 = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hB with ⟨v, hv, hvalue⟩
      refine ⟨![0, 0, v 0, v 1, v 2], ?_, ?_⟩
      · intro hx
        apply hv
        funext i
        fin_cases i
        · exact congrFun hx 2
        · exact congrFun hx 3
        · exact congrFun hx 4
      · rw [gramQuadraticValue_binaryTernaryDifferenceGramBlock]
        change gramQuadraticValue A ![0, 0] -
          gramQuadraticValue B ![v 0, v 1, v 2] = 0
        rw [finThree_eta]
        change gramQuadraticValue A 0 - gramQuadraticValue B v = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hcommon with ⟨c, hc, ⟨u, hu⟩, ⟨v, hv⟩⟩
      refine ⟨![u 0, u 1, v 0, v 1, v 2], ?_, ?_⟩
      · intro hx
        apply hc
        rw [← hu]
        have hu0 : u = 0 := by
          funext i
          fin_cases i
          · exact congrFun hx 0
          · exact congrFun hx 1
        simp [hu0, gramQuadraticValue]
      · rw [gramQuadraticValue_binaryTernaryDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1] -
          gramQuadraticValue B ![v 0, v 1, v 2] = 0
        rw [finTwo_eta, finThree_eta, hu, hv]
        simp

/-- The difference of two ternary forms is isotropic exactly when one side is
isotropic or the two forms represent a common nonzero value. -/
theorem gramIsotropic_ternaryPairDifferenceGramBlock_iff
    {K : Type*} [Field K]
    (A B : Matrix (Fin 3) (Fin 3) K) :
    GramIsotropic (ternaryPairDifferenceGramBlock A B) ↔
      GramIsotropic A ∨ GramIsotropic B ∨
        ∃ c : K, c ≠ 0 ∧
          (∃ u : Fin 3 → K, gramQuadraticValue A u = c) ∧
          ∃ v : Fin 3 → K, gramQuadraticValue B v = c := by
  have finThree_eta (w : Fin 3 → K) : ![w 0, w 1, w 2] = w := by
    funext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨x, hx, hvalue⟩
    let u : Fin 3 → K := ![x 0, x 1, x 2]
    let v : Fin 3 → K := ![x 3, x 4, x 5]
    have huv : gramQuadraticValue A u = gramQuadraticValue B v := by
      rw [gramQuadraticValue_ternaryPairDifferenceGramBlock] at hvalue
      change gramQuadraticValue A u - gramQuadraticValue B v = 0 at hvalue
      linear_combination hvalue
    by_cases hu : u = 0
    · right
      left
      refine ⟨v, ?_, ?_⟩
      · intro hv
        apply hx
        funext i
        fin_cases i
        · exact congrFun hu 0
        · exact congrFun hu 1
        · exact congrFun hu 2
        · exact congrFun hv 0
        · exact congrFun hv 1
        · exact congrFun hv 2
      · rw [hu] at huv
        simpa [gramQuadraticValue] using huv.symm
    · by_cases hv : v = 0
      · left
        refine ⟨u, hu, ?_⟩
        rw [hv] at huv
        simpa [gramQuadraticValue] using huv
      · by_cases hc : gramQuadraticValue A u = 0
        · left
          exact ⟨u, hu, hc⟩
        · right
          right
          exact ⟨gramQuadraticValue A u, hc, ⟨u, rfl⟩, ⟨v, huv.symm⟩⟩
  · rintro (hA | hB | hcommon)
    · rcases hA with ⟨u, hu, hvalue⟩
      refine ⟨![u 0, u 1, u 2, 0, 0, 0], ?_, ?_⟩
      · intro hx
        apply hu
        funext i
        fin_cases i
        · exact congrFun hx 0
        · exact congrFun hx 1
        · exact congrFun hx 2
      · rw [gramQuadraticValue_ternaryPairDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1, u 2] -
          gramQuadraticValue B ![0, 0, 0] = 0
        rw [finThree_eta]
        change gramQuadraticValue A u - gramQuadraticValue B 0 = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hB with ⟨v, hv, hvalue⟩
      refine ⟨![0, 0, 0, v 0, v 1, v 2], ?_, ?_⟩
      · intro hx
        apply hv
        funext i
        fin_cases i
        · exact congrFun hx 3
        · exact congrFun hx 4
        · exact congrFun hx 5
      · rw [gramQuadraticValue_ternaryPairDifferenceGramBlock]
        change gramQuadraticValue A ![0, 0, 0] -
          gramQuadraticValue B ![v 0, v 1, v 2] = 0
        rw [finThree_eta]
        change gramQuadraticValue A 0 - gramQuadraticValue B v = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hcommon with ⟨c, hc, ⟨u, hu⟩, ⟨v, hv⟩⟩
      refine ⟨![u 0, u 1, u 2, v 0, v 1, v 2], ?_, ?_⟩
      · intro hx
        apply hc
        rw [← hu]
        have hu0 : u = 0 := by
          funext i
          fin_cases i
          · exact congrFun hx 0
          · exact congrFun hx 1
          · exact congrFun hx 2
        simp [hu0, gramQuadraticValue]
      · rw [gramQuadraticValue_ternaryPairDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1, u 2] -
          gramQuadraticValue B ![v 0, v 1, v 2] = 0
        rw [finThree_eta, finThree_eta, hu, hv]
        simp

/-- Every nonsingular symmetric ternary Gram matrix in characteristic not two
represents some nonzero scalar. -/
theorem exists_ternary_gramQuadraticValue_eq_ne_zero
    {K : Type*} [Field K] (A : Matrix (Fin 3) (Fin 3) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ c : K, c ≠ 0 ∧
      ∃ v : Fin 3 → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det hchar
  refine ⟨d 0, hd 0, ?_⟩
  apply (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) (d 0)).mpr
  refine ⟨![1, 0, 0], ?_⟩
  simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- For nonsingular symmetric binary and ternary forms, isotropy of their
difference block is equivalent to representing one common nonzero scalar. -/
theorem gramIsotropic_binaryTernaryDifferenceGramBlock_iff_exists_common_value
    {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) (B : Matrix (Fin 3) (Fin 3) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    GramIsotropic (binaryTernaryDifferenceGramBlock A B) ↔
      ∃ c : K, c ≠ 0 ∧
        (∃ u : Fin 2 → K, gramQuadraticValue A u = c) ∧
        ∃ v : Fin 3 → K, gramQuadraticValue B v = c := by
  constructor
  · intro hiso
    rcases (gramIsotropic_binaryTernaryDifferenceGramBlock_iff A B).mp hiso with
      hA | hB | hcommon
    · obtain ⟨c, hc, hBrep⟩ :=
        exists_ternary_gramQuadraticValue_eq_ne_zero
          B hB_symm hB_det hchar
      exact ⟨c, hc,
        exists_binary_gramQuadraticValue_eq_of_gramIsotropic
          A hA_symm hA_det hchar hA c,
        hBrep⟩
    · obtain ⟨c, hc, hArep⟩ :=
        exists_binary_gramQuadraticValue_eq_ne_zero A hA_symm hA_det hchar
      exact ⟨c, hc, hArep,
        exists_ternary_gramQuadraticValue_eq_of_gramIsotropic
          B hB_symm hB_det hchar hB c⟩
    · exact hcommon
  · intro hcommon
    exact (gramIsotropic_binaryTernaryDifferenceGramBlock_iff A B).mpr
      (Or.inr (Or.inr hcommon))

/-- Every nonsingular symmetric rank-five Gram matrix in characteristic not
two is congruent to a difference block of nonsingular symmetric binary and
ternary forms, with Gram isotropy preserved. -/
theorem exists_gramMatrix_congr_binaryTernaryDifferenceGramBlock_gramIsotropic_iff
    {K : Type*} [Field K]
    (M : Matrix (Fin 5) (Fin 5) K)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ (A : Matrix (Fin 2) (Fin 2) K)
      (B : Matrix (Fin 3) (Fin 3) K) (P : GL (Fin 5) K),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
        P.1ᵀ * M * P.1 = binaryTernaryDifferenceGramBlock A B ∧
        (GramIsotropic M ↔
          GramIsotropic (binaryTernaryDifferenceGramBlock A B)) := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal M hM_symm hM_det hchar
  let A : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![d 0, d 1]
  let B : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![-d 2, -d 3, -d 4]
  have hblock : Matrix.diagonal d = binaryTernaryDifferenceGramBlock A B := by
    change Matrix.diagonal d = differenceGramBlock
      (Matrix.diagonal ![d 0, d 1]) (Matrix.diagonal ![-d 2, -d 3, -d 4])
    calc
      Matrix.diagonal d = differenceGramBlock
          (Matrix.diagonal (fun i : Fin 2 ↦ d (Fin.castAdd 3 i)))
          (Matrix.diagonal (fun i : Fin 3 ↦ -d (Fin.natAdd 2 i))) :=
        (differenceGramBlock_diagonal_split (m := 2) (n := 3) d).symm
      _ = differenceGramBlock (Matrix.diagonal ![d 0, d 1])
          (Matrix.diagonal ![-d 2, -d 3, -d 4]) := by
        congr 3 <;> funext i <;> fin_cases i <;> rfl
  have hcongr : P.1ᵀ * M * P.1 = binaryTernaryDifferenceGramBlock A B :=
    hP.trans hblock
  refine ⟨A, B, P, ?_, ?_, ?_, ?_, hcongr, ?_⟩
  · simp [A]
  · simp [A, Matrix.det_diagonal, Fin.prod_univ_two, hd]
  · simp [B]
  · simp [B, Matrix.det_diagonal, Fin.prod_univ_three, hd]
  · exact gramIsotropic_iff_of_isCongruent ⟨P, hcongr⟩

/-- For nonsingular symmetric ternary forms, isotropy of their difference
block is equivalent to representing one common nonzero scalar. -/
theorem gramIsotropic_ternaryPairDifferenceGramBlock_iff_exists_common_value
    {K : Type*} [Field K]
    (A B : Matrix (Fin 3) (Fin 3) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    GramIsotropic (ternaryPairDifferenceGramBlock A B) ↔
      ∃ c : K, c ≠ 0 ∧
        (∃ u : Fin 3 → K, gramQuadraticValue A u = c) ∧
        ∃ v : Fin 3 → K, gramQuadraticValue B v = c := by
  constructor
  · intro hiso
    rcases (gramIsotropic_ternaryPairDifferenceGramBlock_iff A B).mp hiso with
      hA | hB | hcommon
    · obtain ⟨c, hc, hBrep⟩ :=
        exists_ternary_gramQuadraticValue_eq_ne_zero
          B hB_symm hB_det hchar
      exact ⟨c, hc,
        exists_ternary_gramQuadraticValue_eq_of_gramIsotropic
          A hA_symm hA_det hchar hA c,
        hBrep⟩
    · obtain ⟨c, hc, hArep⟩ :=
        exists_ternary_gramQuadraticValue_eq_ne_zero
          A hA_symm hA_det hchar
      exact ⟨c, hc, hArep,
        exists_ternary_gramQuadraticValue_eq_of_gramIsotropic
          B hB_symm hB_det hchar hB c⟩
    · exact hcommon
  · intro hcommon
    exact (gramIsotropic_ternaryPairDifferenceGramBlock_iff A B).mpr
      (Or.inr (Or.inr hcommon))

/-- Every nonsingular symmetric rank-six Gram matrix in characteristic not
two is congruent to a difference block of nonsingular symmetric ternary forms,
with Gram isotropy preserved. -/
theorem exists_gramMatrix_congr_ternaryPairDifferenceGramBlock_gramIsotropic_iff
    {K : Type*} [Field K]
    (M : Matrix (Fin 6) (Fin 6) K)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ (A B : Matrix (Fin 3) (Fin 3) K) (P : GL (Fin 6) K),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
        P.1ᵀ * M * P.1 = ternaryPairDifferenceGramBlock A B ∧
        (GramIsotropic M ↔
          GramIsotropic (ternaryPairDifferenceGramBlock A B)) := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal M hM_symm hM_det hchar
  let A : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![d 0, d 1, d 2]
  let B : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![-d 3, -d 4, -d 5]
  have hblock : Matrix.diagonal d = ternaryPairDifferenceGramBlock A B := by
    change Matrix.diagonal d = differenceGramBlock
      (Matrix.diagonal ![d 0, d 1, d 2])
      (Matrix.diagonal ![-d 3, -d 4, -d 5])
    calc
      Matrix.diagonal d = differenceGramBlock
          (Matrix.diagonal (fun i : Fin 3 ↦ d (Fin.castAdd 3 i)))
          (Matrix.diagonal (fun i : Fin 3 ↦ -d (Fin.natAdd 3 i))) :=
        (differenceGramBlock_diagonal_split (m := 3) (n := 3) d).symm
      _ = differenceGramBlock (Matrix.diagonal ![d 0, d 1, d 2])
          (Matrix.diagonal ![-d 3, -d 4, -d 5]) := by
        congr 3 <;> funext i <;> fin_cases i <;> rfl
  have hcongr : P.1ᵀ * M * P.1 = ternaryPairDifferenceGramBlock A B :=
    hP.trans hblock
  refine ⟨A, B, P, ?_, ?_, ?_, ?_, hcongr, ?_⟩
  · simp [A]
  · simp [A, Matrix.det_diagonal, Fin.prod_univ_three, hd]
  · simp [B]
  · simp [B, Matrix.det_diagonal, Fin.prod_univ_three, hd]
  · exact gramIsotropic_iff_of_isCongruent ⟨P, hcongr⟩

/-- The difference of a ternary and a quaternary form is isotropic exactly
when one side is isotropic or the two forms represent a common nonzero value. -/
theorem gramIsotropic_ternaryQuaternaryDifferenceGramBlock_iff
    {K : Type*} [Field K]
    (A : Matrix (Fin 3) (Fin 3) K) (B : Matrix (Fin 4) (Fin 4) K) :
    GramIsotropic (ternaryQuaternaryDifferenceGramBlock A B) ↔
      GramIsotropic A ∨ GramIsotropic B ∨
        ∃ c : K, c ≠ 0 ∧
          (∃ u : Fin 3 → K, gramQuadraticValue A u = c) ∧
          ∃ v : Fin 4 → K, gramQuadraticValue B v = c := by
  have finThree_eta (w : Fin 3 → K) : ![w 0, w 1, w 2] = w := by
    funext i
    fin_cases i <;> rfl
  have finFour_eta (w : Fin 4 → K) : ![w 0, w 1, w 2, w 3] = w := by
    funext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨x, hx, hvalue⟩
    let u : Fin 3 → K := ![x 0, x 1, x 2]
    let v : Fin 4 → K := ![x 3, x 4, x 5, x 6]
    have huv : gramQuadraticValue A u = gramQuadraticValue B v := by
      rw [gramQuadraticValue_ternaryQuaternaryDifferenceGramBlock] at hvalue
      change gramQuadraticValue A u - gramQuadraticValue B v = 0 at hvalue
      linear_combination hvalue
    by_cases hu : u = 0
    · right
      left
      refine ⟨v, ?_, ?_⟩
      · intro hv
        apply hx
        funext i
        fin_cases i
        · exact congrFun hu 0
        · exact congrFun hu 1
        · exact congrFun hu 2
        · exact congrFun hv 0
        · exact congrFun hv 1
        · exact congrFun hv 2
        · exact congrFun hv 3
      · rw [hu] at huv
        simpa [gramQuadraticValue] using huv.symm
    · by_cases hv : v = 0
      · left
        refine ⟨u, hu, ?_⟩
        rw [hv] at huv
        simpa [gramQuadraticValue] using huv
      · by_cases hc : gramQuadraticValue A u = 0
        · left
          exact ⟨u, hu, hc⟩
        · right
          right
          exact ⟨gramQuadraticValue A u, hc, ⟨u, rfl⟩, ⟨v, huv.symm⟩⟩
  · rintro (hA | hB | hcommon)
    · rcases hA with ⟨u, hu, hvalue⟩
      refine ⟨![u 0, u 1, u 2, 0, 0, 0, 0], ?_, ?_⟩
      · intro hx
        apply hu
        funext i
        fin_cases i
        · exact congrFun hx 0
        · exact congrFun hx 1
        · exact congrFun hx 2
      · rw [gramQuadraticValue_ternaryQuaternaryDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1, u 2] -
          gramQuadraticValue B ![0, 0, 0, 0] = 0
        rw [finThree_eta]
        change gramQuadraticValue A u - gramQuadraticValue B 0 = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hB with ⟨v, hv, hvalue⟩
      refine ⟨![0, 0, 0, v 0, v 1, v 2, v 3], ?_, ?_⟩
      · intro hx
        apply hv
        funext i
        fin_cases i
        · exact congrFun hx 3
        · exact congrFun hx 4
        · exact congrFun hx 5
        · exact congrFun hx 6
      · rw [gramQuadraticValue_ternaryQuaternaryDifferenceGramBlock]
        change gramQuadraticValue A ![0, 0, 0] -
          gramQuadraticValue B ![v 0, v 1, v 2, v 3] = 0
        rw [finFour_eta]
        change gramQuadraticValue A 0 - gramQuadraticValue B v = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hcommon with ⟨c, hc, ⟨u, hu⟩, ⟨v, hv⟩⟩
      refine ⟨![u 0, u 1, u 2, v 0, v 1, v 2, v 3], ?_, ?_⟩
      · intro hx
        apply hc
        rw [← hu]
        have hu0 : u = 0 := by
          funext i
          fin_cases i
          · exact congrFun hx 0
          · exact congrFun hx 1
          · exact congrFun hx 2
        simp [hu0, gramQuadraticValue]
      · rw [gramQuadraticValue_ternaryQuaternaryDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1, u 2] -
          gramQuadraticValue B ![v 0, v 1, v 2, v 3] = 0
        rw [finThree_eta, finFour_eta, hu, hv]
        simp

/-- Every nonsingular symmetric quaternary Gram matrix in characteristic not
two represents some nonzero scalar. -/
theorem exists_quaternary_gramQuadraticValue_eq_ne_zero
    {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ c : K, c ≠ 0 ∧
      ∃ v : Fin 4 → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det hchar
  refine ⟨d 0, hd 0, ?_⟩
  apply (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) (d 0)).mpr
  refine ⟨![1, 0, 0, 0], ?_⟩
  simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- For nonsingular symmetric ternary and quaternary forms, isotropy of their
difference block is equivalent to representing one common nonzero scalar. -/
theorem gramIsotropic_ternaryQuaternaryDifferenceGramBlock_iff_exists_common_value
    {K : Type*} [Field K]
    (A : Matrix (Fin 3) (Fin 3) K) (B : Matrix (Fin 4) (Fin 4) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    GramIsotropic (ternaryQuaternaryDifferenceGramBlock A B) ↔
      ∃ c : K, c ≠ 0 ∧
        (∃ u : Fin 3 → K, gramQuadraticValue A u = c) ∧
        ∃ v : Fin 4 → K, gramQuadraticValue B v = c := by
  constructor
  · intro hiso
    rcases (gramIsotropic_ternaryQuaternaryDifferenceGramBlock_iff A B).mp hiso with
      hA | hB | hcommon
    · obtain ⟨c, hc, hBrep⟩ :=
        exists_quaternary_gramQuadraticValue_eq_ne_zero
          B hB_symm hB_det hchar
      exact ⟨c, hc,
        exists_ternary_gramQuadraticValue_eq_of_gramIsotropic
          A hA_symm hA_det hchar hA c,
        hBrep⟩
    · obtain ⟨c, hc, hArep⟩ :=
        exists_ternary_gramQuadraticValue_eq_ne_zero
          A hA_symm hA_det hchar
      exact ⟨c, hc, hArep,
        exists_quaternary_gramQuadraticValue_eq_of_gramIsotropic
          B hB_symm hB_det hchar hB c⟩
    · exact hcommon
  · intro hcommon
    exact (gramIsotropic_ternaryQuaternaryDifferenceGramBlock_iff A B).mpr
      (Or.inr (Or.inr hcommon))

/-- Every nonsingular symmetric rank-seven Gram matrix in characteristic not
two is congruent to a difference block of nonsingular symmetric ternary and
quaternary forms, with Gram isotropy preserved. -/
theorem exists_gramMatrix_congr_ternaryQuaternaryDifferenceGramBlock_gramIsotropic_iff
    {K : Type*} [Field K]
    (M : Matrix (Fin 7) (Fin 7) K)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ (A : Matrix (Fin 3) (Fin 3) K)
      (B : Matrix (Fin 4) (Fin 4) K) (P : GL (Fin 7) K),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
        P.1ᵀ * M * P.1 = ternaryQuaternaryDifferenceGramBlock A B ∧
        (GramIsotropic M ↔
          GramIsotropic (ternaryQuaternaryDifferenceGramBlock A B)) := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal M hM_symm hM_det hchar
  let A : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![d 0, d 1, d 2]
  let B : Matrix (Fin 4) (Fin 4) K :=
    Matrix.diagonal ![-d 3, -d 4, -d 5, -d 6]
  have hblock : Matrix.diagonal d =
      ternaryQuaternaryDifferenceGramBlock A B := by
    change Matrix.diagonal d = differenceGramBlock
      (Matrix.diagonal ![d 0, d 1, d 2])
      (Matrix.diagonal ![-d 3, -d 4, -d 5, -d 6])
    calc
      Matrix.diagonal d = differenceGramBlock
          (Matrix.diagonal (fun i : Fin 3 ↦ d (Fin.castAdd 4 i)))
          (Matrix.diagonal (fun i : Fin 4 ↦ -d (Fin.natAdd 3 i))) :=
        (differenceGramBlock_diagonal_split (m := 3) (n := 4) d).symm
      _ = differenceGramBlock (Matrix.diagonal ![d 0, d 1, d 2])
          (Matrix.diagonal ![-d 3, -d 4, -d 5, -d 6]) := by
        congr 3 <;> funext i <;> fin_cases i <;> rfl
  have hcongr : P.1ᵀ * M * P.1 =
      ternaryQuaternaryDifferenceGramBlock A B := hP.trans hblock
  refine ⟨A, B, P, ?_, ?_, ?_, ?_, hcongr, ?_⟩
  · simp [A]
  · simp [A, Matrix.det_diagonal, Fin.prod_univ_three, hd]
  · simp [B]
  · simp [B, Matrix.det_diagonal, Fin.prod_univ_four, hd]
  · exact gramIsotropic_iff_of_isCongruent ⟨P, hcongr⟩

/-- The difference of two quaternary forms is isotropic exactly when one side
is isotropic or the two forms represent a common nonzero value. -/
theorem gramIsotropic_quaternaryPairDifferenceGramBlock_iff
    {K : Type*} [Field K]
    (A B : Matrix (Fin 4) (Fin 4) K) :
    GramIsotropic (quaternaryPairDifferenceGramBlock A B) ↔
      GramIsotropic A ∨ GramIsotropic B ∨
        ∃ c : K, c ≠ 0 ∧
          (∃ u : Fin 4 → K, gramQuadraticValue A u = c) ∧
          ∃ v : Fin 4 → K, gramQuadraticValue B v = c := by
  have finFour_eta (w : Fin 4 → K) : ![w 0, w 1, w 2, w 3] = w := by
    funext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨x, hx, hvalue⟩
    let u : Fin 4 → K := ![x 0, x 1, x 2, x 3]
    let v : Fin 4 → K := ![x 4, x 5, x 6, x 7]
    have huv : gramQuadraticValue A u = gramQuadraticValue B v := by
      rw [gramQuadraticValue_quaternaryPairDifferenceGramBlock] at hvalue
      change gramQuadraticValue A u - gramQuadraticValue B v = 0 at hvalue
      linear_combination hvalue
    by_cases hu : u = 0
    · right
      left
      refine ⟨v, ?_, ?_⟩
      · intro hv
        apply hx
        funext i
        fin_cases i
        · exact congrFun hu 0
        · exact congrFun hu 1
        · exact congrFun hu 2
        · exact congrFun hu 3
        · exact congrFun hv 0
        · exact congrFun hv 1
        · exact congrFun hv 2
        · exact congrFun hv 3
      · rw [hu] at huv
        simpa [gramQuadraticValue] using huv.symm
    · by_cases hv : v = 0
      · left
        refine ⟨u, hu, ?_⟩
        rw [hv] at huv
        simpa [gramQuadraticValue] using huv
      · by_cases hc : gramQuadraticValue A u = 0
        · left
          exact ⟨u, hu, hc⟩
        · right
          right
          exact ⟨gramQuadraticValue A u, hc, ⟨u, rfl⟩, ⟨v, huv.symm⟩⟩
  · rintro (hA | hB | hcommon)
    · rcases hA with ⟨u, hu, hvalue⟩
      refine ⟨![u 0, u 1, u 2, u 3, 0, 0, 0, 0], ?_, ?_⟩
      · intro hx
        apply hu
        funext i
        fin_cases i
        · exact congrFun hx 0
        · exact congrFun hx 1
        · exact congrFun hx 2
        · exact congrFun hx 3
      · rw [gramQuadraticValue_quaternaryPairDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1, u 2, u 3] -
          gramQuadraticValue B ![0, 0, 0, 0] = 0
        rw [finFour_eta]
        change gramQuadraticValue A u - gramQuadraticValue B 0 = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hB with ⟨v, hv, hvalue⟩
      refine ⟨![0, 0, 0, 0, v 0, v 1, v 2, v 3], ?_, ?_⟩
      · intro hx
        apply hv
        funext i
        fin_cases i
        · exact congrFun hx 4
        · exact congrFun hx 5
        · exact congrFun hx 6
        · exact congrFun hx 7
      · rw [gramQuadraticValue_quaternaryPairDifferenceGramBlock]
        change gramQuadraticValue A ![0, 0, 0, 0] -
          gramQuadraticValue B ![v 0, v 1, v 2, v 3] = 0
        rw [finFour_eta]
        change gramQuadraticValue A 0 - gramQuadraticValue B v = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hcommon with ⟨c, hc, ⟨u, hu⟩, ⟨v, hv⟩⟩
      refine ⟨![u 0, u 1, u 2, u 3, v 0, v 1, v 2, v 3], ?_, ?_⟩
      · intro hx
        apply hc
        rw [← hu]
        have hu0 : u = 0 := by
          funext i
          fin_cases i
          · exact congrFun hx 0
          · exact congrFun hx 1
          · exact congrFun hx 2
          · exact congrFun hx 3
        simp [hu0, gramQuadraticValue]
      · rw [gramQuadraticValue_quaternaryPairDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1, u 2, u 3] -
          gramQuadraticValue B ![v 0, v 1, v 2, v 3] = 0
        rw [finFour_eta, finFour_eta, hu, hv]
        simp

/-- For nonsingular symmetric quaternary forms, isotropy of their difference
block is equivalent to representing one common nonzero scalar. -/
theorem gramIsotropic_quaternaryPairDifferenceGramBlock_iff_exists_common_value
    {K : Type*} [Field K]
    (A B : Matrix (Fin 4) (Fin 4) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    GramIsotropic (quaternaryPairDifferenceGramBlock A B) ↔
      ∃ c : K, c ≠ 0 ∧
        (∃ u : Fin 4 → K, gramQuadraticValue A u = c) ∧
        ∃ v : Fin 4 → K, gramQuadraticValue B v = c := by
  constructor
  · intro hiso
    rcases (gramIsotropic_quaternaryPairDifferenceGramBlock_iff A B).mp hiso with
      hA | hB | hcommon
    · obtain ⟨c, hc, hBrep⟩ :=
        exists_quaternary_gramQuadraticValue_eq_ne_zero
          B hB_symm hB_det hchar
      exact ⟨c, hc,
        exists_quaternary_gramQuadraticValue_eq_of_gramIsotropic
          A hA_symm hA_det hchar hA c,
        hBrep⟩
    · obtain ⟨c, hc, hArep⟩ :=
        exists_quaternary_gramQuadraticValue_eq_ne_zero
          A hA_symm hA_det hchar
      exact ⟨c, hc, hArep,
        exists_quaternary_gramQuadraticValue_eq_of_gramIsotropic
          B hB_symm hB_det hchar hB c⟩
    · exact hcommon
  · intro hcommon
    exact (gramIsotropic_quaternaryPairDifferenceGramBlock_iff A B).mpr
      (Or.inr (Or.inr hcommon))

/-- Every nonsingular symmetric rank-eight Gram matrix in characteristic not
two is congruent to a difference block of nonsingular symmetric quaternary
forms, with Gram isotropy preserved. -/
theorem exists_gramMatrix_congr_quaternaryPairDifferenceGramBlock_gramIsotropic_iff
    {K : Type*} [Field K]
    (M : Matrix (Fin 8) (Fin 8) K)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ (A B : Matrix (Fin 4) (Fin 4) K) (P : GL (Fin 8) K),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
        P.1ᵀ * M * P.1 = quaternaryPairDifferenceGramBlock A B ∧
        (GramIsotropic M ↔
          GramIsotropic (quaternaryPairDifferenceGramBlock A B)) := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal M hM_symm hM_det hchar
  let A : Matrix (Fin 4) (Fin 4) K :=
    Matrix.diagonal ![d 0, d 1, d 2, d 3]
  let B : Matrix (Fin 4) (Fin 4) K :=
    Matrix.diagonal ![-d 4, -d 5, -d 6, -d 7]
  have hblock : Matrix.diagonal d =
      quaternaryPairDifferenceGramBlock A B := by
    change Matrix.diagonal d = differenceGramBlock
      (Matrix.diagonal ![d 0, d 1, d 2, d 3])
      (Matrix.diagonal ![-d 4, -d 5, -d 6, -d 7])
    calc
      Matrix.diagonal d = differenceGramBlock
          (Matrix.diagonal (fun i : Fin 4 ↦ d (Fin.castAdd 4 i)))
          (Matrix.diagonal (fun i : Fin 4 ↦ -d (Fin.natAdd 4 i))) :=
        (differenceGramBlock_diagonal_split (m := 4) (n := 4) d).symm
      _ = differenceGramBlock (Matrix.diagonal ![d 0, d 1, d 2, d 3])
          (Matrix.diagonal ![-d 4, -d 5, -d 6, -d 7]) := by
        congr 3 <;> funext i <;> fin_cases i <;> rfl
  have hcongr : P.1ᵀ * M * P.1 =
      quaternaryPairDifferenceGramBlock A B := hP.trans hblock
  refine ⟨A, B, P, ?_, ?_, ?_, ?_, hcongr, ?_⟩
  · simp [A]
  · simp [A, Matrix.det_diagonal, Fin.prod_univ_four, hd]
  · simp [B]
  · simp [B, Matrix.det_diagonal, Fin.prod_univ_four, hd]
  · exact gramIsotropic_iff_of_isCongruent ⟨P, hcongr⟩

/-- The difference of a quaternary and a quinary form is isotropic exactly
when one side is isotropic or the two forms represent a common nonzero value. -/
theorem gramIsotropic_quaternaryQuinaryDifferenceGramBlock_iff
    {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (B : Matrix (Fin 5) (Fin 5) K) :
    GramIsotropic (quaternaryQuinaryDifferenceGramBlock A B) ↔
      GramIsotropic A ∨ GramIsotropic B ∨
        ∃ c : K, c ≠ 0 ∧
          (∃ u : Fin 4 → K, gramQuadraticValue A u = c) ∧
          ∃ v : Fin 5 → K, gramQuadraticValue B v = c := by
  have finFour_eta (w : Fin 4 → K) : ![w 0, w 1, w 2, w 3] = w := by
    funext i
    fin_cases i <;> rfl
  have finFive_eta (w : Fin 5 → K) : ![w 0, w 1, w 2, w 3, w 4] = w := by
    funext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨x, hx, hvalue⟩
    let u : Fin 4 → K := ![x 0, x 1, x 2, x 3]
    let v : Fin 5 → K := ![x 4, x 5, x 6, x 7, x 8]
    have huv : gramQuadraticValue A u = gramQuadraticValue B v := by
      rw [gramQuadraticValue_quaternaryQuinaryDifferenceGramBlock] at hvalue
      change gramQuadraticValue A u - gramQuadraticValue B v = 0 at hvalue
      linear_combination hvalue
    by_cases hu : u = 0
    · right
      left
      refine ⟨v, ?_, ?_⟩
      · intro hv
        apply hx
        funext i
        fin_cases i
        · exact congrFun hu 0
        · exact congrFun hu 1
        · exact congrFun hu 2
        · exact congrFun hu 3
        · exact congrFun hv 0
        · exact congrFun hv 1
        · exact congrFun hv 2
        · exact congrFun hv 3
        · exact congrFun hv 4
      · rw [hu] at huv
        simpa [gramQuadraticValue] using huv.symm
    · by_cases hv : v = 0
      · left
        refine ⟨u, hu, ?_⟩
        rw [hv] at huv
        simpa [gramQuadraticValue] using huv
      · by_cases hc : gramQuadraticValue A u = 0
        · left
          exact ⟨u, hu, hc⟩
        · right
          right
          exact ⟨gramQuadraticValue A u, hc, ⟨u, rfl⟩, ⟨v, huv.symm⟩⟩
  · rintro (hA | hB | hcommon)
    · rcases hA with ⟨u, hu, hvalue⟩
      refine ⟨![u 0, u 1, u 2, u 3, 0, 0, 0, 0, 0], ?_, ?_⟩
      · intro hx
        apply hu
        funext i
        fin_cases i
        · exact congrFun hx 0
        · exact congrFun hx 1
        · exact congrFun hx 2
        · exact congrFun hx 3
      · rw [gramQuadraticValue_quaternaryQuinaryDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1, u 2, u 3] -
          gramQuadraticValue B ![0, 0, 0, 0, 0] = 0
        rw [finFour_eta]
        change gramQuadraticValue A u - gramQuadraticValue B 0 = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hB with ⟨v, hv, hvalue⟩
      refine ⟨![0, 0, 0, 0, v 0, v 1, v 2, v 3, v 4], ?_, ?_⟩
      · intro hx
        apply hv
        funext i
        fin_cases i
        · exact congrFun hx 4
        · exact congrFun hx 5
        · exact congrFun hx 6
        · exact congrFun hx 7
        · exact congrFun hx 8
      · rw [gramQuadraticValue_quaternaryQuinaryDifferenceGramBlock]
        change gramQuadraticValue A ![0, 0, 0, 0] -
          gramQuadraticValue B ![v 0, v 1, v 2, v 3, v 4] = 0
        rw [finFive_eta]
        change gramQuadraticValue A 0 - gramQuadraticValue B v = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hcommon with ⟨c, hc, ⟨u, hu⟩, ⟨v, hv⟩⟩
      refine ⟨![u 0, u 1, u 2, u 3, v 0, v 1, v 2, v 3, v 4], ?_, ?_⟩
      · intro hx
        apply hc
        rw [← hu]
        have hu0 : u = 0 := by
          funext i
          fin_cases i
          · exact congrFun hx 0
          · exact congrFun hx 1
          · exact congrFun hx 2
          · exact congrFun hx 3
        simp [hu0, gramQuadraticValue]
      · rw [gramQuadraticValue_quaternaryQuinaryDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1, u 2, u 3] -
          gramQuadraticValue B ![v 0, v 1, v 2, v 3, v 4] = 0
        rw [finFour_eta, finFive_eta, hu, hv]
        simp

/-- Every nonsingular symmetric quinary Gram matrix in characteristic not two
represents some nonzero scalar. -/
theorem exists_quinary_gramQuadraticValue_eq_ne_zero
    {K : Type*} [Field K] (A : Matrix (Fin 5) (Fin 5) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ c : K, c ≠ 0 ∧
      ∃ v : Fin 5 → K, gramQuadraticValue A v = c := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal A hA_symm hA_det hchar
  refine ⟨d 0, hd 0, ?_⟩
  apply (exists_gramQuadraticValue_eq_iff_of_isCongruent
    (show A.IsCongruent (Matrix.diagonal d) from ⟨P, hP⟩) (d 0)).mpr
  refine ⟨![1, 0, 0, 0, 0], ?_⟩
  simp [gramQuadraticValue, Matrix.mulVec, dotProduct, Fin.sum_univ_five]

/-- For nonsingular symmetric quaternary and quinary forms, isotropy of their
difference block is equivalent to representing one common nonzero scalar. -/
theorem gramIsotropic_quaternaryQuinaryDifferenceGramBlock_iff_exists_common_value
    {K : Type*} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (B : Matrix (Fin 5) (Fin 5) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    GramIsotropic (quaternaryQuinaryDifferenceGramBlock A B) ↔
      ∃ c : K, c ≠ 0 ∧
        (∃ u : Fin 4 → K, gramQuadraticValue A u = c) ∧
        ∃ v : Fin 5 → K, gramQuadraticValue B v = c := by
  constructor
  · intro hiso
    rcases (gramIsotropic_quaternaryQuinaryDifferenceGramBlock_iff A B).mp hiso with
      hA | hB | hcommon
    · obtain ⟨c, hc, hBrep⟩ :=
        exists_quinary_gramQuadraticValue_eq_ne_zero
          B hB_symm hB_det hchar
      exact ⟨c, hc,
        exists_quaternary_gramQuadraticValue_eq_of_gramIsotropic
          A hA_symm hA_det hchar hA c,
        hBrep⟩
    · obtain ⟨c, hc, hArep⟩ :=
        exists_quaternary_gramQuadraticValue_eq_ne_zero
          A hA_symm hA_det hchar
      exact ⟨c, hc, hArep,
        exists_quinary_gramQuadraticValue_eq_of_gramIsotropic
          B hB_symm hB_det hchar hB c⟩
    · exact hcommon
  · intro hcommon
    exact (gramIsotropic_quaternaryQuinaryDifferenceGramBlock_iff A B).mpr
      (Or.inr (Or.inr hcommon))

set_option maxHeartbeats 800000 in
/-- Every nonsingular symmetric rank-nine Gram matrix in characteristic not
two is congruent to a difference block of nonsingular symmetric quaternary and
quinary forms, with Gram isotropy preserved. -/
theorem exists_gramMatrix_congr_quaternaryQuinaryDifferenceGramBlock_gramIsotropic_iff
    {K : Type*} [Field K]
    (M : Matrix (Fin 9) (Fin 9) K)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ (A : Matrix (Fin 4) (Fin 4) K)
      (B : Matrix (Fin 5) (Fin 5) K) (P : GL (Fin 9) K),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
        P.1ᵀ * M * P.1 = quaternaryQuinaryDifferenceGramBlock A B ∧
        (GramIsotropic M ↔
          GramIsotropic (quaternaryQuinaryDifferenceGramBlock A B)) := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal M hM_symm hM_det hchar
  let A : Matrix (Fin 4) (Fin 4) K :=
    Matrix.diagonal ![d 0, d 1, d 2, d 3]
  let B : Matrix (Fin 5) (Fin 5) K :=
    Matrix.diagonal ![-d 4, -d 5, -d 6, -d 7, -d 8]
  have hblock : Matrix.diagonal d =
      quaternaryQuinaryDifferenceGramBlock A B := by
    change Matrix.diagonal d = differenceGramBlock
      (Matrix.diagonal ![d 0, d 1, d 2, d 3])
      (Matrix.diagonal ![-d 4, -d 5, -d 6, -d 7, -d 8])
    calc
      Matrix.diagonal d = differenceGramBlock
          (Matrix.diagonal (fun i : Fin 4 ↦ d (Fin.castAdd 5 i)))
          (Matrix.diagonal (fun i : Fin 5 ↦ -d (Fin.natAdd 4 i))) :=
        (differenceGramBlock_diagonal_split (m := 4) (n := 5) d).symm
      _ = differenceGramBlock (Matrix.diagonal ![d 0, d 1, d 2, d 3])
          (Matrix.diagonal ![-d 4, -d 5, -d 6, -d 7, -d 8]) := by
        congr 3 <;> funext i <;> fin_cases i <;> rfl
  have hcongr : P.1ᵀ * M * P.1 =
      quaternaryQuinaryDifferenceGramBlock A B := hP.trans hblock
  refine ⟨A, B, P, ?_, ?_, ?_, ?_, hcongr, ?_⟩
  · simp [A]
  · simp [A, Matrix.det_diagonal, Fin.prod_univ_four, hd]
  · simp [B]
  · simp [B, Matrix.det_diagonal, Fin.prod_univ_five, hd]
  · exact gramIsotropic_iff_of_isCongruent ⟨P, hcongr⟩

/-- The difference of two quinary forms is isotropic exactly when one side
is isotropic or the two forms represent a common nonzero value. -/
theorem gramIsotropic_quinaryPairDifferenceGramBlock_iff
    {K : Type*} [Field K]
    (A B : Matrix (Fin 5) (Fin 5) K) :
    GramIsotropic (quinaryPairDifferenceGramBlock A B) ↔
      GramIsotropic A ∨ GramIsotropic B ∨
        ∃ c : K, c ≠ 0 ∧
          (∃ u : Fin 5 → K, gramQuadraticValue A u = c) ∧
          ∃ v : Fin 5 → K, gramQuadraticValue B v = c := by
  have finFive_eta (w : Fin 5 → K) :
      ![w 0, w 1, w 2, w 3, w 4] = w := by
    funext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨x, hx, hvalue⟩
    let u : Fin 5 → K := ![x 0, x 1, x 2, x 3, x 4]
    let v : Fin 5 → K := ![x 5, x 6, x 7, x 8, x 9]
    have huv : gramQuadraticValue A u = gramQuadraticValue B v := by
      rw [gramQuadraticValue_quinaryPairDifferenceGramBlock] at hvalue
      change gramQuadraticValue A u - gramQuadraticValue B v = 0 at hvalue
      linear_combination hvalue
    by_cases hu : u = 0
    · right
      left
      refine ⟨v, ?_, ?_⟩
      · intro hv
        apply hx
        funext i
        fin_cases i
        · exact congrFun hu 0
        · exact congrFun hu 1
        · exact congrFun hu 2
        · exact congrFun hu 3
        · exact congrFun hu 4
        · exact congrFun hv 0
        · exact congrFun hv 1
        · exact congrFun hv 2
        · exact congrFun hv 3
        · exact congrFun hv 4
      · rw [hu] at huv
        simpa [gramQuadraticValue] using huv.symm
    · by_cases hv : v = 0
      · left
        refine ⟨u, hu, ?_⟩
        rw [hv] at huv
        simpa [gramQuadraticValue] using huv
      · by_cases hc : gramQuadraticValue A u = 0
        · left
          exact ⟨u, hu, hc⟩
        · right
          right
          exact ⟨gramQuadraticValue A u, hc, ⟨u, rfl⟩, ⟨v, huv.symm⟩⟩
  · rintro (hA | hB | hcommon)
    · rcases hA with ⟨u, hu, hvalue⟩
      refine ⟨![u 0, u 1, u 2, u 3, u 4, 0, 0, 0, 0, 0], ?_, ?_⟩
      · intro hx
        apply hu
        funext i
        fin_cases i
        · exact congrFun hx 0
        · exact congrFun hx 1
        · exact congrFun hx 2
        · exact congrFun hx 3
        · exact congrFun hx 4
      · rw [gramQuadraticValue_quinaryPairDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1, u 2, u 3, u 4] -
          gramQuadraticValue B ![0, 0, 0, 0, 0] = 0
        rw [finFive_eta]
        change gramQuadraticValue A u - gramQuadraticValue B 0 = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hB with ⟨v, hv, hvalue⟩
      refine ⟨![0, 0, 0, 0, 0, v 0, v 1, v 2, v 3, v 4], ?_, ?_⟩
      · intro hx
        apply hv
        funext i
        fin_cases i
        · exact congrFun hx 5
        · exact congrFun hx 6
        · exact congrFun hx 7
        · exact congrFun hx 8
        · exact congrFun hx 9
      · rw [gramQuadraticValue_quinaryPairDifferenceGramBlock]
        change gramQuadraticValue A ![0, 0, 0, 0, 0] -
          gramQuadraticValue B ![v 0, v 1, v 2, v 3, v 4] = 0
        rw [finFive_eta]
        change gramQuadraticValue A 0 - gramQuadraticValue B v = 0
        rw [hvalue]
        simp [gramQuadraticValue]
    · rcases hcommon with ⟨c, hc, ⟨u, hu⟩, ⟨v, hv⟩⟩
      refine ⟨![u 0, u 1, u 2, u 3, u 4, v 0, v 1, v 2, v 3, v 4], ?_, ?_⟩
      · intro hx
        apply hc
        rw [← hu]
        have hu0 : u = 0 := by
          funext i
          fin_cases i
          · exact congrFun hx 0
          · exact congrFun hx 1
          · exact congrFun hx 2
          · exact congrFun hx 3
          · exact congrFun hx 4
        simp [hu0, gramQuadraticValue]
      · rw [gramQuadraticValue_quinaryPairDifferenceGramBlock]
        change gramQuadraticValue A ![u 0, u 1, u 2, u 3, u 4] -
          gramQuadraticValue B ![v 0, v 1, v 2, v 3, v 4] = 0
        rw [finFive_eta, finFive_eta, hu, hv]
        simp

/-- For nonsingular symmetric quinary forms, isotropy of their difference
block is equivalent to representing one common nonzero scalar. -/
theorem gramIsotropic_quinaryPairDifferenceGramBlock_iff_exists_common_value
    {K : Type*} [Field K]
    (A B : Matrix (Fin 5) (Fin 5) K)
    (hA_symm : A.IsSymm) (hA_det : A.det ≠ 0)
    (hB_symm : B.IsSymm) (hB_det : B.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    GramIsotropic (quinaryPairDifferenceGramBlock A B) ↔
      ∃ c : K, c ≠ 0 ∧
        (∃ u : Fin 5 → K, gramQuadraticValue A u = c) ∧
        ∃ v : Fin 5 → K, gramQuadraticValue B v = c := by
  constructor
  · intro hiso
    rcases (gramIsotropic_quinaryPairDifferenceGramBlock_iff A B).mp hiso with
      hA | hB | hcommon
    · obtain ⟨c, hc, hBrep⟩ :=
        exists_quinary_gramQuadraticValue_eq_ne_zero
          B hB_symm hB_det hchar
      exact ⟨c, hc,
        exists_quinary_gramQuadraticValue_eq_of_gramIsotropic
          A hA_symm hA_det hchar hA c,
        hBrep⟩
    · obtain ⟨c, hc, hArep⟩ :=
        exists_quinary_gramQuadraticValue_eq_ne_zero
          A hA_symm hA_det hchar
      exact ⟨c, hc, hArep,
        exists_quinary_gramQuadraticValue_eq_of_gramIsotropic
          B hB_symm hB_det hchar hB c⟩
    · exact hcommon
  · intro hcommon
    exact (gramIsotropic_quinaryPairDifferenceGramBlock_iff A B).mpr
      (Or.inr (Or.inr hcommon))

set_option maxHeartbeats 800000 in
/-- Every nonsingular symmetric rank-ten Gram matrix in characteristic not
two is congruent to a difference block of nonsingular symmetric quinary
forms, with Gram isotropy preserved. -/
theorem exists_gramMatrix_congr_quinaryPairDifferenceGramBlock_gramIsotropic_iff
    {K : Type*} [Field K]
    (M : Matrix (Fin 10) (Fin 10) K)
    (hM_symm : M.IsSymm) (hM_det : M.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    ∃ (A B : Matrix (Fin 5) (Fin 5) K) (P : GL (Fin 10) K),
      A.IsSymm ∧ A.det ≠ 0 ∧ B.IsSymm ∧ B.det ≠ 0 ∧
        P.1ᵀ * M * P.1 = quinaryPairDifferenceGramBlock A B ∧
        (GramIsotropic M ↔
          GramIsotropic (quinaryPairDifferenceGramBlock A B)) := by
  obtain ⟨d, P, hd, hP⟩ :=
    exists_gramMatrix_congr_diagonal M hM_symm hM_det hchar
  let A : Matrix (Fin 5) (Fin 5) K :=
    Matrix.diagonal ![d 0, d 1, d 2, d 3, d 4]
  let B : Matrix (Fin 5) (Fin 5) K :=
    Matrix.diagonal ![-d 5, -d 6, -d 7, -d 8, -d 9]
  have hblock : Matrix.diagonal d =
      quinaryPairDifferenceGramBlock A B := by
    change Matrix.diagonal d = differenceGramBlock
      (Matrix.diagonal ![d 0, d 1, d 2, d 3, d 4])
      (Matrix.diagonal ![-d 5, -d 6, -d 7, -d 8, -d 9])
    calc
      Matrix.diagonal d = differenceGramBlock
          (Matrix.diagonal (fun i : Fin 5 ↦ d (Fin.castAdd 5 i)))
          (Matrix.diagonal (fun i : Fin 5 ↦ -d (Fin.natAdd 5 i))) :=
        (differenceGramBlock_diagonal_split (m := 5) (n := 5) d).symm
      _ = differenceGramBlock (Matrix.diagonal ![d 0, d 1, d 2, d 3, d 4])
          (Matrix.diagonal ![-d 5, -d 6, -d 7, -d 8, -d 9]) := by
        congr 3 <;> funext i <;> fin_cases i <;> rfl
  have hcongr : P.1ᵀ * M * P.1 =
      quinaryPairDifferenceGramBlock A B := hP.trans hblock
  refine ⟨A, B, P, ?_, ?_, ?_, ?_, hcongr, ?_⟩
  · simp [A]
  · simp [A, Matrix.det_diagonal, Fin.prod_univ_five, hd]
  · simp [B]
  · simp [B, Matrix.det_diagonal, Fin.prod_univ_five, hd]
  · exact gramIsotropic_iff_of_isCongruent ⟨P, hcongr⟩

end PositiveDefiniteIntegralLattice

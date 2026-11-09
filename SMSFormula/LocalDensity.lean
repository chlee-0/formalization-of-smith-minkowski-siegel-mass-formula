import SMSFormula.LocalDensityDefinitions
import SMSFormula.GenusDeterminantInvariants
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.LinearAlgebra.Matrix.BilinearForm

open Matrix

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

lemma coordinateLocalDualQuotientCount_eq_of_submodule_eq
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    {D E : Submodule ℤ (Fin n → ℤ)}
    (hDE : D = E)
    (hD_rank : Module.finrank ℤ D = n)
    (hE_rank : Module.finrank ℤ E = n) :
    coordinateLocalDualQuotientCount L p k D hD_rank =
      coordinateLocalDualQuotientCount L p k E hE_rank := by
  subst E
  have hproof : hD_rank = hE_rank := Subsingleton.elim _ _
  subst hproof
  rfl

/-- Away from `2`, the source-normalized and current quotient counts agree. -/
lemma associatedBilinearDualQuotientCount_eq_current_of_ne_two
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hp_two : p ≠ 2) :
    associatedBilinearDualQuotientCount L p k =
      localDualQuotientCount L p k := by
  unfold associatedBilinearDualQuotientCount
    localDualQuotientCount
  exact coordinateLocalDualQuotientCount_eq_of_submodule_eq L p k
    (L.associatedBilinearDualPadicDenominatorIntegralPreimage_eq_localDualPadicDenominatorIntegralPreimage_of_ne_two
      p k hp_two)
    (associatedBilinearDualPadicDenominatorIntegralPreimage_rank (n := n) L p k)
    (localDualPadicDenominatorIntegralPreimage_rank (n := n) L p k)

lemma coordinateLocalDualQuotientCount_localDualPadicCoordinateSubmodule_eq_pairingMatrixLocalDual
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    coordinateLocalDualQuotientCount L p k
        (localDualPadicCoordinateSubmodule L p k)
        (localDualPadicCoordinateSubmodule_rank (n := n) L p k) =
      coordinateLocalDualQuotientCount L p k
        (pairingMatrixLocalDualCoordinateSubmodule L p k)
        (pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k) := by
  exact coordinateLocalDualQuotientCount_eq_of_submodule_eq L p k
    (localDualPadicCoordinateSubmodule_eq_pairingMatrixLocalDualCoordinateSubmodule
      (n := n) L p k)
    (localDualPadicCoordinateSubmodule_rank (n := n) L p k)
    (pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k)

lemma localDualQuotientCount_eq_localDualPadicCoordinateSubmodule
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    localDualQuotientCount L p k =
      coordinateLocalDualQuotientCount L p k
        (localDualPadicCoordinateSubmodule L p k)
        (localDualPadicCoordinateSubmodule_rank (n := n) L p k) := by
  exact coordinateLocalDualQuotientCount_eq_of_submodule_eq L p k
    (localDualPadicDenominatorIntegralPreimage_eq_localDualPadicCoordinateSubmodule
      (n := n) L p k)
    (localDualPadicDenominatorIntegralPreimage_rank (n := n) L p k)
    (localDualPadicCoordinateSubmodule_rank (n := n) L p k)

lemma localDualQuotientCount_eq_pairingMatrixLocalDual
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    localDualQuotientCount L p k =
      coordinateLocalDualQuotientCount L p k
        (pairingMatrixLocalDualCoordinateSubmodule L p k)
        (pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k) := by
  rw [localDualQuotientCount_eq_localDualPadicCoordinateSubmodule]
  exact coordinateLocalDualQuotientCount_localDualPadicCoordinateSubmodule_eq_pairingMatrixLocalDual
    (n := n) L p k

lemma mem_localDualQuotientSolutionFamilies_iff
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {D : Submodule ℤ (Fin n → ℤ)} {hD_rank : Module.finrank ℤ D = n}
    {Y : Fin n → localDualQuotientTarget D} :
    Y ∈ localDualQuotientSolutionFamilies L p k D hD_rank ↔
      ∀ x y : Fin n → ℤ,
        quotientBasisFamilyMap D Y x = D.mkQ y →
          (L.quadForm y : ZMod (primePowModulus p k : ℕ)) =
            (L.quadForm x : ZMod (primePowModulus p k : ℕ)) := by
  classical
  simp [localDualQuotientSolutionFamilies]

/-- The finite type of canonical local-dual quotient solution families at one
depth. -/
abbrev localDualQuotientSolutionFamily
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :=
  {Y : Fin n → localDualQuotientTarget
      (localDualPadicDenominatorIntegralPreimage L p k) //
    Y ∈ localDualQuotientSolutionFamilies L p k
      (localDualPadicDenominatorIntegralPreimage L p k)
      (localDualPadicDenominatorIntegralPreimage_rank (n := n) L p k)}

/-- The finite type of source-normalized associated-bilinear-dual solution
families at one depth. -/
abbrev associatedBilinearDualQuotientSolutionFamily
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :=
  {Y : Fin n → localDualQuotientTarget
      (associatedBilinearDualPadicDenominatorIntegralPreimage L p k) //
    Y ∈ localDualQuotientSolutionFamilies L p k
      (associatedBilinearDualPadicDenominatorIntegralPreimage L p k)
      (associatedBilinearDualPadicDenominatorIntegralPreimage_rank (n := n) L p k)}

/-- The canonical local-dual quotient count is the cardinality of its
solution-family subtype. -/
lemma localDualQuotientCount_eq_natCard_solutionFamily
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    localDualQuotientCount L p k =
      Nat.card (localDualQuotientSolutionFamily L p k) := by
  unfold localDualQuotientCount coordinateLocalDualQuotientCount
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

lemma associatedBilinearDualQuotientCount_eq_natCard_solutionFamily
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    associatedBilinearDualQuotientCount L p k =
      Nat.card
        (associatedBilinearDualQuotientSolutionFamily L p k) := by
  unfold associatedBilinearDualQuotientCount coordinateLocalDualQuotientCount
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- An integral representative matrix for a source-normalized solution
family. -/
def associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => Quotient.out (Y.1 j) i

lemma
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix_mkQ_mulVec
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (x : Fin n → ℤ) :
    (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).mkQ
        ((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
          L p k Y).mulVec x) =
      quotientBasisFamilyMap
        (associatedBilinearDualPadicDenominatorIntegralPreimage L p k) Y.1 x := by
  classical
  rw [quotientBasisFamilyMap]
  calc
    (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).mkQ
        ((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
          L p k Y).mulVec x) =
        (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).mkQ
          (∑ i, (x i) • Quotient.out (Y.1 i)) := by
            apply congrArg
            ext a
            simp
              [associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix,
                Matrix.mulVec, dotProduct, mul_comm]
    _ = ∑ i, (x i) •
          (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).mkQ
            (Quotient.out (Y.1 i)) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact
            (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).mkQ.map_smul
              (x i) (Quotient.out (Y.1 i))
    _ = ∑ i, (x i) • Y.1 i := by
          apply Finset.sum_congr rfl
          intro i _
          exact congrArg (fun q => (x i) • q)
            (Submodule.Quotient.mk_out (Y.1 i))

lemma
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix_quadForm_zmod
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (x : Fin n → ℤ) :
    (L.quadForm
        ((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
          L p k Y).mulVec x) : ZMod (primePowModulus p k : ℕ)) =
      (L.quadForm x : ZMod (primePowModulus p k : ℕ)) := by
  apply (mem_localDualQuotientSolutionFamilies_iff.mp Y.2) x
  rw [←
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix_mkQ_mulVec]

/-- The source representative matrix modulo the working prime power. -/
def associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZMod
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ)) :=
  (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
    L p k Y).map Int.cast

/-- The source representative matrix reduced modulo the residue prime. -/
def
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    Matrix (Fin n) (Fin n) (ZMod p) :=
  (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
    L p k Y).map Int.cast

lemma localDualQuotientFamilyOfLE_mem_localDualQuotientSolutionFamilies
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {D E : Submodule ℤ (Fin n → ℤ)}
    {hD_rank : Module.finrank ℤ D = n} {hE : IsDualQuotientAdmissible L p k E}
    (hDE : D ≤ E) {Y : Fin n → localDualQuotientTarget D}
    (hY : Y ∈ localDualQuotientSolutionFamilies L p k D hD_rank) :
    localDualQuotientFamilyOfLE (n := n) hDE Y ∈
      localDualQuotientSolutionFamilies L p k E hE.1 := by
  classical
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  let q : localDualQuotientTarget D := quotientBasisFamilyMap D Y x
  let z : Fin n → ℤ := Quotient.out q
  have hq : quotientBasisFamilyMap D Y x = D.mkQ z := by
    change q = D.mkQ z
    exact (Submodule.Quotient.mk_out q).symm
  have hmap :
      quotientBasisFamilyMap E (localDualQuotientFamilyOfLE (n := n) hDE Y) x =
        E.mkQ z := by
    rw [quotientBasisFamilyMap_ofLE (n := n) hDE Y x, hq]
    exact localDualQuotientMapOfLE_mkQ (n := n) hDE z
  have hzy : E.mkQ z = E.mkQ y := hmap.symm.trans hxy
  have hyz :
      (L.quadForm y : ZMod (primePowModulus p k : ℕ)) =
        (L.quadForm z : ZMod (primePowModulus p k : ℕ)) := by
    have hyz_mem : y - z ∈ E := by
      have hzy' : E.mkQ y = E.mkQ z := hzy.symm
      change (Submodule.Quotient.mk y : (Fin n → ℤ) ⧸ E) =
        Submodule.Quotient.mk z at hzy'
      rw [Submodule.Quotient.eq] at hzy'
      exact hzy'
    exact hE.2 hyz_mem
  have hzx :
      (L.quadForm z : ZMod (primePowModulus p k : ℕ)) =
        (L.quadForm x : ZMod (primePowModulus p k : ℕ)) := by
    exact (mem_localDualQuotientSolutionFamilies_iff.mp hY) x z hq
  exact hyz.trans hzx

/-- Reduce a canonical solution family from depth `k+1` to depth `k`. The
underlying quotient-family map is induced by the inclusion
`p^(k+1) L_p# ∩ L ≤ p^k L_p# ∩ L`; validity follows by reducing the quadratic
congruence modulo `p^k`. -/
noncomputable def localDualQuotientSolutionFamilySuccReduction
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    localDualQuotientSolutionFamily L p (k + 1) →
      localDualQuotientSolutionFamily L p k := by
  intro Y
  let hDE := localDualPadicDenominatorIntegralPreimage_succ_le L p k
  refine ⟨localDualQuotientFamilyOfLE (n := n) hDE Y.1, ?_⟩
  apply localDualQuotientFamilyOfLE_mem_localDualQuotientSolutionFamilies
    (hD_rank :=
      localDualPadicDenominatorIntegralPreimage_rank (n := n) L p (k + 1))
    (hE := localDualPadicDenominatorIntegralPreimage_admissible (n := n) L p k)
    hDE
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  exact quadForm_zmod_eq_of_succ L p k
    ((mem_localDualQuotientSolutionFamilies_iff.mp Y.2) x y hxy)

@[simp] lemma localDualQuotientSolutionFamilySuccReduction_coe
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : localDualQuotientSolutionFamily L p (k + 1)) :
    (localDualQuotientSolutionFamilySuccReduction L p k Y).1 =
      localDualQuotientFamilyOfLE (n := n)
        (localDualPadicDenominatorIntegralPreimage_succ_le L p k) Y.1 := rfl

/-! ### Linear algebra of the adjacent Hensel correction -/

section HenselCorrectionLinearization

variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]


/-- Once the correction space is identified with the dual of the source, a
linear correction `h` contributes the bilinear form `(x,y) ↦ e(h x)(y)`.
This is the linear map underlying the quadratic defect in the quantitative
Hensel argument. -/
def henselCorrectionBilinearMap
    (e : W ≃ₗ[R] Module.Dual R V) :
    (V →ₗ[R] W) →ₗ[R] LinearMap.BilinForm R V where
  toFun h :=
    { toFun := fun x => e (h x)
      map_add' := fun x y => by simp
      map_smul' := fun a x => by simp }
  map_add' h₁ h₂ := by
    ext x y
    simp
  map_smul' a h := by
    ext x y
    simp

/-- The quadratic defect contributed by a correction map.  Negating this map
gives the convention `h ↦ -b(f(-),h(-))` used in Schulze--Pillot's proof. -/
def henselCorrectionQuadraticMap
    (e : W ≃ₗ[R] Module.Dual R V) :
    (V →ₗ[R] W) →ₗ[R] QuadraticForm R V :=
  (LinearMap.BilinMap.toQuadraticMapLinearMap R R V).comp
    (henselCorrectionBilinearMap e)

@[simp] lemma henselCorrectionQuadraticMap_apply
    (e : W ≃ₗ[R] Module.Dual R V) (h : V →ₗ[R] W) (x : V) :
    henselCorrectionQuadraticMap e h x = e (h x) x := rfl

/-- The correction-to-quadratic-defect map is surjective whenever the target
correction space pairs perfectly with the source.  The proof is valid in
characteristic two: it uses Mathlib's basis-dependent bilinear presentation
of an arbitrary quadratic form rather than polarization by `1 / 2`. -/
lemma henselCorrectionQuadraticMap_surjective
    [Module.Free R V] (e : W ≃ₗ[R] Module.Dual R V) :
    Function.Surjective (henselCorrectionQuadraticMap e) := by
  intro Q
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective Q
  let h : V →ₗ[R] W := e.symm.toLinearMap.comp B
  refine ⟨h, ?_⟩
  rw [← hB]
  apply congrArg LinearMap.BilinMap.toQuadraticMap
  ext x y
  simp [henselCorrectionBilinearMap, h]

end HenselCorrectionLinearization

section HenselMatrixCorrectionLinearization

variable {K : Type*} [Field K]


/-- Coordinate form of `henselCorrectionQuadraticMap`.  For an invertible
pairing matrix `A`, a correction matrix `H` contributes the quadratic form
obtained from the endomorphism `H` and the perfect pairing represented by
`A`. -/
def henselMatrixCorrectionQuadraticMap
    (A : Matrix (Fin n) (Fin n) K) [Invertible A] :
    Matrix (Fin n) (Fin n) K →ₗ[K] QuadraticForm K (Fin n → K) :=
  (henselCorrectionQuadraticMap
    ((Matrix.toLinearEquiv' A inferInstance).trans
      (Pi.basisFun K (Fin n)).toDualEquiv)).comp
    (Matrix.toLin' :
      Matrix (Fin n) (Fin n) K ≃ₗ[K]
        (Fin n → K) →ₗ[K] (Fin n → K)).toLinearMap

lemma basisFun_toDual_eq_dotProduct
    (v x : Fin n → K) :
    (Pi.basisFun K (Fin n)).toDual v x = dotProduct v x := by
  conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]
  rw [map_sum, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, Module.Basis.toDual_apply_left, Pi.basisFun_repr]
  simp only [smul_eq_mul]
  rw [Pi.basisFun_repr]
  ring

lemma henselMatrixCorrectionQuadraticMap_apply_eq_dotProduct
    (A H : Matrix (Fin n) (Fin n) K) [Invertible A]
    (x : Fin n → K) :
    henselMatrixCorrectionQuadraticMap A H x =
      dotProduct (A.mulVec (H.mulVec x)) x := by
  simp [henselMatrixCorrectionQuadraticMap,
    henselCorrectionQuadraticMap_apply, basisFun_toDual_eq_dotProduct]
  change (Matrix.toLin' A) (H.mulVec x) ⬝ᵥ x = _
  rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec]

lemma dotProduct_transpose_mulVec
    (A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    dotProduct (Aᵀ.mulVec y) x = dotProduct (A.mulVec x) y := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The coordinate correction-to-quadratic-defect map is surjective for every
invertible pairing matrix, including over residue fields of characteristic
two. -/
lemma henselMatrixCorrectionQuadraticMap_surjective
    (A : Matrix (Fin n) (Fin n) K) [Invertible A] :
    Function.Surjective (henselMatrixCorrectionQuadraticMap A) := by
  simpa [henselMatrixCorrectionQuadraticMap] using
    (henselCorrectionQuadraticMap_surjective
      ((Matrix.toLinearEquiv' A inferInstance).trans
        (Pi.basisFun K (Fin n)).toDualEquiv)).comp
      (Matrix.toLin' :
        Matrix (Fin n) (Fin n) K ≃ₗ[K]
          (Fin n → K) →ₗ[K] (Fin n → K)).surjective

end HenselMatrixCorrectionLinearization

section QuadraticFormSym2

variable {K : Type*} [CommRing K]


/-! ### Cardinality of the adjacent Hensel defect fibers -/

/-- Symmetrize the upper triangle of a matrix as a function on unordered
pairs. This is the coordinate target for a quadratic form in arbitrary
characteristic. -/
def upperMatrixToSym2LinearMap :
    Matrix (Fin n) (Fin n) K →ₗ[K] (Sym2 (Fin n) → K) where
  toFun A := Sym2.lift ⟨fun i j => if i ≤ j then A i j else A j i, by
    intro i j
    rcases le_total i j with hij | hji
    · by_cases hji' : j ≤ i
      · have h : i = j := le_antisymm hij hji'
        subst j
        simp
      · simp [hij, hji']
    · by_cases hij' : i ≤ j
      · have h : i = j := le_antisymm hij' hji
        subst j
        simp
      · simp [hji, hij']
    ⟩
  map_add' A B := by
    ext z
    induction z using Sym2.ind with
    | _ i j =>
        simp only [Sym2.lift_mk, Pi.add_apply]
        split <;> rfl
  map_smul' a A := by
    ext z
    induction z using Sym2.ind with
    | _ i j => simp [Sym2.lift_mk]

/-- Put unordered-pair coordinates into the upper triangle of a matrix. -/
def sym2ToUpperMatrixLinearMap :
    (Sym2 (Fin n) → K) →ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun c i j := if i ≤ j then c s(i, j) else 0
  map_add' c d := by
    ext i j
    by_cases hij : i ≤ j <;> simp [hij]
  map_smul' a c := by
    ext i j
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split <;> simp_all

lemma sym2ToUpperMatrix_upperMatrixToSym2_of_upper
    (A : Matrix (Fin n) (Fin n) K)
    (hA : ∀ i j, j < i → A i j = 0) :
    sym2ToUpperMatrixLinearMap (K := K)
        (upperMatrixToSym2LinearMap (K := K) A) = A := by
  ext i j
  by_cases hij : i ≤ j
  · simp [sym2ToUpperMatrixLinearMap, upperMatrixToSym2LinearMap, hij,
      Sym2.lift_mk]
  · simp [sym2ToUpperMatrixLinearMap, hij, hA i j (lt_of_not_ge hij)]

lemma upperMatrixToSym2_sym2ToUpperMatrix
    (c : Sym2 (Fin n) → K) :
    upperMatrixToSym2LinearMap (K := K)
        (sym2ToUpperMatrixLinearMap (K := K) c) = c := by
  ext z
  induction z using Sym2.ind with
  | _ i j =>
      rcases le_total i j with hij | hji
      · simp [upperMatrixToSym2LinearMap, sym2ToUpperMatrixLinearMap,
          Sym2.lift_mk, hij]
      · by_cases hij : i ≤ j
        · simp [upperMatrixToSym2LinearMap, sym2ToUpperMatrixLinearMap,
            Sym2.lift_mk, hij]
        · have hs : s(j, i) = s(i, j) := Sym2.eq_swap
          simp [upperMatrixToSym2LinearMap, sym2ToUpperMatrixLinearMap,
            Sym2.lift_mk, hij, hji, hs]

/-- Record a quadratic form by the upper-triangular bilinear representative
provided by the standard coordinate basis. -/
def quadraticFormToSym2LinearMap :
    QuadraticForm K (Fin n → K) →ₗ[K] (Sym2 (Fin n) → K) :=
  (upperMatrixToSym2LinearMap (K := K)).comp
    ((LinearMap.BilinForm.toMatrix').toLinearMap.comp
      (QuadraticMap.toBilinHom K (Pi.basisFun K (Fin n))))

/-- Build a quadratic form from its unordered-pair coordinates using the
corresponding upper-triangular bilinear form. -/
def sym2ToQuadraticFormLinearMap :
    (Sym2 (Fin n) → K) →ₗ[K] QuadraticForm K (Fin n → K) :=
  (LinearMap.BilinMap.toQuadraticMapLinearMap K K (Fin n → K)).comp
    ((LinearMap.BilinForm.toMatrix').symm.toLinearMap.comp
      (sym2ToUpperMatrixLinearMap (K := K)))

lemma sym2ToQuadraticFormLinearMap_apply_eq_dotProduct
    (c : Sym2 (Fin n) → K) (x : Fin n → K) :
    sym2ToQuadraticFormLinearMap c x =
      dotProduct x ((sym2ToUpperMatrixLinearMap c).mulVec x) := by
  simp [sym2ToQuadraticFormLinearMap,
    LinearMap.BilinMap.toQuadraticMapLinearMap,
    LinearMap.BilinMap.toQuadraticMap_apply]
  change (((Matrix.toLinearMap₂' K) (sym2ToUpperMatrixLinearMap c)) x) x = _
  rw [Matrix.toLinearMap₂'_apply']

lemma quadraticFormToSym2LinearMap_mk
    (Q : QuadraticForm K (Fin n → K)) (i j : Fin n) :
    quadraticFormToSym2LinearMap Q s(i, j) =
      if i = j then Q ((Pi.basisFun K (Fin n)) i)
      else Q ((Pi.basisFun K (Fin n)) i + (Pi.basisFun K (Fin n)) j) -
        Q ((Pi.basisFun K (Fin n)) i) -
        Q ((Pi.basisFun K (Fin n)) j) := by
  change upperMatrixToSym2LinearMap
      (LinearMap.BilinForm.toMatrix'
        (Q.toBilin (Pi.basisFun K (Fin n)))) s(i, j) = _
  change (if i ≤ j then
      LinearMap.BilinForm.toMatrix'
        (Q.toBilin (Pi.basisFun K (Fin n))) i j
    else LinearMap.BilinForm.toMatrix'
        (Q.toBilin (Pi.basisFun K (Fin n))) j i) = _
  rw [LinearMap.BilinForm.toMatrix'_apply,
    LinearMap.BilinForm.toMatrix'_apply,
    ← Pi.basisFun_apply, ← Pi.basisFun_apply]
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [if_pos hij.le, if_neg hij.ne]
    rw [QuadraticMap.toBilin_apply, if_neg hij.ne, if_pos hij]
    rfl
  · rw [QuadraticMap.toBilin_apply]
    simp
  · rw [if_neg (not_le_of_gt hji), if_neg hji.ne']
    rw [QuadraticMap.toBilin_apply, if_neg hji.ne, if_pos hji]
    simp [QuadraticMap.polar]
    ring_nf

lemma toBilin_toQuadraticMap_of_upper
    (B : LinearMap.BilinForm K (Fin n → K))
    (hB : ∀ i j, j < i →
      B ((Pi.basisFun K (Fin n)) i) ((Pi.basisFun K (Fin n)) j) = 0) :
    B.toQuadraticMap.toBilin (Pi.basisFun K (Fin n)) = B := by
  apply (Pi.basisFun K (Fin n)).ext
  intro i
  apply (Pi.basisFun K (Fin n)).ext
  intro j
  rw [QuadraticMap.toBilin_apply]
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [if_neg hij.ne, if_pos hij,
      LinearMap.BilinMap.polar_toQuadraticMap, hB j i hij, add_zero]
  · simp [LinearMap.BilinMap.toQuadraticMap_apply]
  · rw [if_neg hji.ne', if_neg hji.not_gt, hB i j hji]

lemma quadraticFormToSym2LinearMap_comp_sym2ToQuadraticFormLinearMap :
    (quadraticFormToSym2LinearMap (n := n) (K := K)).comp
        (sym2ToQuadraticFormLinearMap (n := n) (K := K)) = LinearMap.id := by
  apply LinearMap.ext
  intro c
  funext z
  induction z using Sym2.ind with
  | _ i j =>
      change upperMatrixToSym2LinearMap (K := K)
        (LinearMap.BilinForm.toMatrix'
          (((LinearMap.BilinForm.toMatrix').symm
            (sym2ToUpperMatrixLinearMap (K := K) c)).toQuadraticMap.toBilin
              (Pi.basisFun K (Fin n)))) s(i, j) = c s(i, j)
      rw [toBilin_toQuadraticMap_of_upper]
      · rw [LinearEquiv.apply_symm_apply,
          upperMatrixToSym2_sym2ToUpperMatrix]
      · intro a b hba
        rw [Pi.basisFun_apply, Pi.basisFun_apply]
        rw [← LinearMap.BilinForm.toMatrix'_apply]
        rw [LinearEquiv.apply_symm_apply]
        simp [sym2ToUpperMatrixLinearMap, not_le_of_gt hba]

lemma sym2ToQuadraticFormLinearMap_comp_quadraticFormToSym2LinearMap :
    (sym2ToQuadraticFormLinearMap (n := n) (K := K)).comp
        (quadraticFormToSym2LinearMap (n := n) (K := K)) = LinearMap.id := by
  apply LinearMap.ext
  intro Q
  change ((LinearMap.BilinForm.toMatrix').symm
      (sym2ToUpperMatrixLinearMap (K := K)
        (upperMatrixToSym2LinearMap (K := K)
          (LinearMap.BilinForm.toMatrix'
            (Q.toBilin (Pi.basisFun K (Fin n))))))).toQuadraticMap = Q
  rw [sym2ToUpperMatrix_upperMatrixToSym2_of_upper]
  · simp only [LinearEquiv.symm_apply_apply]
    exact QuadraticMap.toQuadraticMap_toBilin Q (Pi.basisFun K (Fin n))
  · intro i j hji
    rw [LinearMap.BilinForm.toMatrix'_apply]
    rw [← Pi.basisFun_apply K (Fin n) i,
      ← Pi.basisFun_apply K (Fin n) j]
    rw [QuadraticMap.toBilin_apply]
    simp [hji.ne', hji.not_gt]

/-- Quadratic forms on `K^n` have one free coordinate for each unordered pair,
including the diagonal. This avoids any division by two. -/
noncomputable def quadraticFormEquivSym2 :
    QuadraticForm K (Fin n → K) ≃ₗ[K] (Sym2 (Fin n) → K) :=
  LinearEquiv.ofLinear
    (quadraticFormToSym2LinearMap (n := n) (K := K))
    (sym2ToQuadraticFormLinearMap (n := n) (K := K))
    quadraticFormToSym2LinearMap_comp_sym2ToQuadraticFormLinearMap
    sym2ToQuadraticFormLinearMap_comp_quadraticFormToSym2LinearMap

end QuadraticFormSym2


/-- Coordinatewise reduction modulo a prime commutes with evaluating the
division-free `Sym2` presentation of a quadratic form. -/
lemma intCast_sym2ToQuadraticFormLinearMap_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (c : Sym2 (Fin n) → ℤ) (x : Fin n → ℤ) :
    ((sym2ToQuadraticFormLinearMap c x : ℤ) : ZMod p) =
      sym2ToQuadraticFormLinearMap (fun z => (c z : ZMod p))
        (fun i => (x i : ZMod p)) := by
  rw [sym2ToQuadraticFormLinearMap_apply_eq_dotProduct,
    sym2ToQuadraticFormLinearMap_apply_eq_dotProduct]
  simp only [dotProduct, Matrix.mulVec, sym2ToUpperMatrixLinearMap]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change ((if i ≤ j then c s(i, j) else 0 : ℤ) : ZMod p) * (x j : ZMod p) =
    (if i ≤ j then (c s(i, j) : ZMod p) else 0) * (x j : ZMod p)
  split <;> simp

section HenselMatrixCorrectionLinearization

variable {K : Type*} [Field K]


lemma finrank_quadraticForm_fin_fun :
    Module.finrank K (QuadraticForm K (Fin n → K)) = (n + 1).choose 2 := by
  rw [(quadraticFormEquivSym2 (n := n) (K := K)).finrank_eq]
  simp [Module.finrank_fintype_fun_eq_card, Sym2.card]

lemma choose_two_add_choose_succ_two (n : ℕ) :
    n.choose 2 + (n + 1).choose 2 = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        Nat.choose_succ_succ, Nat.choose_succ_succ,
        Nat.choose_one_right, Nat.choose_one_right]
      change n + n.choose 2 + (n + 1 + (n + 1).choose 2) = _
      rw [show n + n.choose 2 + (n + 1 + (n + 1).choose 2) =
        (n.choose 2 + (n + 1).choose 2) + (n + (n + 1)) by omega, ih]
      ring

/-- The kernel of the surjective correction-to-defect map has the expected
alternating-triangular dimension. -/
lemma finrank_ker_henselMatrixCorrectionQuadraticMap
    (A : Matrix (Fin n) (Fin n) K) [Invertible A] :
    Module.finrank K (LinearMap.ker (henselMatrixCorrectionQuadraticMap A)) =
      n.choose 2 := by
  let f := henselMatrixCorrectionQuadraticMap A
  have hrange : f.range = ⊤ :=
    LinearMap.range_eq_top.mpr (henselMatrixCorrectionQuadraticMap_surjective A)
  have hdim := f.finrank_range_add_finrank_ker
  dsimp [f] at hdim
  rw [hrange] at hdim
  have htarget : Module.finrank K (QuadraticForm K (Fin n → K)) =
      (n + 1).choose 2 := finrank_quadraticForm_fin_fun
  have hdomain : Module.finrank K (Matrix (Fin n) (Fin n) K) = n * n := by
    change Module.finrank K (Fin n → Fin n → K) = _
    rw [Module.finrank_pi_fintype]
    simp
  rw [finrank_top] at hdim
  rw [htarget, hdomain] at hdim
  have hchoose := choose_two_add_choose_succ_two n
  omega

lemma natCard_ker_henselMatrixCorrectionQuadraticMap_zmod
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : Matrix (Fin n) (Fin n) (ZMod p)) [Invertible A] :
    Nat.card (LinearMap.ker (henselMatrixCorrectionQuadraticMap A)) =
      p ^ (n * (n - 1) / 2) := by
  letI : Fintype (ZMod p) := Fintype.ofFinite (ZMod p)
  letI : Fintype (LinearMap.ker
      (henselMatrixCorrectionQuadraticMap A)) :=
    Fintype.ofFinite (LinearMap.ker
      (henselMatrixCorrectionQuadraticMap A))
  rw [Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod p)
      (V := LinearMap.ker (henselMatrixCorrectionQuadraticMap A)),
    finrank_ker_henselMatrixCorrectionQuadraticMap, Nat.choose_two_right]
  simp

/-- Translation by one chosen preimage identifies the kernel of a surjective
linear map with every affine fiber. -/
noncomputable def linearMapKerEquivFiberOfSurjective
    {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) (w : W) :
    LinearMap.ker f ≃ {v : V // f v = w} := by
  let v₀ : V := Classical.choose (hf w)
  have hv₀ : f v₀ = w := Classical.choose_spec (hf w)
  exact
    { toFun := fun z => ⟨v₀ + z.1, by simp [hv₀, LinearMap.mem_ker.mp z.2]⟩
      invFun := fun v => ⟨v.1 - v₀, by
        rw [LinearMap.mem_ker, map_sub, v.2, hv₀, sub_self]⟩
      left_inv := by
        intro z
        apply Subtype.ext
        simp
      right_inv := by
        intro v
        apply Subtype.ext
        simp }

/-- Every affine fiber of the residue correction-to-defect map has exactly
`p^(n(n-1)/2)` elements. -/
lemma natCard_henselMatrixCorrectionQuadraticMap_fiber_zmod
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : Matrix (Fin n) (Fin n) (ZMod p)) [Invertible A]
    (Q : QuadraticForm (ZMod p) (Fin n → ZMod p)) :
    Nat.card {H : Matrix (Fin n) (Fin n) (ZMod p) //
        henselMatrixCorrectionQuadraticMap A H = Q} =
      p ^ (n * (n - 1) / 2) := by
  rw [← Nat.card_congr
    (linearMapKerEquivFiberOfSurjective
      (henselMatrixCorrectionQuadraticMap A)
      (henselMatrixCorrectionQuadraticMap_surjective A) Q)]
  exact natCard_ker_henselMatrixCorrectionQuadraticMap_zmod p A

end HenselMatrixCorrectionLinearization


/-! ### The source raw defect modulo the adjacent prime -/

/-- The integral source raw defect as a quadratic form, before dividing by
the working prime power. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilyRawDefectIntegralQuadraticForm
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    QuadraticForm ℤ (Fin n → ℤ) :=
  L.quadraticForm.comp
      (Matrix.toLin'
        (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
          L p k Y)) -
    L.quadraticForm

/-- The integral quadratic defect of a source depth-`k` representative
matrix. -/
def associatedBilinearDualQuotientSolutionFamilyRawDefect
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (x : Fin n → ℤ) : ℤ :=
  L.quadForm
      ((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
        L p k Y).mulVec x) -
    L.quadForm x

@[simp] lemma
    associatedBilinearDualQuotientSolutionFamilyRawDefectIntegralQuadraticForm_apply
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (x : Fin n → ℤ) :
    associatedBilinearDualQuotientSolutionFamilyRawDefectIntegralQuadraticForm
        L p k Y x =
      associatedBilinearDualQuotientSolutionFamilyRawDefect
        L p k Y x := rfl

/-- The source solution congruence says that every integral raw defect is
divisible by `p^k`. -/
lemma primePow_dvd_associatedBilinearDualQuotientSolutionFamilyRawDefect
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (x : Fin n → ℤ) :
    (p ^ k : ℤ) ∣
      associatedBilinearDualQuotientSolutionFamilyRawDefect
        L p k Y x := by
  have h :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix_quadForm_zmod
      L p k Y x
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  rcases h with ⟨c, hc⟩
  refine ⟨-c, ?_⟩
  dsimp
    [associatedBilinearDualQuotientSolutionFamilyRawDefect,
      primePowModulus] at hc ⊢
  calc
    L.quadForm
          ((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
            L p k Y).mulVec x) - L.quadForm x =
        -(L.quadForm x -
          L.quadForm
            ((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
              L p k Y).mulVec x)) := by ring
    _ = -((p : ℤ) ^ k * c) := by rw [hc]
    _ = (p : ℤ) ^ k * -c := by ring

/-- Unordered-pair numerator for the raw defect: diagonal entries record the
defect on a basis vector, while off-diagonal entries record its polarization.
-/
def associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (i j : Fin n) : ℤ :=
  if i = j then
    associatedBilinearDualQuotientSolutionFamilyRawDefect
      L p k Y ((Pi.basisFun ℤ (Fin n)) i)
  else
    associatedBilinearDualQuotientSolutionFamilyRawDefect
        L p k Y
        ((Pi.basisFun ℤ (Fin n)) i + (Pi.basisFun ℤ (Fin n)) j) -
      associatedBilinearDualQuotientSolutionFamilyRawDefect
        L p k Y ((Pi.basisFun ℤ (Fin n)) i) -
      associatedBilinearDualQuotientSolutionFamilyRawDefect
        L p k Y ((Pi.basisFun ℤ (Fin n)) j)

lemma
    associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator_comm
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (i j : Fin n) :
    associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator
        L p k Y i j =
      associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator
        L p k Y j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp only
      [associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator,
        if_neg hij, if_neg hji]
    rw [add_comm]
    ring

lemma
    primePow_dvd_associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (i j : Fin n) :
    (p ^ k : ℤ) ∣
      associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator
        L p k Y i j := by
  by_cases hij : i = j
  · simp only
      [associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator,
        if_pos hij]
    exact
      primePow_dvd_associatedBilinearDualQuotientSolutionFamilyRawDefect
        L p k Y _
  · simp only
      [associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator,
        if_neg hij]
    exact
      ((primePow_dvd_associatedBilinearDualQuotientSolutionFamilyRawDefect
          L p k Y _).sub
        (primePow_dvd_associatedBilinearDualQuotientSolutionFamilyRawDefect
          L p k Y _)).sub
        (primePow_dvd_associatedBilinearDualQuotientSolutionFamilyRawDefect
          L p k Y _)

/-- Divide the unordered-pair raw defect by its guaranteed factor `p^k`. -/
def associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (i j : Fin n) : ℤ :=
  associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator
      L p k Y i j / (p ^ k : ℤ)

lemma
    primePow_mul_associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (i j : Fin n) :
    (p ^ k : ℤ) *
        associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient
          L p k Y i j =
      associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator
        L p k Y i j := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel
    (primePow_dvd_associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator
      L p k Y i j)

lemma
    associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient_comm
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (i j : Fin n) :
    associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient
        L p k Y i j =
      associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient
        L p k Y j i := by
  unfold
    associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient
  rw [
    associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator_comm]

/-- The exactly divided raw-defect coordinates before reduction modulo `p`. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotientSym2Int
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    Sym2 (Fin n) → ℤ :=
  Sym2.lift ⟨fun i j =>
    associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient
      L p k Y i j, by
    intro i j
    exact
      associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient_comm
        L p k Y i j⟩

@[simp] lemma
    associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotientSym2Int_mk
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (i j : Fin n) :
    associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotientSym2Int
        L p k Y s(i, j) =
      associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient
        L p k Y i j := rfl

/-- Exact coordinatewise division assembles into an integral quadratic form. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilyRawDefectQuotientIntegralQuadraticForm
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    QuadraticForm ℤ (Fin n → ℤ) :=
  sym2ToQuadraticFormLinearMap
    (associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotientSym2Int
      L p k Y)

/-- The raw adjacent defect in unordered-pair residue coordinates. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilyRawDefectSym2
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    Sym2 (Fin n) → ZMod p :=
  fun z =>
    (associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotientSym2Int
      L p k Y z : ZMod p)

@[simp] lemma
    associatedBilinearDualQuotientSolutionFamilyRawDefectSym2_mk
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (i j : Fin n) :
    associatedBilinearDualQuotientSolutionFamilyRawDefectSym2
        L p k Y s(i, j) =
      (associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient
        L p k Y i j : ZMod p) := rfl

/-- The divided source raw defect as a genuine quadratic form over the
residue field. Its coordinates are defined by exact integral division, so no
choice of residue-vector lifts enters the construction. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    QuadraticForm (ZMod p) (Fin n → ZMod p) :=
  sym2ToQuadraticFormLinearMap
    (associatedBilinearDualQuotientSolutionFamilyRawDefectSym2
      L p k Y)

lemma
    quadraticFormToSym2_associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    quadraticFormToSym2LinearMap
        (associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm
          L p k Y) =
      associatedBilinearDualQuotientSolutionFamilyRawDefectSym2
        L p k Y := by
  change
    ((quadraticFormToSym2LinearMap (n := n) (K := ZMod p)).comp
      (sym2ToQuadraticFormLinearMap (n := n) (K := ZMod p))) _ = _
  rw [quadraticFormToSym2LinearMap_comp_sym2ToQuadraticFormLinearMap]
  rfl

@[simp] lemma
    quadraticFormToSym2_associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm_mk
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (i j : Fin n) :
    quadraticFormToSym2LinearMap
        (associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm
          L p k Y) s(i, j) =
      (associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient
        L p k Y i j : ZMod p) := by
  rw [
    quadraticFormToSym2_associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm]
  rfl

@[simp] lemma
    quadraticFormToSym2_associatedBilinearDualQuotientSolutionFamilyRawDefectIntegralQuadraticForm_mk
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (i j : Fin n) :
    quadraticFormToSym2LinearMap
        (associatedBilinearDualQuotientSolutionFamilyRawDefectIntegralQuadraticForm
          L p k Y) s(i, j) =
      associatedBilinearDualQuotientSolutionFamilyRawDefectPairNumerator
        L p k Y i j := by
  rw [quadraticFormToSym2LinearMap_mk]
  rfl

lemma
    quadraticFormToSym2_associatedBilinearDualQuotientSolutionFamilyRawDefectQuotientIntegralQuadraticForm
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    quadraticFormToSym2LinearMap
        (associatedBilinearDualQuotientSolutionFamilyRawDefectQuotientIntegralQuadraticForm
          L p k Y) =
      associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotientSym2Int
        L p k Y := by
  change ((quadraticFormToSym2LinearMap (n := n) (K := ℤ)).comp
    (sym2ToQuadraticFormLinearMap (n := n) (K := ℤ))) _ = _
  rw [quadraticFormToSym2LinearMap_comp_sym2ToQuadraticFormLinearMap]
  rfl

/-- Exact coordinatewise division recovers the integral raw defect after
scaling by the guaranteed factor `p^k`. -/
lemma
    primePow_smul_associatedBilinearDualQuotientSolutionFamilyRawDefectQuotientIntegralQuadraticForm
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    ((p : ℤ) ^ k) •
        associatedBilinearDualQuotientSolutionFamilyRawDefectQuotientIntegralQuadraticForm
          L p k Y =
      associatedBilinearDualQuotientSolutionFamilyRawDefectIntegralQuadraticForm
        L p k Y := by
  apply (quadraticFormEquivSym2 (n := n) (K := ℤ)).injective
  ext z
  induction z using Sym2.ind with
  | _ i j =>
      change quadraticFormToSym2LinearMap
          ((p : ℤ) ^ k •
            associatedBilinearDualQuotientSolutionFamilyRawDefectQuotientIntegralQuadraticForm
              L p k Y) s(i, j) =
        quadraticFormToSym2LinearMap
          (associatedBilinearDualQuotientSolutionFamilyRawDefectIntegralQuadraticForm
            L p k Y) s(i, j)
      rw [map_smul,
        quadraticFormToSym2_associatedBilinearDualQuotientSolutionFamilyRawDefectQuotientIntegralQuadraticForm]
      change (p : ℤ) ^ k *
          associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient
            L p k Y i j = _
      rw [quadraticFormToSym2LinearMap_mk]
      exact
        primePow_mul_associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotient
          L p k Y i j

lemma
    associatedBilinearDualQuotientSolutionFamilyRawDefectQuotientIntegralQuadraticForm_apply
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (x : Fin n → ℤ) :
    associatedBilinearDualQuotientSolutionFamilyRawDefectQuotientIntegralQuadraticForm
        L p k Y x =
      associatedBilinearDualQuotientSolutionFamilyRawDefect
          L p k Y x / (p : ℤ) ^ k := by
  apply Eq.symm
  apply Int.ediv_eq_of_eq_mul_left
  · exact pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  · have h := congrArg (fun Q : QuadraticForm ℤ (Fin n → ℤ) => Q x)
        (primePow_smul_associatedBilinearDualQuotientSolutionFamilyRawDefectQuotientIntegralQuadraticForm
          L p k Y)
    change (p : ℤ) ^ k * _ = _ at h
    calc
      associatedBilinearDualQuotientSolutionFamilyRawDefect
          L p k Y x =
          associatedBilinearDualQuotientSolutionFamilyRawDefectIntegralQuadraticForm
            L p k Y x := rfl
      _ = (p : ℤ) ^ k *
          associatedBilinearDualQuotientSolutionFamilyRawDefectQuotientIntegralQuadraticForm
            L p k Y x := h.symm
      _ = _ := by ring

/-- The packaged residue quadratic form evaluates to the exactly divided
integral raw defect on every integral residue vector. -/
lemma
    associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm_apply_intCast
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (x : Fin n → ℤ) :
    associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm
        L p k Y (fun i => (x i : ZMod p)) =
      ((associatedBilinearDualQuotientSolutionFamilyRawDefect
          L p k Y x / (p : ℤ) ^ k : ℤ) : ZMod p) := by
  rw [←
    associatedBilinearDualQuotientSolutionFamilyRawDefectQuotientIntegralQuadraticForm_apply
      L p k Y x]
  exact (intCast_sym2ToQuadraticFormLinearMap_apply p
    (associatedBilinearDualQuotientSolutionFamilyRawDefectPairQuotientSym2Int
      L p k Y) x).symm

/-! ### Source-normalized adjacent Hensel fibers -/

/-- Reduce a source associated-bilinear solution family from depth `k+1` to
depth `k`. The source quadratic-depth hypothesis supplies admissibility of the
target quotient. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilySuccReduction
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k) :
    associatedBilinearDualQuotientSolutionFamily L p (k + 1) →
      associatedBilinearDualQuotientSolutionFamily L p k := by
  intro Y
  let hDE :=
    associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le L p k
  refine ⟨localDualQuotientFamilyOfLE (n := n) hDE Y.1, ?_⟩
  apply localDualQuotientFamilyOfLE_mem_localDualQuotientSolutionFamilies
    (hD_rank :=
      associatedBilinearDualPadicDenominatorIntegralPreimage_rank
        (n := n) L p (k + 1))
    (hE :=
      associatedBilinearDualPadicDenominatorIntegralPreimage_admissible
        L p k hk)
    hDE
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  exact quadForm_zmod_eq_of_succ L p k
    ((mem_localDualQuotientSolutionFamilies_iff.mp Y.2) x y hxy)

@[simp] lemma
    associatedBilinearDualQuotientSolutionFamilySuccReduction_coe
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p (k + 1)) :
    (associatedBilinearDualQuotientSolutionFamilySuccReduction
      L p k hk Y).1 =
      localDualQuotientFamilyOfLE (n := n)
        (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
          L p k) Y.1 := rfl

/-- A canonical raw lift of a source-normalized depth-`k` family to the
depth-`k+1` source quotient. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilySuccRawLift
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    Fin n → localDualQuotientTarget
      (associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + 1)) :=
  fun i =>
    (associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + 1)).mkQ
      (Quotient.out (Y.1 i))

lemma
    associatedBilinearDualQuotientSolutionFamilySuccRawLift_reduces
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    localDualQuotientFamilyOfLE (n := n)
        (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
          L p k)
        (associatedBilinearDualQuotientSolutionFamilySuccRawLift
          L p k Y) = Y.1 := by
  ext i
  exact Submodule.Quotient.mk_out (Y.1 i)

/-- Columnwise corrections to a source-normalized adjacent raw lift. -/
abbrev associatedBilinearDualQuotientSolutionFamilySuccCorrection
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :=
  Fin n → LinearMap.ker
    (localDualQuotientMapOfLE (n := n)
      (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
        L p k))

/-- Integral column representatives of a source adjacent correction family. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => Quotient.out (H j).1 i

lemma
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix_col_mem
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (j : Fin n) :
    (fun i =>
      associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
        L p k H i j) ∈
        associatedBilinearDualPadicDenominatorIntegralPreimage L p k := by
  let Dsucc :=
    associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + 1)
  let D := associatedBilinearDualPadicDenominatorIntegralPreimage L p k
  rw [← Submodule.Quotient.mk_eq_zero D]
  calc
    D.mkQ
        (fun i =>
          associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
            L p k H i j) =
        localDualQuotientMapOfLE (n := n)
          (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
            L p k)
          (Dsucc.mkQ (Quotient.out (H j).1)) := by
      rfl
    _ = localDualQuotientMapOfLE (n := n)
          (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
            L p k) (H j).1 := by
      exact congrArg
        (localDualQuotientMapOfLE (n := n)
          (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
            L p k))
        (Submodule.Quotient.mk_out (H j).1)
    _ = 0 := LinearMap.mem_ker.mp (H j).2

/-- A source correction column, viewed in the depth-`k` p-adic denominator
through its chosen integral representative. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeColumnPadic
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (j : Fin n) :
    associatedBilinearDualPadicDenominator L p k :=
  ⟨integralVectorToPadic (n := n) p (fun i =>
      associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
        L p k H i j),
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix_col_mem
      L p k H j⟩

/-- The source kernel/subquotient equivalence sends a correction column to
the class of its chosen integral representative. -/
lemma
    associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivPadicSubquotient_correctionColumn
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (j : Fin n) :
    associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivPadicSubquotient
        L p k (H j) =
      ((associatedBilinearDualPadicDenominator L p (k + 1)).comap
        (associatedBilinearDualPadicDenominator L p k).subtype).mkQ
        (associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeColumnPadic
          L p k H j) := by
  unfold
    associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivPadicSubquotient
  simp only [LinearEquiv.trans_apply]
  let d :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeColumnPadic
      L p k H j
  have hfirst :
      associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivPadic
          L p k (H j) =
        ⟨(associatedBilinearDualPadicDenominator L p (k + 1)).mkQ d.1,
          by
            rw [LinearMap.mem_ker]
            exact (Submodule.Quotient.mk_eq_zero _).mpr d.2⟩ := by
    apply Subtype.ext
    change
      associatedBilinearDualPadicDenominatorIntegralPreimageQuotientEquiv
          L p (k + 1) (H j).1 =
        (associatedBilinearDualPadicDenominator L p (k + 1)).mkQ d.1
    change padicSubmoduleIntegralPreimageQuotientMap (n := n) p
        (associatedBilinearDualPadicDenominator L p (k + 1)) (H j).1 = _
    calc
      padicSubmoduleIntegralPreimageQuotientMap (n := n) p
          (associatedBilinearDualPadicDenominator L p (k + 1)) (H j).1 =
        padicSubmoduleIntegralPreimageQuotientMap (n := n) p
          (associatedBilinearDualPadicDenominator L p (k + 1))
          ((associatedBilinearDualPadicDenominatorIntegralPreimage
            L p (k + 1)).mkQ (Quotient.out (H j).1)) := by
              exact congrArg
                (padicSubmoduleIntegralPreimageQuotientMap (n := n) p
                  (associatedBilinearDualPadicDenominator L p (k + 1)))
                (Submodule.Quotient.mk_out (H j).1).symm
      _ = (associatedBilinearDualPadicDenominator L p (k + 1)).mkQ d.1 := rfl
  rw [hfirst]
  exact
    padicSubmoduleQuotientMapOfLEKerEquivSubquotient_mkQ
      (n := n)
      (associatedBilinearDualPadicDenominator_succ_le L p k) d

/-- Source correction families are residue matrices under exact source
lattice depth. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivMatrix
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k) :
    associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k ≃ₗ[ℤ]
      Matrix (Fin n) (Fin n) (ZMod p) :=
  LinearEquiv.piCongrRight (fun _ =>
    associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivResidue
      L p k hk)

/-- Residue-matrix entries of a source correction are precisely the standard
source-denominator coordinates of its scaled integral columns modulo `p`. -/
lemma
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivMatrix_apply
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (j i : Fin n) :
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivMatrix
        L p k hk H j i =
      PadicInt.toZMod
        (associatedBilinearDualPadicDenominatorEquivCoordinates L p k hk
          (associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeColumnPadic
            L p k H j) i) := by
  change
    (associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivResidue
      L p k hk (H j)) i = _
  unfold
    associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivResidue
  simp only [LinearEquiv.trans_apply]
  change
    (associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue
      L p k hk
      (associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivPadicSubquotient
        L p k (H j))) i = _
  rw [
    associatedBilinearDualPadicDenominatorIntegralPreimageSuccKernelEquivPadicSubquotient_correctionColumn]
  exact congrFun
    (associatedBilinearDualPadicDenominatorAdjacentSubquotientToResidue_mkQ
      L p k hk
      (associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeColumnPadic
        L p k H j)) i

/-- Divide one associated-bilinear Gram coordinate of an integral correction
column by its guaranteed factor `p^k`. -/
def
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotient
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (j i : Fin n) : ℤ :=
  L.polarGramMatrix.mulVec
      (fun a =>
        associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
          L p k H a j) i /
    ((p : ℤ) ^ k)

lemma
    primePow_mul_associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotient
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (j i : Fin n) :
    ((p : ℤ) ^ k) *
        associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotient
          L p k H j i =
      L.polarGramMatrix.mulVec
        (fun a =>
          associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
            L p k H a j) i := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel
    (primePow_dvd_polarGramMatrix_mulVec_of_mem_associatedBilinearDualPadicDenominatorIntegralPreimage
      L p k _
      (associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix_col_mem
        L p k H j) i)

/-- The computational correction residue is the divided integral Gram
coordinate of the chosen correction column. -/
lemma
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivMatrix_apply_eq_gramCoordinateQuotient
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselLatticeDepth p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (j i : Fin n) :
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivMatrix
        L p k hk H j i =
      (associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotient
        L p k H j i : ZMod p) := by
  rw [
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivMatrix_apply]
  rw [← map_intCast PadicInt.toZMod]
  apply congrArg PadicInt.toZMod
  apply PadicInt.ext
  let d :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeColumnPadic
      L p k H j
  let q :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotient
      L p k H j i
  change
    (L.polarGramMatrix_padicField p).mulVec
        (fun a => (d.1 a : ℚ_[p]) / (p : ℚ_[p]) ^ k) i =
      (q : ℚ_[p])
  have hp : (p : ℚ_[p]) ^ k ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  have hleft :
      (L.polarGramMatrix_padicField p).mulVec
          (fun a => (d.1 a : ℚ_[p]) / (p : ℚ_[p]) ^ k) i =
        (L.polarGramMatrix.mulVec
          (fun a =>
            associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
              L p k H a j) i : ℚ_[p]) /
          (p : ℚ_[p]) ^ k := by
    simp only [d, polarGramMatrix_padicField, Matrix.mulVec, dotProduct,
      associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeColumnPadic,
      integralVectorToPadic, div_eq_mul_inv, Matrix.map_apply]
    push_cast
    rw [Finset.sum_mul]
    simp only [mul_assoc]
  rw [hleft]
  apply (div_eq_iff hp).2
  have hmul :=
    primePow_mul_associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotient
      L p k H j i
  calc
    (L.polarGramMatrix.mulVec
        (fun a =>
          associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
            L p k H a j) i : ℚ_[p]) =
        (((p : ℤ) ^ k) * q : ℤ) := by
      exact congrArg (fun z : ℤ => (z : ℚ_[p])) hmul.symm
    _ = (q : ℚ_[p]) * (p : ℚ_[p]) ^ k := by
      push_cast
      ring

/-- The integral matrix of divided associated-bilinear Gram coordinates of a
source correction. Rows index correction columns, matching the established
residue correction-matrix convention. -/
def
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotientMatrix
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun j i =>
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotient
      L p k H j i

/-- Columnwise exact division assembles into the vector identity
`gram(L) * (Gx) = p^k (Cᵀx)`. -/
lemma
    polarGramMatrix_mulVec_associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix_mulVec
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (x : Fin n → ℤ) :
    L.polarGramMatrix.mulVec
        ((associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
          L p k H).mulVec x) =
      ((p : ℤ) ^ k) •
        ((associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotientMatrix
          L p k H)ᵀ.mulVec x) := by
  rw [Matrix.mulVec_mulVec]
  ext i
  simp only [Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only
    [associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotientMatrix]
  change
    (L.polarGramMatrix.mulVec
      (fun a =>
        associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
          L p k H a j) i) * x j = _
  rw [←
    primePow_mul_associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotient]
  ring

/-- The integral associated-bilinear cross term in the corrected source
lift. -/
def
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTerm
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (x : Fin n → ℤ) : ℤ :=
  dotProduct
    ((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
      L p k Y).mulVec x)
    (L.polarGramMatrix.mulVec
      ((associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
        L p k H).mulVec x))

/-- Divide the corrected-lift cross term by its exact factor `p^k`. -/
def
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (x : Fin n → ℤ) : ℤ :=
  associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTerm
      L p k Y H x /
    ((p : ℤ) ^ k)

lemma
    primePow_mul_associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (x : Fin n → ℤ) :
    ((p : ℤ) ^ k) *
        associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient
          L p k Y H x =
      associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTerm
        L p k Y H x := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel ⟨
    dotProduct
      ((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
        L p k Y).mulVec x)
      (((associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotientMatrix
        L p k H)ᵀ).mulVec x), by
    unfold
      associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTerm
    rw [
      polarGramMatrix_mulVec_associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix_mulVec,
      dotProduct_smul]
    simp only [smul_eq_mul]⟩

/-- The divided integral cross term is the quadratic polynomial defined by
the source representative matrix and the transposed correction coordinates.
-/
lemma
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient_eq_dotProduct
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (x : Fin n → ℤ) :
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient
        L p k Y H x =
      dotProduct
        ((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
          L p k Y).mulVec x)
        (((associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotientMatrix
          L p k H)ᵀ).mulVec x) := by
  apply Int.ediv_eq_of_eq_mul_left
  · exact pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  · unfold
      associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTerm
    rw [
      polarGramMatrix_mulVec_associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix_mulVec,
      dotProduct_smul]
    simp only [smul_eq_mul]
    ring

/-- Add a source-normalized columnwise kernel correction to the canonical raw
lift. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k) :
    Fin n → localDualQuotientTarget
      (associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + 1)) :=
  fun i =>
    associatedBilinearDualQuotientSolutionFamilySuccRawLift
      L p k Y i + (H i).1

lemma
    associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift_reduces
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k) :
    localDualQuotientFamilyOfLE (n := n)
        (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
          L p k)
        (associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift
          L p k Y H) = Y.1 := by
  ext i
  change localDualQuotientMapOfLE (n := n)
      (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le L p k)
      (associatedBilinearDualQuotientSolutionFamilySuccRawLift
        L p k Y i + (H i).1) = Y.1 i
  rw [map_add, LinearMap.mem_ker.mp (H i).2, add_zero]
  exact congr_fun
    (associatedBilinearDualQuotientSolutionFamilySuccRawLift_reduces
      L p k Y) i

/-- The corrected source quotient-family map is represented integrally by
the sum of the source solution matrix and the correction matrix. -/
lemma
    associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift_quotientBasisFamilyMap
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (x : Fin n → ℤ) :
    quotientBasisFamilyMap
        (associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + 1))
        (associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift
          L p k Y H) x =
      (associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + 1)).mkQ
        (((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
            L p k Y) +
          associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
            L p k H).mulVec x) := by
  classical
  let Dsucc :=
    associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + 1)
  let X :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
      L p k Y
  let G :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
      L p k H
  calc
    quotientBasisFamilyMap Dsucc
        (associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift
          L p k Y H) x =
        ∑ j, (x j) •
          (Dsucc.mkQ (Quotient.out (Y.1 j)) + (H j).1) := by
      rfl
    _ = ∑ j, (x j) •
          (Dsucc.mkQ (Quotient.out (Y.1 j)) +
            Dsucc.mkQ (Quotient.out (H j).1)) := by
      apply Finset.sum_congr rfl
      intro j _
      have hH : Dsucc.mkQ (Quotient.out (H j).1) = (H j).1 :=
        Submodule.Quotient.mk_out (H j).1
      rw [hH]
    _ = Dsucc.mkQ
        (∑ j, (x j) •
          (Quotient.out (Y.1 j) + Quotient.out (H j).1)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, map_add]
    _ = Dsucc.mkQ ((X + G).mulVec x) := by
      apply congrArg Dsucc.mkQ
      ext i
      simp only [X, G,
        associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix,
        associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix,
        Matrix.mulVec, dotProduct, Matrix.add_apply]
      rw [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
      ring

/-- Integral cross-term expansion for a corrected source lift. The middle
term is written with the associated-bilinear Gram matrix so that division by
`p^k` matches the source correction residue coordinates. -/
lemma
    associatedBilinearDualQuotientSolutionFamilySuccCorrection_quadForm_expansion
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (x : Fin n → ℤ) :
    let X :=
      associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
        L p k Y
    let G :=
      associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
        L p k H
    L.quadForm ((X + G).mulVec x) =
      L.quadForm (X.mulVec x) +
        dotProduct (X.mulVec x) (L.polarGramMatrix.mulVec (G.mulVec x)) +
          L.quadForm (G.mulVec x) := by
  dsimp only
  let X :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
      L p k Y
  let G :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
      L p k H
  have hadd : (X + G).mulVec x = X.mulVec x + G.mulVec x := by
    ext i
    simp [Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]
  rw [hadd, quadForm_add_eq_bilinearFormValue,
    dotProduct_polarGramMatrix_mulVec]

/-- The pure quadratic term of a source correction vanishes modulo the next
prime-power depth. -/
lemma
    primePow_succ_dvd_associatedBilinearDualQuotientSolutionFamilySuccCorrection_quadForm
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (x : Fin n → ℤ) :
    ((p : ℤ) ^ (k + 1)) ∣
      L.quadForm
        ((associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
          L p k H).mulVec x) := by
  let D := associatedBilinearDualPadicDenominatorIntegralPreimage L p k
  let G :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
      L p k H
  have hGx : G.mulVec x ∈ D := by
    have hsum : ∑ j, (x j) • G.col j ∈ D := by
      exact D.sum_mem fun j _ => D.smul_mem (x j)
        (associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix_col_mem
          L p k H j)
    convert hsum using 1
    ext i
    simp [G, Matrix.mulVec, dotProduct, mul_comm]
  exact
    primePow_succ_dvd_quadForm_of_mem_associatedBilinearDualPadicDenominatorIntegralPreimage
      L p k hk (G.mulVec x) hGx

/-- Every underlying source-normalized adjacent lift is uniquely its canonical
raw lift plus a columnwise source correction. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivUnderlyingFiber
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k ≃
      {Z : Fin n → localDualQuotientTarget
          (associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + 1)) //
        localDualQuotientFamilyOfLE (n := n)
          (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
            L p k) Z = Y.1} where
  toFun H :=
    ⟨associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift
        L p k Y H,
      associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift_reduces
        L p k Y H⟩
  invFun Z := fun i =>
    ⟨Z.1 i -
        associatedBilinearDualQuotientSolutionFamilySuccRawLift
          L p k Y i, by
      rw [LinearMap.mem_ker, map_sub]
      have hZi := congr_fun Z.2 i
      have hRi := congr_fun
        (associatedBilinearDualQuotientSolutionFamilySuccRawLift_reduces
          L p k Y) i
      exact sub_eq_zero.mpr (hZi.trans hRi.symm)⟩
  left_inv H := by
    ext i
    simp [associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift]
  right_inv Z := by
    ext i
    simp [associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift]

/-- A source correction solves the adjacent Hensel problem when its corrected
raw lift satisfies the source depth-`k+1` quadratic congruence. -/
def IsLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k) : Prop :=
  associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift
      L p k Y H ∈
    localDualQuotientSolutionFamilies L p (k + 1)
      (associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + 1))
      (associatedBilinearDualPadicDenominatorIntegralPreimage_rank
        (n := n) L p (k + 1))

/-- A source correction is valid exactly when its corrected integral
representative preserves the quadratic form modulo the adjacent prime-power
depth. -/
lemma
    isLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection_iff_quadForm
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k) :
    IsLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k Y H ↔
      ∀ x : Fin n → ℤ,
        (L.quadForm
            (((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
                L p k Y) +
              associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
                L p k H).mulVec x) :
              ZMod (primePowModulus p (k + 1) : ℕ)) =
          (L.quadForm x : ZMod (primePowModulus p (k + 1) : ℕ)) := by
  let D :=
    associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + 1)
  let Z :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift
      L p k Y H
  let M :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
        L p k Y +
      associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
        L p k H
  constructor
  · intro h x
    exact (mem_localDualQuotientSolutionFamilies_iff.mp h) x (M.mulVec x)
      (associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift_quotientBasisFamilyMap
        L p k Y H x)
  · intro h
    change Z ∈
      localDualQuotientSolutionFamilies L p (k + 1) D
        (associatedBilinearDualPadicDenominatorIntegralPreimage_rank
          (n := n) L p (k + 1))
    rw [mem_localDualQuotientSolutionFamilies_iff]
    intro x y hxy
    have hM : D.mkQ (M.mulVec x) = D.mkQ y := by
      calc
        D.mkQ (M.mulVec x) = quotientBasisFamilyMap D Z x :=
          (associatedBilinearDualQuotientSolutionFamilySuccCorrectedRawLift_quotientBasisFamilyMap
            L p k Y H x).symm
        _ = D.mkQ y := hxy
    have hyM : y - M.mulVec x ∈ D := by
      have hM' := hM.symm
      change Submodule.Quotient.mk y =
        Submodule.Quotient.mk (M.mulVec x) at hM'
      exact (Submodule.Quotient.eq D).mp hM'
    exact
      ((associatedBilinearDualPadicDenominatorIntegralPreimage_admissible
          L p (k + 1) (hk.succ L p k)).2 hyM).trans (h x)

/-- After removing the correction's quadratically negligible term, the
adjacent source congruence is exactly the vanishing of the raw defect plus
the associated-bilinear cross term. -/
lemma
    isLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection_iff_rawDefect_add_crossTerm
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k) :
    IsLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k Y H ↔
      ∀ x : Fin n → ℤ,
        ((associatedBilinearDualQuotientSolutionFamilyRawDefect
              L p k Y x +
            associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTerm
              L p k Y H x : ℤ) :
            ZMod (primePowModulus p (k + 1) : ℕ)) = 0 := by
  rw [
    isLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection_iff_quadForm
      L p k hk Y H]
  apply forall_congr'
  intro x
  let X :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
      L p k Y
  let G :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionRepresentativeMatrix
      L p k H
  let q := primePowModulus p (k + 1)
  have hGzero : (L.quadForm (G.mulVec x) : ZMod q) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [q, primePowModulus] using
      (primePow_succ_dvd_associatedBilinearDualQuotientSolutionFamilySuccCorrection_quadForm
        L p k hk H x)
  have hexpand :
      L.quadForm ((X + G).mulVec x) - L.quadForm x =
        associatedBilinearDualQuotientSolutionFamilyRawDefect
            L p k Y x +
          associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTerm
            L p k Y H x +
          L.quadForm (G.mulVec x) := by
    rw [
      associatedBilinearDualQuotientSolutionFamilySuccCorrection_quadForm_expansion]
    simp only
      [associatedBilinearDualQuotientSolutionFamilyRawDefect,
        associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTerm,
        G]
    ring
  have hcast :
      ((L.quadForm ((X + G).mulVec x) - L.quadForm x : ℤ) : ZMod q) =
        ((associatedBilinearDualQuotientSolutionFamilyRawDefect
              L p k Y x +
            associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTerm
              L p k Y H x : ℤ) : ZMod q) := by
    rw [hexpand]
    push_cast
    rw [hGzero, add_zero]
  constructor
  · intro h
    have hzero :
        ((L.quadForm ((X + G).mulVec x) - L.quadForm x : ℤ) : ZMod q) = 0 := by
      push_cast
      exact sub_eq_zero.mpr h
    rw [hcast] at hzero
    exact hzero
  · intro h
    apply sub_eq_zero.mp
    have hzero :
        ((L.quadForm ((X + G).mulVec x) - L.quadForm x : ℤ) : ZMod q) = 0 := by
      rw [hcast]
      exact h
    simpa using hzero

/-- Cancelling the common factor `p^k` reduces the adjacent prime-power
congruence to the residue-field equation for the two divided defects. -/
lemma
    isLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection_iff_dividedRawDefect_add_crossTermQuotient
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k) :
    IsLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k Y H ↔
      ∀ x : Fin n → ℤ,
        (((associatedBilinearDualQuotientSolutionFamilyRawDefect
                L p k Y x / (p : ℤ) ^ k : ℤ) +
            associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient
              L p k Y H x : ℤ) : ZMod p) = 0 := by
  rw [
    isLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection_iff_rawDefect_add_crossTerm
      L p k hk Y H]
  apply forall_congr'
  intro x
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  let raw :=
    associatedBilinearDualQuotientSolutionFamilyRawDefect
      L p k Y x
  let rawQ := raw / (p : ℤ) ^ k
  let cross :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTerm
      L p k Y H x
  let crossQ :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient
      L p k Y H x
  change ((p : ℤ) ^ (k + 1) ∣ raw + cross) ↔
    (p : ℤ) ∣ rawQ + crossQ
  have hraw : (p : ℤ) ^ k * rawQ = raw := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel
      (primePow_dvd_associatedBilinearDualQuotientSolutionFamilyRawDefect
        L p k Y x)
  have hcross : (p : ℤ) ^ k * crossQ = cross :=
    primePow_mul_associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient
      L p k Y H x
  have hsum : raw + cross = (p : ℤ) ^ k * (rawQ + crossQ) := by
    rw [← hraw, ← hcross]
    ring
  rw [hsum, pow_succ]
  exact Int.mul_dvd_mul_iff_left
    (pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero))

/-- The fiber of source-normalized adjacent reduction is exactly its valid
source correction subtype. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivReductionFiber
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    {H :
        associatedBilinearDualQuotientSolutionFamilySuccCorrection
          L p k //
      IsLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k Y H} ≃
      {Z : associatedBilinearDualQuotientSolutionFamily
          L p (k + 1) //
        associatedBilinearDualQuotientSolutionFamilySuccReduction
          L p k hk Z = Y} := by
  let e :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivUnderlyingFiber
      L p k Y
  refine
    { toFun := fun H =>
        ⟨⟨(e H.1).1, H.2⟩, ?_⟩
      invFun := fun Z =>
        ⟨e.symm ⟨Z.1.1, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Subtype.ext
    exact (e H.1).2
  · have h := congrArg Subtype.val Z.2
    simpa using h
  · change (e (e.symm ⟨Z.1.1, _⟩)).1 ∈ _
    rw [e.apply_symm_apply]
    exact Z.1.2
  · intro H
    apply Subtype.ext
    exact e.symm_apply_apply H.1
  · intro Z
    apply Subtype.ext
    apply Subtype.ext
    change (e (e.symm ⟨Z.1.1, _⟩)).1 = Z.1.1
    exact congrArg Subtype.val (e.apply_symm_apply ⟨Z.1.1, _⟩)

lemma localDualQuotientFamilyOfLE_preimage_mem_localDualQuotientSolutionFamilies
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {D E : Submodule ℤ (Fin n → ℤ)}
    {hD_rank : Module.finrank ℤ D = n} {hE_rank : Module.finrank ℤ E = n}
    (hDE : D ≤ E) {Y : Fin n → localDualQuotientTarget E}
    (hY : Y ∈ localDualQuotientSolutionFamilies L p k E hE_rank)
    {Z : Fin n → localDualQuotientTarget D}
    (hZ : localDualQuotientFamilyOfLE (n := n) hDE Z = Y) :
    Z ∈ localDualQuotientSolutionFamilies L p k D hD_rank := by
  classical
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  have hmap :
      quotientBasisFamilyMap E Y x = E.mkQ y := by
    rw [← hZ]
    rw [quotientBasisFamilyMap_ofLE (n := n) hDE Z x, hxy]
    exact localDualQuotientMapOfLE_mkQ (n := n) hDE y
  exact (mem_localDualQuotientSolutionFamilies_iff.mp hY) x y hmap

/-- At positive dyadic depth, one source/current denominator column has
exactly `2^n` refinements. The exact shift `S_(r+1)=D_r` reduces this to the
existing residue-kernel calculation for adjacent current denominators. -/
lemma associatedBilinearDualCurrentDenominatorSubquotient_natCard_dyadic
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ) (hk : 1 ≤ k)
    (hquad : L.IsAssociatedBilinearHenselQuadraticDepth 2 k) :
    Nat.card
        (associatedBilinearDualPadicDenominatorIntegralPreimage L 2 k ⧸
          (localDualPadicDenominatorIntegralPreimage L 2 k).comap
            (associatedBilinearDualPadicDenominatorIntegralPreimage L 2 k).subtype) =
      2 ^ n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hsourceLattice :
      L.IsAssociatedBilinearHenselLatticeDepth 2 (r + 1) := by
    simpa [Nat.add_comm] using
      hquad.latticeDepth L 2 (1 + r)
  have hcurrentLattice : L.IsHenselLatticeDepth 2 r :=
    hsourceLattice.current_of_succ_dyadic L r
  rw [show 1 + r = r + 1 by omega,
    L.associatedBilinearDualPadicDenominatorIntegralPreimage_succ_eq_localDualPadicDenominatorIntegralPreimage_dyadic]
  rw [← localDualQuotientMapOfLE_ker_card_eq_subquotient
    (n := n) (localDualPadicDenominatorIntegralPreimage_succ_le L 2 r)]
  exact natCard_localDualPadicDenominatorIntegralPreimage_succKernel
    L 2 r hcurrentLattice

/-- Project a current dyadic solution family to the source-normalized
associated-bilinear-dual quotient at the same congruence depth. -/
noncomputable def currentToAssociatedBilinearDualSolutionFamily_dyadic
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ)
    (hk : IsLocalDensityHenselExponent L 2 k) :
    localDualQuotientSolutionFamily L 2 k →
      associatedBilinearDualQuotientSolutionFamily L 2 k := by
  intro Y
  let hDE :=
    localDualPadicDenominatorIntegralPreimage_le_associatedBilinearDualPadicDenominatorIntegralPreimage_dyadic
      L k hk.admissible.one_le
  let hE := associatedBilinearDualPadicDenominatorIntegralPreimage_admissible
    L 2 k hk.associated_bilinear_quadratic_depth
  exact ⟨localDualQuotientFamilyOfLE (n := n) hDE Y.1,
    localDualQuotientFamilyOfLE_mem_localDualQuotientSolutionFamilies
      (hD_rank := localDualPadicDenominatorIntegralPreimage_rank (n := n) L 2 k)
      (hE := hE) hDE Y.2⟩

@[simp] lemma currentToAssociatedBilinearDualSolutionFamily_dyadic_coe
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ)
    (hk : IsLocalDensityHenselExponent L 2 k)
    (Y : localDualQuotientSolutionFamily L 2 k) :
    (currentToAssociatedBilinearDualSolutionFamily_dyadic
      L k hk Y).1 =
      localDualQuotientFamilyOfLE (n := n)
        (localDualPadicDenominatorIntegralPreimage_le_associatedBilinearDualPadicDenominatorIntegralPreimage_dyadic
          L k hk.admissible.one_le) Y.1 := rfl

/-- The fiber over a source solution is the full raw quotient-family fiber:
every current refinement preserves the same depth-`k` quadratic congruence. -/
noncomputable def
    currentToAssociatedBilinearDualSolutionFamily_dyadic_fiberEquiv
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ)
    (hk : IsLocalDensityHenselExponent L 2 k)
    (Y : associatedBilinearDualQuotientSolutionFamily L 2 k) :
    {X : localDualQuotientSolutionFamily L 2 k //
      currentToAssociatedBilinearDualSolutionFamily_dyadic
        L k hk X = Y} ≃
      {Z : Fin n → localDualQuotientTarget
          (localDualPadicDenominatorIntegralPreimage L 2 k) //
        localDualQuotientFamilyOfLE (n := n)
          (localDualPadicDenominatorIntegralPreimage_le_associatedBilinearDualPadicDenominatorIntegralPreimage_dyadic
            L k hk.admissible.one_le) Z = Y.1} where
  toFun X := ⟨X.1.1, congrArg Subtype.val X.2⟩
  invFun Z :=
    ⟨⟨Z.1,
      localDualQuotientFamilyOfLE_preimage_mem_localDualQuotientSolutionFamilies
        (L := L) (p := 2) (k := k)
        (hD_rank := localDualPadicDenominatorIntegralPreimage_rank (n := n) L 2 k)
        (hE_rank :=
          associatedBilinearDualPadicDenominatorIntegralPreimage_rank (n := n) L 2 k)
        (localDualPadicDenominatorIntegralPreimage_le_associatedBilinearDualPadicDenominatorIntegralPreimage_dyadic
          L k hk.admissible.one_le) Y.2 Z.2⟩,
      by
        apply Subtype.ext
        exact Z.2⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv Z := by
    apply Subtype.ext
    rfl

lemma currentToAssociatedBilinearDualSolutionFamily_dyadic_fiber_natCard
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ)
    (hk : IsLocalDensityHenselExponent L 2 k)
    (Y : associatedBilinearDualQuotientSolutionFamily L 2 k) :
    Nat.card
        {X : localDualQuotientSolutionFamily L 2 k //
          currentToAssociatedBilinearDualSolutionFamily_dyadic
            L k hk X = Y} =
      2 ^ (n * n) := by
  rw [Nat.card_congr
    (currentToAssociatedBilinearDualSolutionFamily_dyadic_fiberEquiv
      L k hk Y)]
  have hfamily :=
    localDualQuotientFamilyOfLE_fiber_card_eq_pow_of_subquotient_card
      (n := n)
      (localDualPadicDenominatorIntegralPreimage_rank (n := n) L 2 k)
      (associatedBilinearDualPadicDenominatorIntegralPreimage_rank (n := n) L 2 k)
      (localDualPadicDenominatorIntegralPreimage_le_associatedBilinearDualPadicDenominatorIntegralPreimage_dyadic
        L k hk.admissible.one_le)
      Y.1 (2 ^ n)
      (associatedBilinearDualCurrentDenominatorSubquotient_natCard_dyadic
        L k hk.admissible.one_le hk.associated_bilinear_quadratic_depth)
  calc
    Nat.card
        {Z : Fin n → localDualQuotientTarget
            (localDualPadicDenominatorIntegralPreimage L 2 k) //
          localDualQuotientFamilyOfLE (n := n)
            (localDualPadicDenominatorIntegralPreimage_le_associatedBilinearDualPadicDenominatorIntegralPreimage_dyadic
              L k hk.admissible.one_le) Z = Y.1} =
        (2 ^ n) ^ n := hfamily
    _ = 2 ^ (n * n) := by rw [← pow_mul]

/-- At a valid dyadic Hensel depth, the current `F`-dual count is the source
associated-bilinear-dual count times the depth-independent factor
`2^(n*n)`. -/
lemma localDualQuotientCount_eq_two_pow_mul_associatedBilinear_dyadic
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ)
    (hk : IsLocalDensityHenselExponent L 2 k) :
    localDualQuotientCount L 2 k =
      2 ^ (n * n) *
        associatedBilinearDualQuotientCount L 2 k := by
  rw [localDualQuotientCount_eq_natCard_solutionFamily,
    associatedBilinearDualQuotientCount_eq_natCard_solutionFamily]
  have hcount := nat_card_eq_mul_of_fiber_card
    (currentToAssociatedBilinearDualSolutionFamily_dyadic
      L k hk)
    (2 ^ (n * n))
    (currentToAssociatedBilinearDualSolutionFamily_dyadic_fiber_natCard
      L k hk)
  rw [hcount, Nat.mul_comm]

lemma localDualPadicTransportedIntegralPreimageBasisFamily_mem_localDualQuotientSolutionFamilies_of_equiv
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p k : ℕ) [Fact (Nat.Prime p)]
    {U : Matrix (Fin n) (Fin n) ℤ_[p]}
    (hU : Uᵀ * L₁.pairingMatrix_padic p * U = L₀.pairingMatrix_padic p)
    (e : (Fin n → ℤ_[p]) ≃ₗ[ℤ_[p]] (Fin n → ℤ_[p]))
    (hDE : Submodule.map e.toLinearMap (localDualPadicDenominator L₀ p k) =
        localDualPadicDenominator L₁ p k)
    (he_apply : ∀ x : Fin n → ℤ_[p], e x = U.mulVec x)
    {Y : Fin n → localDualQuotientTarget
      (padicSubmoduleIntegralPreimage (n := n) p
        (localDualPadicDenominator L₀ p k))}
    (hY : Y ∈ localDualQuotientSolutionFamilies L₀ p k
      (padicSubmoduleIntegralPreimage (n := n) p
        (localDualPadicDenominator L₀ p k))
      (padicSubmoduleIntegralPreimage_localDualPadicDenominator_rank (n := n) L₀ p k)) :
    localDualPadicTransportedIntegralPreimageBasisFamily
        (n := n) L₁ p k (localDualPadicDenominator L₀ p k) e hDE
        (fun i => padicSubmoduleIntegralPreimageQuotientMap (n := n) p
          (localDualPadicDenominator L₀ p k) (Y i)) ∈
      localDualQuotientSolutionFamilies L₁ p k
        (padicSubmoduleIntegralPreimage (n := n) p
          (localDualPadicDenominator L₁ p k))
        (padicSubmoduleIntegralPreimage_localDualPadicDenominator_rank (n := n) L₁ p k) := by
  classical
  let D₀ : Submodule ℤ_[p] (Fin n → ℤ_[p]) := localDualPadicDenominator L₀ p k
  let D₁ : Submodule ℤ_[p] (Fin n → ℤ_[p]) := localDualPadicDenominator L₁ p k
  let S₀ : Submodule ℤ (Fin n → ℤ) := padicSubmoduleIntegralPreimage (n := n) p D₀
  let Yp : Fin n → ((Fin n → ℤ_[p]) ⧸ D₀) :=
    fun i => padicSubmoduleIntegralPreimageQuotientMap (n := n) p D₀ (Y i)
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  let vx : Fin n → ℤ_[p] := e.symm (integralVectorToPadic (n := n) p x)
  let vy : Fin n → ℤ_[p] := e.symm (integralVectorToPadic (n := n) p y)
  have hx_lift := exists_integralVectorToPadic_forall_primePow_dvd_sub
    (n := n) p k vx
  rcases hx_lift with ⟨x₀, hx₀⟩
  have hy_lift := exists_integralVectorToPadic_forall_primePow_dvd_sub
    (n := n) p k vy
  rcases hy_lift with ⟨y₀, hy₀⟩
  have htarget_padic :
      padicQuotientBasisFamilyMapFromPadicValues (n := n) p D₁
          (padicQuotientTransportedBasisFamily (n := n) p D₀ D₁ e hDE Yp)
          (integralVectorToPadic (n := n) p x) =
        D₁.mkQ (integralVectorToPadic (n := n) p y) := by
    exact (quotientBasisFamilyMap_localDualPadicTransportedIntegralPreimageBasisFamily_eq_mkQ_iff
      (n := n) L₁ p k D₀ e hDE Yp x y).mp hxy
  have hpre_padic :
      padicQuotientBasisFamilyMapFromPadicValues (n := n) p D₀ Yp vx =
        D₀.mkQ vy := by
    exact (padicQuotientBasisFamilyMapFromPadicValues_transport_eq_mkQ_iff
      (n := n) p D₀ D₁ e hDE Yp
      (integralVectorToPadic (n := n) p x)
      (integralVectorToPadic (n := n) p y)).mp htarget_padic
  have hmap_x₀ :
      padicQuotientBasisFamilyMapFromPadicValues (n := n) p D₀ Yp vx =
        padicQuotientBasisFamilyMap (n := n) p D₀ Y x₀ := by
    exact padicQuotientBasisFamilyMap_eq_of_forall_primePow_dvd_sub
      (n := n) L₀ p k Y vx x₀ hx₀
  have hmk_y₀ : D₀.mkQ vy = D₀.mkQ (integralVectorToPadic (n := n) p y₀) := by
    change (Submodule.Quotient.mk vy : (Fin n → ℤ_[p]) ⧸ D₀) =
      Submodule.Quotient.mk (integralVectorToPadic (n := n) p y₀)
    rw [Submodule.Quotient.eq]
    exact mem_localDualPadicDenominator_of_forall_coord_primePow_dvd
      (n := n) L₀ p k hy₀
  have hsource_padic :
      padicQuotientBasisFamilyMap (n := n) p D₀ Y x₀ =
        D₀.mkQ (integralVectorToPadic (n := n) p y₀) := by
    rw [← hmap_x₀, hpre_padic, hmk_y₀]
  have hsource :
      quotientBasisFamilyMap S₀ Y x₀ = S₀.mkQ y₀ := by
    refine padicSubmoduleIntegralPreimageQuotientMap_injective (n := n) p D₀ ?_
    rw [padicSubmoduleIntegralPreimageQuotientMap_quotientBasisFamilyMap,
      padicSubmoduleIntegralPreimageQuotientMap_mkQ]
    exact hsource_padic
  have hq₀ :
      (L₀.quadForm y₀ : ZMod (primePowModulus p k : ℕ)) =
        (L₀.quadForm x₀ : ZMod (primePowModulus p k : ℕ)) := by
    exact (mem_localDualQuotientSolutionFamilies_iff.mp hY) x₀ y₀ hsource
  have hUx : U.mulVec vx = integralVectorToPadic (n := n) p x := by
    rw [← he_apply vx]
    exact e.apply_symm_apply (integralVectorToPadic (n := n) p x)
  have hUy : U.mulVec vy = integralVectorToPadic (n := n) p y := by
    rw [← he_apply vy]
    exact e.apply_symm_apply (integralVectorToPadic (n := n) p y)
  have hxquad :
      (L₀.quadForm x₀ : ZMod (primePowModulus p k : ℕ)) =
        (L₁.quadForm x : ZMod (primePowModulus p k : ℕ)) :=
    quadForm_zmod_eq_of_local_isometry_matrix_approx
      (L₀ := L₀) (L₁ := L₁) p k hU vx x₀ x hx₀ hUx
  have hyquad :
      (L₀.quadForm y₀ : ZMod (primePowModulus p k : ℕ)) =
        (L₁.quadForm y : ZMod (primePowModulus p k : ℕ)) :=
    quadForm_zmod_eq_of_local_isometry_matrix_approx
      (L₀ := L₀) (L₁ := L₁) p k hU vy y₀ y hy₀ hUy
  rw [← hyquad, ← hxquad]
  exact hq₀

lemma localDualPadicTransportedIntegralPreimageBasisFamily_mem_localDualQuotientSolutionFamilies
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p k : ℕ) [Fact (Nat.Prime p)]
    {U : Matrix (Fin n) (Fin n) ℤ_[p]}
    (hU_unit : IsUnit U)
    (hU : Uᵀ * L₁.pairingMatrix_padic p * U = L₀.pairingMatrix_padic p)
    {Y : Fin n → localDualQuotientTarget
      (padicSubmoduleIntegralPreimage (n := n) p
        (localDualPadicDenominator L₀ p k))}
    (hY : Y ∈ localDualQuotientSolutionFamilies L₀ p k
      (padicSubmoduleIntegralPreimage (n := n) p
        (localDualPadicDenominator L₀ p k))
      (padicSubmoduleIntegralPreimage_localDualPadicDenominator_rank (n := n) L₀ p k)) :
    let e := padicMatrixLinearEquivOfIsUnit (n := n) p U hU_unit
    let hDE : Submodule.map e.toLinearMap (localDualPadicDenominator L₀ p k) =
        localDualPadicDenominator L₁ p k := by
      change Submodule.map (Matrix.toLin' U) (localDualPadicDenominator L₀ p k) =
        localDualPadicDenominator L₁ p k
      exact localDualPadicDenominator_map_of_local_isometry_matrix
        (L₀ := L₀) (L₁ := L₁) p k hU_unit hU
    localDualPadicTransportedIntegralPreimageBasisFamily
        (n := n) L₁ p k (localDualPadicDenominator L₀ p k) e hDE
        (fun i => padicSubmoduleIntegralPreimageQuotientMap (n := n) p
          (localDualPadicDenominator L₀ p k) (Y i)) ∈
      localDualQuotientSolutionFamilies L₁ p k
        (padicSubmoduleIntegralPreimage (n := n) p
          (localDualPadicDenominator L₁ p k))
        (padicSubmoduleIntegralPreimage_localDualPadicDenominator_rank (n := n) L₁ p k) := by
  classical
  dsimp
  let e := padicMatrixLinearEquivOfIsUnit (n := n) p U hU_unit
  let hDE : Submodule.map e.toLinearMap (localDualPadicDenominator L₀ p k) =
      localDualPadicDenominator L₁ p k := by
    change Submodule.map (Matrix.toLin' U) (localDualPadicDenominator L₀ p k) =
      localDualPadicDenominator L₁ p k
    exact localDualPadicDenominator_map_of_local_isometry_matrix
      (L₀ := L₀) (L₁ := L₁) p k hU_unit hU
  exact localDualPadicTransportedIntegralPreimageBasisFamily_mem_localDualQuotientSolutionFamilies_of_equiv
    (L₀ := L₀) (L₁ := L₁) p k (U := U) hU e hDE (by intro x; rfl) hY

lemma localDualPadicTransportedIntegralPreimageBasisFamily_inverse_mem_localDualQuotientSolutionFamilies
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p k : ℕ) [Fact (Nat.Prime p)]
    {U : Matrix (Fin n) (Fin n) ℤ_[p]}
    (hU_unit : IsUnit U)
    (hU : Uᵀ * L₁.pairingMatrix_padic p * U = L₀.pairingMatrix_padic p)
    {Y : Fin n → localDualQuotientTarget
      (padicSubmoduleIntegralPreimage (n := n) p
        (localDualPadicDenominator L₁ p k))}
    (hY : Y ∈ localDualQuotientSolutionFamilies L₁ p k
      (padicSubmoduleIntegralPreimage (n := n) p
        (localDualPadicDenominator L₁ p k))
      (padicSubmoduleIntegralPreimage_localDualPadicDenominator_rank (n := n) L₁ p k)) :
    let D₀ : Submodule ℤ_[p] (Fin n → ℤ_[p]) :=
      localDualPadicDenominator L₀ p k
    let D₁ : Submodule ℤ_[p] (Fin n → ℤ_[p]) :=
      localDualPadicDenominator L₁ p k
    let e := padicMatrixLinearEquivOfIsUnit (n := n) p U hU_unit
    let hDE : Submodule.map e.toLinearMap D₀ = D₁ := by
      change Submodule.map (Matrix.toLin' U) D₀ = D₁
      exact localDualPadicDenominator_map_of_local_isometry_matrix
        (L₀ := L₀) (L₁ := L₁) p k hU_unit hU
    let hED : Submodule.map e.symm.toLinearMap D₁ = D₀ :=
      padicSubmodule_map_symm_eq_of_map_eq (n := n) p D₀ D₁ e hDE
    localDualPadicTransportedIntegralPreimageBasisFamily
        (n := n) L₀ p k D₁ e.symm hED
        (fun i => padicSubmoduleIntegralPreimageQuotientMap (n := n) p D₁ (Y i)) ∈
      localDualQuotientSolutionFamilies L₀ p k
        (padicSubmoduleIntegralPreimage (n := n) p
          (localDualPadicDenominator L₀ p k))
        (padicSubmoduleIntegralPreimage_localDualPadicDenominator_rank (n := n) L₀ p k) := by
  classical
  dsimp
  let D₀ : Submodule ℤ_[p] (Fin n → ℤ_[p]) := localDualPadicDenominator L₀ p k
  let D₁ : Submodule ℤ_[p] (Fin n → ℤ_[p]) := localDualPadicDenominator L₁ p k
  let e := padicMatrixLinearEquivOfIsUnit (n := n) p U hU_unit
  let hDE : Submodule.map e.toLinearMap D₀ = D₁ := by
    change Submodule.map (Matrix.toLin' U) D₀ = D₁
    exact localDualPadicDenominator_map_of_local_isometry_matrix
      (L₀ := L₀) (L₁ := L₁) p k hU_unit hU
  let hED : Submodule.map e.symm.toLinearMap D₁ = D₀ :=
    padicSubmodule_map_symm_eq_of_map_eq (n := n) p D₀ D₁ e hDE
  exact
    localDualPadicTransportedIntegralPreimageBasisFamily_mem_localDualQuotientSolutionFamilies_of_equiv
      (L₀ := L₁) (L₁ := L₀) p k
      (U := U⁻¹)
      (hU := local_isometry_padic_matrix_inv (L₀ := L₀) (L₁ := L₁) p hU_unit hU)
      e.symm hED
      (by
        intro x
        exact padicMatrixLinearEquivOfIsUnit_symm_apply (n := n) p U hU_unit x)
      hY

lemma localDualPadicTransportedIntegralPreimageBasisFamily_injective
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p k : ℕ) [Fact (Nat.Prime p)]
    {U : Matrix (Fin n) (Fin n) ℤ_[p]}
    (hU_unit : IsUnit U)
    (hU : Uᵀ * L₁.pairingMatrix_padic p * U = L₀.pairingMatrix_padic p) :
    let D₀ : Submodule ℤ_[p] (Fin n → ℤ_[p]) :=
      localDualPadicDenominator L₀ p k
    let D₁ : Submodule ℤ_[p] (Fin n → ℤ_[p]) :=
      localDualPadicDenominator L₁ p k
    let e := padicMatrixLinearEquivOfIsUnit (n := n) p U hU_unit
    let hDE : Submodule.map e.toLinearMap D₀ = D₁ := by
      change Submodule.map (Matrix.toLin' U) D₀ = D₁
      exact localDualPadicDenominator_map_of_local_isometry_matrix
        (L₀ := L₀) (L₁ := L₁) p k hU_unit hU
    Function.Injective
      (fun Y : Fin n → localDualQuotientTarget
          (padicSubmoduleIntegralPreimage (n := n) p D₀) =>
        localDualPadicTransportedIntegralPreimageBasisFamily
          (n := n) L₁ p k D₀ e hDE
          (fun i => padicSubmoduleIntegralPreimageQuotientMap (n := n) p D₀ (Y i))) := by
  classical
  dsimp
  let D₀ : Submodule ℤ_[p] (Fin n → ℤ_[p]) := localDualPadicDenominator L₀ p k
  let D₁ : Submodule ℤ_[p] (Fin n → ℤ_[p]) := localDualPadicDenominator L₁ p k
  let e := padicMatrixLinearEquivOfIsUnit (n := n) p U hU_unit
  let hDE : Submodule.map e.toLinearMap D₀ = D₁ := by
    change Submodule.map (Matrix.toLin' U) D₀ = D₁
    exact localDualPadicDenominator_map_of_local_isometry_matrix
      (L₀ := L₀) (L₁ := L₁) p k hU_unit hU
  let hED := padicSubmodule_map_symm_eq_of_map_eq (n := n) p D₀ D₁ e hDE
  intro Y Z hYZ
  ext i
  let Yp : Fin n → ((Fin n → ℤ_[p]) ⧸ D₀) :=
    fun j => padicSubmoduleIntegralPreimageQuotientMap (n := n) p D₀ (Y j)
  let Zp : Fin n → ((Fin n → ℤ_[p]) ⧸ D₀) :=
    fun j => padicSubmoduleIntegralPreimageQuotientMap (n := n) p D₀ (Z j)
  have htarget : padicQuotientTransportedBasisFamily (n := n) p D₀ D₁ e hDE Yp =
      padicQuotientTransportedBasisFamily (n := n) p D₀ D₁ e hDE Zp := by
    ext j
    have hj := congr_fun hYZ j
    have hcast := congrArg
      (padicSubmoduleIntegralPreimageQuotientMap (n := n) p D₁) hj
    rw [padicSubmoduleIntegralPreimageQuotientMap_localDualPadicTransportedIntegralPreimageBasisFamily
      (n := n) L₁ p k D₀ e hDE Yp j] at hcast
    rw [padicSubmoduleIntegralPreimageQuotientMap_localDualPadicTransportedIntegralPreimageBasisFamily
      (n := n) L₁ p k D₀ e hDE Zp j] at hcast
    exact hcast
  have hsource := congrArg
    (padicQuotientTransportedBasisFamily (n := n) p D₁ D₀ e.symm hED) htarget
  have hp_i : Yp i = Zp i := by
    simpa [Yp, Zp, padicQuotientTransportedBasisFamily_symm (n := n) p D₀ D₁ e hDE]
      using congr_fun hsource i
  exact padicSubmoduleIntegralPreimageQuotientMap_injective (n := n) p D₀ hp_i

lemma localDualQuotientCount_eq_of_local_isometry_matrix
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p k : ℕ) [Fact (Nat.Prime p)]
    {U : Matrix (Fin n) (Fin n) ℤ_[p]}
    (hU_unit : IsUnit U)
    (hU : Uᵀ * L₁.pairingMatrix_padic p * U = L₀.pairingMatrix_padic p) :
    localDualQuotientCount L₀ p k =
      localDualQuotientCount L₁ p k := by
  classical
  rw [localDualQuotientCount,
    localDualQuotientCount,
    coordinateLocalDualQuotientCount, coordinateLocalDualQuotientCount]
  let D₀ : Submodule ℤ_[p] (Fin n → ℤ_[p]) := localDualPadicDenominator L₀ p k
  let D₁ : Submodule ℤ_[p] (Fin n → ℤ_[p]) := localDualPadicDenominator L₁ p k
  let S₀ : Submodule ℤ (Fin n → ℤ) := padicSubmoduleIntegralPreimage (n := n) p D₀
  let S₁ : Submodule ℤ (Fin n → ℤ) := padicSubmoduleIntegralPreimage (n := n) p D₁
  let e := padicMatrixLinearEquivOfIsUnit (n := n) p U hU_unit
  let hDE : Submodule.map e.toLinearMap D₀ = D₁ := by
    change Submodule.map (Matrix.toLin' U) D₀ = D₁
    exact localDualPadicDenominator_map_of_local_isometry_matrix
      (L₀ := L₀) (L₁ := L₁) p k hU_unit hU
  let T : (Fin n → localDualQuotientTarget S₀) →
      Fin n → localDualQuotientTarget S₁ :=
    fun Y =>
      localDualPadicTransportedIntegralPreimageBasisFamily
        (n := n) L₁ p k D₀ e hDE
        (fun i => padicSubmoduleIntegralPreimageQuotientMap (n := n) p D₀ (Y i))
  refine Finset.card_bij (fun Y _ => T Y) ?map_mem ?map_inj ?map_surj
  · intro Y hY
    simpa [D₀, D₁, S₀, S₁, e, hDE, T] using
      localDualPadicTransportedIntegralPreimageBasisFamily_mem_localDualQuotientSolutionFamilies
        (L₀ := L₀) (L₁ := L₁) p k (hU_unit := hU_unit) (hU := hU)
        (Y := Y) hY
  · intro Y _ Z _ hYZ
    have hinj :=
      localDualPadicTransportedIntegralPreimageBasisFamily_injective
        (L₀ := L₀) (L₁ := L₁) p k (hU_unit := hU_unit) (hU := hU)
    dsimp [D₀, D₁, S₀, S₁, e, hDE] at hinj
    exact hinj hYZ
  · intro Y hY
    let hED := padicSubmodule_map_symm_eq_of_map_eq (n := n) p D₀ D₁ e hDE
    let Yp : Fin n → ((Fin n → ℤ_[p]) ⧸ D₁) :=
      fun i => padicSubmoduleIntegralPreimageQuotientMap (n := n) p D₁ (Y i)
    let X : Fin n → localDualQuotientTarget S₀ :=
      localDualPadicTransportedIntegralPreimageBasisFamily
        (n := n) L₀ p k D₁ e.symm hED Yp
    refine ⟨X, ?_, ?_⟩
    · simpa [D₀, D₁, S₀, S₁, e, hDE, hED, Yp, X] using
        localDualPadicTransportedIntegralPreimageBasisFamily_inverse_mem_localDualQuotientSolutionFamilies
          (L₀ := L₀) (L₁ := L₁) p k
          (hU_unit := hU_unit) (hU := hU) (Y := Y) hY
    · ext i
      let Xp : Fin n → ((Fin n → ℤ_[p]) ⧸ D₀) :=
        fun j => padicSubmoduleIntegralPreimageQuotientMap (n := n) p D₀ (X j)
      have hXp :
          Xp = padicQuotientTransportedBasisFamily (n := n) p D₁ D₀ e.symm
              (padicSubmodule_map_symm_eq_of_map_eq (n := n) p D₀ D₁ e hDE) Yp := by
        ext j
        exact padicSubmoduleIntegralPreimageQuotientMap_localDualPadicTransportedIntegralPreimageBasisFamily
          (n := n) L₀ p k D₁ e.symm hED Yp j
      have htarget_fun :
          padicQuotientTransportedBasisFamily (n := n) p D₀ D₁ e hDE Xp = Yp := by
        rw [hXp]
        simpa using
          (padicQuotientTransportedBasisFamily_symm (n := n) p D₁ D₀ e.symm
            (padicSubmodule_map_symm_eq_of_map_eq (n := n) p D₀ D₁ e hDE) Yp)
      refine padicSubmoduleIntegralPreimageQuotientMap_injective (n := n) p D₁ ?_
      rw [padicSubmoduleIntegralPreimageQuotientMap_localDualPadicTransportedIntegralPreimageBasisFamily
        (n := n) L₁ p k D₀ e hDE Xp i]
      simpa [Yp, T, Xp] using congr_fun htarget_fun i

lemma localDualQuotientCount_eq_of_isLocallyIsometricAt
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p k : ℕ) [Fact (Nat.Prime p)]
    (h : L₀.IsLocallyIsometricAt L₁ p) :
    localDualQuotientCount L₀ p k =
      localDualQuotientCount L₁ p k := by
  rcases h with ⟨U, hU_unit, hU⟩
  exact localDualQuotientCount_eq_of_local_isometry_matrix
    (L₀ := L₀) (L₁ := L₁) p k (hU_unit := hU_unit) (hU := hU)

lemma localDualQuotientFamilyMatrix_preserves_quadForm_zmod
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {Y : Fin n →
      localDualQuotientTarget (primePowCoordinateSubmodule (n := n) p k)}
    (hY : Y ∈ localDualQuotientSolutionFamilies L p k
      (primePowCoordinateSubmodule (n := n) p k)
      (primePowCoordinateSubmodule_rank (n := n) p k))
    (x : Fin n → ℤ) :
    let X := localDualQuotientFamilyMatrix (n := n) p k Y
    dotProduct
        (X.mulVec (fun j : Fin n => (x j : ZMod (primePowModulus p k : ℕ))))
        ((matrixMod L.pairingMatrix (primePowModulus p k)).mulVec
          (X.mulVec (fun j : Fin n => (x j : ZMod (primePowModulus p k : ℕ))))) =
      (L.quadForm x : ZMod (primePowModulus p k : ℕ)) := by
  classical
  let D : Submodule ℤ (Fin n → ℤ) := primePowCoordinateSubmodule (n := n) p k
  let q : localDualQuotientTarget D := quotientBasisFamilyMap D Y x
  let y : Fin n → ℤ := Quotient.out q
  have hq : quotientBasisFamilyMap D Y x = D.mkQ y := by
    change q = D.mkQ y
    exact (Submodule.Quotient.mk_out q).symm
  have hquad :
      (L.quadForm y : ZMod (primePowModulus p k : ℕ)) =
        (L.quadForm x : ZMod (primePowModulus p k : ℕ)) := by
    exact (mem_localDualQuotientSolutionFamilies_iff.mp hY) x y hq
  have hvec :
      (fun i : Fin n => (y i : ZMod (primePowModulus p k : ℕ))) =
        (localDualQuotientFamilyMatrix (n := n) p k Y).mulVec
          (fun j : Fin n => (x j : ZMod (primePowModulus p k : ℕ))) := by
    have hmat := localDualQuotientFamilyMatrix_mulVec_eq (n := n) p k Y x
    have hqcoord :
        primePowQuotientVector (n := n) p k
            (quotientBasisFamilyMap D Y x) =
          fun i : Fin n => (y i : ZMod (primePowModulus p k : ℕ)) := by
      rw [hq]
      exact primePowQuotientVector_mkQ (n := n) p k y
    exact (hmat.trans hqcoord).symm
  let X := localDualQuotientFamilyMatrix (n := n) p k Y
  calc
    dotProduct
        (X.mulVec (fun j : Fin n => (x j : ZMod (primePowModulus p k : ℕ))))
        ((matrixMod L.pairingMatrix (primePowModulus p k)).mulVec
          (X.mulVec (fun j : Fin n => (x j : ZMod (primePowModulus p k : ℕ))))) =
        dotProduct (fun i : Fin n => (y i : ZMod (primePowModulus p k : ℕ)))
          ((matrixMod L.pairingMatrix (primePowModulus p k)).mulVec
            (fun i : Fin n => (y i : ZMod (primePowModulus p k : ℕ)))) := by
          rw [hvec]
    _ = (L.quadForm y : ZMod (primePowModulus p k : ℕ)) := by
          simp [quadForm_eq_dotProduct, matrixMod, dotProduct, Matrix.mulVec]
    _ = (L.quadForm x : ZMod (primePowModulus p k : ℕ)) := hquad

/-- Polarization for the stored quadratic matrix after reduction modulo a
positive integer.  Since `L.polarGramMatrix = L.pairingMatrix + L.pairingMatrixᵀ`, no
division by two is needed. -/
lemma matrixMod_gram_dotProduct_eq_polarization
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ+)
    (x y : Fin n → ZMod (m : ℕ)) :
    dotProduct x ((matrixMod L.polarGramMatrix m).mulVec y) =
      dotProduct (x + y) ((matrixMod L.pairingMatrix m).mulVec (x + y)) -
        dotProduct x ((matrixMod L.pairingMatrix m).mulVec x) -
        dotProduct y ((matrixMod L.pairingMatrix m).mulVec y) := by
  rw [eq_comm]
  simp [dotProduct, Matrix.mulVec, matrixMod, polarGramMatrix,
    Finset.sum_add_distrib, mul_add, add_mul, sub_eq_add_neg]
  rw [show (∑ x_1, y x_1 * ∑ x_2, ↑(L.pairingMatrix x_1 x_2) * x x_2) =
      ∑ x_1, x x_1 * ∑ x_2, ↑(L.pairingMatrix x_2 x_1) * y x_2 by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    rw [L.form_symm.apply]
    ring]
  ring_nf

/-- A source-normalized quadratic solution family has no kernel beyond the
source denominator. This is the nondegeneracy input behind invertibility of
the residue pairing: if the represented map kills `x`, polarization against
every integral vector forces `x` into `p^k Lambda#`. -/
lemma
    quotientBasisFamilyLinearMap_ker_le_associatedBilinearDualPadicDenominatorIntegralPreimage
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    LinearMap.ker
        (quotientBasisFamilyLinearMap
          (associatedBilinearDualPadicDenominatorIntegralPreimage L p k)
          Y.1) ≤
      associatedBilinearDualPadicDenominatorIntegralPreimage L p k := by
  intro x hx
  let D := associatedBilinearDualPadicDenominatorIntegralPreimage L p k
  let f := quotientBasisFamilyLinearMap D Y.1
  have hfx : f x = 0 := LinearMap.mem_ker.mp hx
  have hsol := mem_localDualQuotientSolutionFamilies_iff.mp Y.2
  have hQx : (L.quadForm x : ZMod (primePowModulus p k : ℕ)) = 0 := by
    have h := hsol x 0 (by
      change f x = D.mkQ 0
      rw [hfx]
      exact (map_zero D.mkQ).symm)
    simpa [quadForm_eq_dotProduct, dotProduct, Matrix.mulVec] using h.symm
  change integralVectorToPadic (n := n) p x ∈
    associatedBilinearDualPadicDenominator L p k
  rw [mem_associatedBilinearDualPadicDenominator_iff]
  intro z
  have hQadd :
      (L.quadForm (z + x) : ZMod (primePowModulus p k : ℕ)) =
        (L.quadForm z : ZMod (primePowModulus p k : ℕ)) := by
    let qz : localDualQuotientTarget D := f z
    let y : Fin n → ℤ := Quotient.out qz
    have hz : f z = D.mkQ y := by
      change qz = D.mkQ y
      exact (Submodule.Quotient.mk_out qz).symm
    have hzx : f (z + x) = D.mkQ y := by
      rw [map_add, hfx, add_zero]
      exact hz
    exact (hsol (z + x) y hzx).symm.trans (hsol z y hz)
  have hzero :
      ((dotProduct z (L.polarGramMatrix.mulVec x) : ℤ) :
          ZMod (primePowModulus p k : ℕ)) = 0 := by
    let m : ℕ+ := primePowModulus p k
    let zmod : Fin n → ZMod (m : ℕ) := fun i => (z i : ZMod (m : ℕ))
    let xmod : Fin n → ZMod (m : ℕ) := fun i => (x i : ZMod (m : ℕ))
    have hpolar := matrixMod_gram_dotProduct_eq_polarization L m zmod xmod
    have hcast_add :
        (fun i => ((z + x) i : ZMod (m : ℕ))) = zmod + xmod := by
      ext i
      simp [zmod, xmod]
    have hquad_cast (v : Fin n → ℤ) :
        dotProduct (fun i => (v i : ZMod (m : ℕ)))
            ((matrixMod L.pairingMatrix m).mulVec
              (fun i => (v i : ZMod (m : ℕ)))) =
          (L.quadForm v : ZMod (m : ℕ)) := by
      simp [quadForm_eq_dotProduct, matrixMod, dotProduct, Matrix.mulVec]
    calc
      ((dotProduct z (L.polarGramMatrix.mulVec x) : ℤ) : ZMod (m : ℕ)) =
          dotProduct zmod ((matrixMod L.polarGramMatrix m).mulVec xmod) := by
            simp [zmod, xmod, matrixMod, dotProduct, Matrix.mulVec]
      _ = 0 := by
        rw [hpolar]
        rw [← hcast_add, hquad_cast, hquad_cast, hquad_cast]
        rw [hQadd, hQx]
        simp
  have hdiv :
      ((p : ℤ_[p]) ^ k ∣
        ((dotProduct z (L.polarGramMatrix.mulVec x) : ℤ) : ℤ_[p])) :=
    (padicInt_primePow_dvd_intCast_iff_zmod_eq_zero p k _).mpr hzero
  simpa [polarGramMatrix_padic, integralVectorToPadic, dotProduct, Matrix.mulVec]
    using hdiv

/-- Every source-normalized quadratic solution family generates its whole
finite quotient. The kernel inclusion above forces its image to have at least
the quotient cardinality, while it is a subgroup of that same finite
quotient. -/
lemma quotientBasisFamilyLinearMap_surjective_associatedBilinear
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    Function.Surjective
      (quotientBasisFamilyLinearMap
        (associatedBilinearDualPadicDenominatorIntegralPreimage L p k)
        Y.1) := by
  classical
  let D := associatedBilinearDualPadicDenominatorIntegralPreimage L p k
  let f := quotientBasisFamilyLinearMap D Y.1
  have hD_rank : Module.finrank ℤ D = n :=
    associatedBilinearDualPadicDenominatorIntegralPreimage_rank
      (n := n) L p k
  have hD_rank' : Module.finrank ℤ D = Module.finrank ℤ (Fin n → ℤ) := by
    simpa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hD_rank
  letI : Finite (localDualQuotientTarget D) :=
    Submodule.finiteQuotientOfFreeOfRankEq (M := Fin n → ℤ) D hD_rank'
  have hker : LinearMap.ker f ≤ D := by
    exact
      quotientBasisFamilyLinearMap_ker_le_associatedBilinearDualPadicDenominatorIntegralPreimage
        L p k Y
  letI : Finite (LinearMap.range f) := Subtype.finite
  letI : Finite ((Fin n → ℤ) ⧸ LinearMap.ker f) :=
    Finite.of_equiv (LinearMap.range f) f.quotKerEquivRange.symm.toEquiv
  have hproduct :
      Nat.card ((Fin n → ℤ) ⧸ LinearMap.ker f) =
        Nat.card (D ⧸ (LinearMap.ker f).comap D.subtype) *
          Nat.card (localDualQuotientTarget D) :=
    localDualQuotientMapOfLE_domain_card_eq_subquotient_mul_codomain_card
      (n := n) hker
  have hquot_pos : 0 < Nat.card ((Fin n → ℤ) ⧸ LinearMap.ker f) :=
    Nat.card_pos
  have hcod_pos : 0 < Nat.card (localDualQuotientTarget D) := Nat.card_pos
  have hsub_pos :
      0 < Nat.card (D ⧸ (LinearMap.ker f).comap D.subtype) := by
    exact Nat.pos_of_mul_pos_right (hproduct ▸ hquot_pos)
  have hquot_range :
      Nat.card ((Fin n → ℤ) ⧸ LinearMap.ker f) =
        Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have hcod_le_range :
      Nat.card (localDualQuotientTarget D) ≤
        Nat.card (LinearMap.range f) := by
    calc
      Nat.card (localDualQuotientTarget D) ≤
          Nat.card (D ⧸ (LinearMap.ker f).comap D.subtype) *
            Nat.card (localDualQuotientTarget D) :=
        Nat.le_mul_of_pos_left _ hsub_pos
      _ = Nat.card ((Fin n → ℤ) ⧸ LinearMap.ker f) := hproduct.symm
      _ = Nat.card (LinearMap.range f) := hquot_range
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨y, -, hy⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  have hlt : Nat.card (LinearMap.range f) <
      Nat.card (localDualQuotientTarget D) :=
    Finite.card_subtype_lt hy
  omega

/-- A source solution family is nondegenerate on residue coordinates. Source
quadratic depth puts the quotient denominator inside `p Z^n`, so surjectivity
on the source quotient descends to surjectivity modulo `p`. -/
lemma
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime_isUnit
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    IsUnit
      (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
        L p k Y) := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  intro v
  choose z hz using fun i => ZMod.intCast_surjective (v i)
  let D := associatedBilinearDualPadicDenominatorIntegralPreimage L p k
  let X :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
      L p k Y
  obtain ⟨x, hx⟩ :=
    quotientBasisFamilyLinearMap_surjective_associatedBilinear L p k Y
      (D.mkQ z)
  refine ⟨fun i => (x i : ZMod p), ?_⟩
  have hmk : D.mkQ (X.mulVec x) = D.mkQ z := by
    rw [associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix_mkQ_mulVec]
    exact hx
  have hsub : X.mulVec x - z ∈ D := by
    rw [← Submodule.Quotient.eq]
    exact hmk
  have hpSub : X.mulVec x - z ∈
      primePowCoordinateSubmodule (n := n) p 1 :=
    associatedBilinearDualPadicDenominatorIntegralPreimage_le_primeCoordinateSubmodule
      L p k hk hsub
  rcases hpSub with ⟨w, hw⟩
  ext i
  have hcast : ((X.mulVec x) i : ZMod p) = (z i : ZMod p) := by
    have hi := congr_fun hw i
    have hi' : (((X.mulVec x - z) i : ℤ) : ZMod p) = 0 := by
      rw [← hi]
      simp [Pi.smul_apply]
    simp only [Pi.sub_apply, Int.cast_sub] at hi'
    exact sub_eq_zero.mp hi'
  calc
    (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
        L p k Y).mulVec (fun i => (x i : ZMod p)) i =
        ((X.mulVec x) i : ZMod p) := by
      simp [associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime,
        X, Matrix.mulVec, dotProduct]
    _ = (z i : ZMod p) := hcast
    _ = v i := hz i

/-- The transpose of the source representative matrix is the residue pairing
matrix occurring in the corrected-lift cross term. -/
lemma
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime_transpose_isUnit
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    IsUnit
      (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
        L p k Y)ᵀ := by
  rw [Matrix.isUnit_transpose]
  exact
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime_isUnit
      L p k hk Y

/-- The concrete invertibility witness used by the source Hensel defect map. -/
@[implicit_reducible]
noncomputable def
    associatedBilinearDualQuotientSolutionFamilyResiduePairingInvertible
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    Invertible
      (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
        L p k Y)ᵀ :=
  (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime_transpose_isUnit
    L p k hk Y).invertible

/-- The source correction-to-defect map with its concrete residue pairing
instance installed. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilyResidueCorrectionQuadraticMap
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    Matrix (Fin n) (Fin n) (ZMod p) →ₗ[ZMod p]
      QuadraticForm (ZMod p) (Fin n → ZMod p) := by
  letI : Invertible
      (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
        L p k Y)ᵀ :=
    associatedBilinearDualQuotientSolutionFamilyResiduePairingInvertible
      L p k hk Y
  exact henselMatrixCorrectionQuadraticMap
    (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
      L p k Y)ᵀ

/-- Reduction modulo `p` identifies the divided integral cross term with the
existing matrix correction-to-quadratic-defect map. The transpose on the
correction matrix converts the row-indexed correction-column convention into
the usual coordinate matrix. -/
lemma
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient_zmod_eq_henselMatrixCorrectionQuadraticMap
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k)
    (x : Fin n → ℤ) :
    (associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient
        L p k Y H x : ZMod p) =
      associatedBilinearDualQuotientSolutionFamilyResidueCorrectionQuadraticMap
        L p k hk Y
        ((associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivMatrix
          L p k (hk.latticeDepth L p k) H)ᵀ)
        (fun i => (x i : ZMod p)) := by
  let X :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
      L p k Y
  let Xp :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
      L p k Y
  let C :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionGramCoordinateQuotientMatrix
      L p k H
  let Hp :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivMatrix
      L p k (hk.latticeDepth L p k) H
  let xp : Fin n → ZMod p := fun i => (x i : ZMod p)
  letI : Invertible Xpᵀ :=
    associatedBilinearDualQuotientSolutionFamilyResiduePairingInvertible
      L p k hk Y
  have hX :
      (fun i => ((X.mulVec x i : ℤ) : ZMod p)) = Xp.mulVec xp := by
    ext i
    simp [X, Xp, xp,
      associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime,
      Matrix.mulVec, dotProduct]
  have hCentry (j i : Fin n) :
      (C j i : ZMod p) = Hp j i := by
    exact
      (associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivMatrix_apply_eq_gramCoordinateQuotient
        L p k (hk.latticeDepth L p k) H j i).symm
  have hC :
      (fun i => (((Cᵀ).mulVec x i : ℤ) : ZMod p)) =
        Hpᵀ.mulVec xp := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, xp]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [hCentry]
  rw [
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient_eq_dotProduct]
  change _ = henselMatrixCorrectionQuadraticMap Xpᵀ Hpᵀ xp
  rw [henselMatrixCorrectionQuadraticMap_apply_eq_dotProduct]
  change
    ((dotProduct (X.mulVec x) ((Cᵀ).mulVec x) : ℤ) : ZMod p) =
      dotProduct (Xpᵀ.mulVec (Hpᵀ.mulVec xp)) xp
  calc
    ((dotProduct (X.mulVec x) ((Cᵀ).mulVec x) : ℤ) : ZMod p) =
        dotProduct
          (fun i => ((X.mulVec x i : ℤ) : ZMod p))
          (fun i => (((Cᵀ).mulVec x i : ℤ) : ZMod p)) := by
      simp [dotProduct]
    _ = dotProduct (Xp.mulVec xp) (Hpᵀ.mulVec xp) := by
      rw [hX, hC]
    _ = dotProduct (Xpᵀ.mulVec (Hpᵀ.mulVec xp)) xp := by
      rw [dotProduct_transpose_mulVec]

/-- A source correction is valid exactly when its transposed residue matrix
lies in the affine correction-to-defect fiber over the negative raw defect. -/
lemma
    isLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection_iff_residueCorrectionQuadraticMap_eq_neg_rawDefect
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (H :
      associatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k) :
    IsLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k Y H ↔
      associatedBilinearDualQuotientSolutionFamilyResidueCorrectionQuadraticMap
          L p k hk Y
          ((associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivMatrix
            L p k (hk.latticeDepth L p k) H)ᵀ) =
        -associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm
          L p k Y := by
  rw [
    isLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection_iff_dividedRawDefect_add_crossTermQuotient
      L p k hk Y H]
  let Hp :=
    (associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivMatrix
      L p k (hk.latticeDepth L p k) H)ᵀ
  let Qraw :=
    associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm
      L p k Y
  let Qcross :=
    associatedBilinearDualQuotientSolutionFamilyResidueCorrectionQuadraticMap
      L p k hk Y Hp
  constructor
  · intro h
    apply QuadraticMap.ext
    intro v
    choose x hx using fun i => (ZMod.intCast_surjective :
      Function.Surjective (Int.cast : ℤ → ZMod p)) (v i)
    have hxv : (fun i => (x i : ZMod p)) = v := by
      ext i
      exact hx i
    have hzero := h x
    push_cast at hzero
    have hresidue : Qraw (fun i => (x i : ZMod p)) +
        Qcross (fun i => (x i : ZMod p)) = 0 := by
      rw [
        associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm_apply_intCast,
        ←
          associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient_zmod_eq_henselMatrixCorrectionQuadraticMap
            L p k hk Y H x]
      exact hzero
    change Qcross v = (-Qraw) v
    rw [← hxv]
    exact eq_neg_of_add_eq_zero_right hresidue
  · intro h x
    push_cast
    let xp : Fin n → ZMod p := fun i => (x i : ZMod p)
    have hpoint := congrArg (fun Q : QuadraticForm (ZMod p) (Fin n → ZMod p) =>
      Q xp) h
    change Qcross xp = -Qraw xp at hpoint
    calc
      ((associatedBilinearDualQuotientSolutionFamilyRawDefect
            L p k Y x / (p : ℤ) ^ k : ℤ) : ZMod p) +
          (associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient
            L p k Y H x : ZMod p) =
          Qraw xp + Qcross xp := by
            rw [
              associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm_apply_intCast,
              ←
                associatedBilinearDualQuotientSolutionFamilySuccCorrectionCrossTermQuotient_zmod_eq_henselMatrixCorrectionQuadraticMap
                  L p k hk Y H x]
      _ = 0 := by
        rw [hpoint]
        exact add_neg_cancel _

/-- Valid source corrections are exactly the affine residue-matrix fiber over
the negative raw defect. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilySuccValidCorrectionEquivResidueFiber
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    {H :
        associatedBilinearDualQuotientSolutionFamilySuccCorrection
          L p k //
      IsLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection
        L p k Y H} ≃
      {M : Matrix (Fin n) (Fin n) (ZMod p) //
        associatedBilinearDualQuotientSolutionFamilyResidueCorrectionQuadraticMap
            L p k hk Y M =
          -associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm
            L p k Y} := by
  let e :=
    associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivMatrix
      L p k (hk.latticeDepth L p k)
  refine
    { toFun := fun H => ⟨(e H.1)ᵀ, ?_⟩
      invFun := fun M => ⟨e.symm M.1ᵀ, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact
      (isLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection_iff_residueCorrectionQuadraticMap_eq_neg_rawDefect
        L p k hk Y H.1).mp H.2
  · apply
      (isLocalDensityAssociatedBilinearDualQuotientSolutionFamilySuccCorrection_iff_residueCorrectionQuadraticMap_eq_neg_rawDefect
        L p k hk Y (e.symm M.1ᵀ)).mpr
    change
      associatedBilinearDualQuotientSolutionFamilyResidueCorrectionQuadraticMap
          L p k hk Y ((e (e.symm M.1ᵀ))ᵀ) =
        -associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm
          L p k Y
    rw [e.apply_symm_apply, Matrix.transpose_transpose]
    exact M.2
  · intro H
    apply Subtype.ext
    change e.symm ((e H.1)ᵀ)ᵀ = H.1
    rw [Matrix.transpose_transpose, e.symm_apply_apply]
  · intro M
    apply Subtype.ext
    change (e (e.symm M.1ᵀ))ᵀ = M.1
    rw [e.apply_symm_apply, Matrix.transpose_transpose]

/-- Every source-normalized adjacent reduction fiber has the quantitative
Hensel cardinality. -/
lemma
    associatedBilinearDualQuotientSolutionFamilySuccReduction_fiber_natCard
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    Nat.card
        {Z : associatedBilinearDualQuotientSolutionFamily
            L p (k + 1) //
          associatedBilinearDualQuotientSolutionFamilySuccReduction
            L p k hk Z = Y} =
      p ^ (n * (n - 1) / 2) := by
  rw [← Nat.card_congr
    (associatedBilinearDualQuotientSolutionFamilySuccCorrectionEquivReductionFiber
      L p k hk Y)]
  rw [Nat.card_congr
    (associatedBilinearDualQuotientSolutionFamilySuccValidCorrectionEquivResidueFiber
      L p k hk Y)]
  let Xp :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZModPrime
      L p k Y
  letI : Invertible Xpᵀ :=
    associatedBilinearDualQuotientSolutionFamilyResiduePairingInvertible
      L p k hk Y
  change Nat.card {M : Matrix (Fin n) (Fin n) (ZMod p) //
      henselMatrixCorrectionQuadraticMap Xpᵀ M =
        -associatedBilinearDualQuotientSolutionFamilyRawDefectQuadraticForm
          L p k Y} = _
  exact natCard_henselMatrixCorrectionQuadraticMap_fiber_zmod p Xpᵀ _

/-- Source-normalized solutions lift through every adjacent Hensel reduction.
The current dyadic quotient requires its separate source/current comparison. -/
theorem
    associatedBilinearDualQuotientSolutionFamilySuccReduction_surjective
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k) :
    Function.Surjective
      (associatedBilinearDualQuotientSolutionFamilySuccReduction
        L p k hk) := by
  intro Y
  have hcard :=
    associatedBilinearDualQuotientSolutionFamilySuccReduction_fiber_natCard
      L p k hk Y
  have hpos :
      0 < Nat.card
        {Z : associatedBilinearDualQuotientSolutionFamily
            L p (k + 1) //
          associatedBilinearDualQuotientSolutionFamilySuccReduction
            L p k hk Z = Y} := by
    rw [hcard]
    exact pow_pos (Fact.out : Nat.Prime p).pos _
  obtain ⟨Z⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨Z.1, Z.2⟩

/-- A chosen compatible tower of source-normalized quotient solutions above
one solution at depth `k`. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilyTowerValue
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    ∀ r : ℕ,
      associatedBilinearDualQuotientSolutionFamily L p (k + r)
  | 0 => by simpa using Y
  | r + 1 =>
      Classical.choose
        (associatedBilinearDualQuotientSolutionFamilySuccReduction_surjective
          L p (k + r) (hk.add L p k r)
          (associatedBilinearDualQuotientSolutionFamilyTowerValue
            L p k hk Y r))

@[simp] lemma
    associatedBilinearDualQuotientSolutionFamilyTowerValue_zero
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    associatedBilinearDualQuotientSolutionFamilyTowerValue
      L p k hk Y 0 = Y := by
  rfl

@[simp] lemma
    associatedBilinearDualQuotientSolutionFamilyTowerValue_succ_reduction
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (r : ℕ) :
    associatedBilinearDualQuotientSolutionFamilySuccReduction
        L p (k + r) (hk.add L p k r)
        (associatedBilinearDualQuotientSolutionFamilyTowerValue
          L p k hk Y (r + 1)) =
      associatedBilinearDualQuotientSolutionFamilyTowerValue
        L p k hk Y r := by
  exact Classical.choose_spec
    (associatedBilinearDualQuotientSolutionFamilySuccReduction_surjective
      L p (k + r) (hk.add L p k r)
      (associatedBilinearDualQuotientSolutionFamilyTowerValue
        L p k hk Y r))

/-- Adjacent representative columns in the chosen tower differ by the
coarser source denominator. -/
lemma
    associatedBilinearDualQuotientSolutionFamilyTowerValue_representative_sub_mem
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (r : ℕ) (j : Fin n) :
    (fun i =>
        associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
            L p (k + (r + 1))
            (associatedBilinearDualQuotientSolutionFamilyTowerValue
              L p k hk Y (r + 1)) i j -
          associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
            L p (k + r)
            (associatedBilinearDualQuotientSolutionFamilyTowerValue
              L p k hk Y r) i j) ∈
      associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + r) := by
  let D :=
    associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + r)
  let E :=
    associatedBilinearDualPadicDenominatorIntegralPreimage L p (k + (r + 1))
  let Z :=
    associatedBilinearDualQuotientSolutionFamilyTowerValue
      L p k hk Y (r + 1)
  let W :=
    associatedBilinearDualQuotientSolutionFamilyTowerValue
      L p k hk Y r
  have hred :
      associatedBilinearDualQuotientSolutionFamilySuccReduction
          L p (k + r) (hk.add L p k r) Z = W :=
    associatedBilinearDualQuotientSolutionFamilyTowerValue_succ_reduction
      L p k hk Y r
  have hcol :
      localDualQuotientMapOfLE (n := n)
          (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
            L p (k + r)) (Z.1 j) =
        W.1 j := by
    have hfun := congrArg Subtype.val hred
    exact congrFun hfun j
  have hmk :
      D.mkQ (Quotient.out (Z.1 j)) =
        D.mkQ (Quotient.out (W.1 j)) := by
    calc
      D.mkQ (Quotient.out (Z.1 j)) =
          localDualQuotientMapOfLE (n := n)
            (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
              L p (k + r))
            (E.mkQ (Quotient.out (Z.1 j))) := by
              exact
                (localDualQuotientMapOfLE_mkQ (n := n)
                  (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
                    L p (k + r)) (Quotient.out (Z.1 j))).symm
      _ = localDualQuotientMapOfLE (n := n)
            (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
              L p (k + r)) (Z.1 j) := by
              exact congrArg
                (localDualQuotientMapOfLE (n := n)
                  (associatedBilinearDualPadicDenominatorIntegralPreimage_succ_le
                    L p (k + r)))
                (Submodule.Quotient.mk_out (Z.1 j))
      _ = W.1 j := hcol
      _ = D.mkQ (Quotient.out (W.1 j)) := by
              exact (Submodule.Quotient.mk_out (W.1 j)).symm
  change Quotient.out (Z.1 j) - Quotient.out (W.1 j) ∈ D
  rw [← Submodule.Quotient.eq]
  exact hmk

/-- A tower representative at any later depth reduces to its initial source
solution modulo the initial associated-bilinear denominator. -/
lemma
    associatedBilinearDualQuotientSolutionFamilyTowerValue_representative_sub_initial_mem
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (r : ℕ) (j : Fin n) :
    (fun i =>
        associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
            L p (k + r)
            (associatedBilinearDualQuotientSolutionFamilyTowerValue
              L p k hk Y r) i j -
          associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
            L p k Y i j) ∈
      associatedBilinearDualPadicDenominatorIntegralPreimage L p k := by
  induction r with
  | zero =>
      simpa only [Nat.add_zero,
        associatedBilinearDualQuotientSolutionFamilyTowerValue_zero,
        sub_self] using
          (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).zero_mem
  | succ r ih =>
      have hstep :=
        associatedBilinearDualQuotientSolutionFamilyTowerValue_representative_sub_mem
          L p k hk Y r j
      have hstep' :
          (fun i =>
              associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
                  L p (k + (r + 1))
                  (associatedBilinearDualQuotientSolutionFamilyTowerValue
                    L p k hk Y (r + 1)) i j -
                associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
                  L p (k + r)
                  (associatedBilinearDualQuotientSolutionFamilyTowerValue
                    L p k hk Y r) i j) ∈
            associatedBilinearDualPadicDenominatorIntegralPreimage L p k :=
        L.associatedBilinearDualPadicDenominatorIntegralPreimage_add_le
          p k r hstep
      have hadd :=
        (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).add_mem
          hstep' ih
      convert hadd using 1
      ext i
      simp only [Pi.add_apply]
      ring

/-- The cofinal denominator bound makes adjacent representative entries
congruent modulo `p^(r+1)`. -/
lemma
    associatedBilinearDualQuotientSolutionFamilyTowerValue_representative_sub_primePow_dvd
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (r : ℕ) (i j : Fin n) :
    (p : ℤ) ^ (r + 1) ∣
      associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
          L p (k + (r + 1))
          (associatedBilinearDualQuotientSolutionFamilyTowerValue
            L p k hk Y (r + 1)) i j -
        associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
          L p (k + r)
          (associatedBilinearDualQuotientSolutionFamilyTowerValue
            L p k hk Y r) i j := by
  let d : Fin n → ℤ := fun a =>
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
        L p (k + (r + 1))
        (associatedBilinearDualQuotientSolutionFamilyTowerValue
          L p k hk Y (r + 1)) a j -
      associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
        L p (k + r)
        (associatedBilinearDualQuotientSolutionFamilyTowerValue
          L p k hk Y r) a j
  have hd :
      d ∈ primePowCoordinateSubmodule (n := n) p (r + 1) :=
    associatedBilinearDualPadicDenominatorIntegralPreimage_add_le_primePowCoordinateSubmodule
      L p k hk r
      (associatedBilinearDualQuotientSolutionFamilyTowerValue_representative_sub_mem
        L p k hk Y r j)
  obtain ⟨z, hz⟩ := hd
  refine ⟨z i, ?_⟩
  have hi := congrFun hz i
  simpa [d, Pi.smul_apply, smul_eq_mul] using hi.symm

/-- One entry of the integral representative sequence selected by the source
solution tower. -/
def
    associatedBilinearDualQuotientSolutionFamilyTowerRepresentativeEntry
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (i j : Fin n) (r : ℕ) : ℤ :=
  associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
    L p (k + r)
    (associatedBilinearDualQuotientSolutionFamilyTowerValue
      L p k hk Y r) i j

lemma
    associatedBilinearDualQuotientSolutionFamilyTowerRepresentativeEntry_succ_sub_dvd
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (i j : Fin n) (r : ℕ) :
    (p : ℤ) ^ r ∣
      associatedBilinearDualQuotientSolutionFamilyTowerRepresentativeEntry
          L p k hk Y i j (r + 1) -
        associatedBilinearDualQuotientSolutionFamilyTowerRepresentativeEntry
          L p k hk Y i j r := by
  exact (pow_dvd_pow (p : ℤ) (Nat.le_succ r)).trans
    (associatedBilinearDualQuotientSolutionFamilyTowerValue_representative_sub_primePow_dvd
      L p k hk Y r i j)

/-- The entrywise p-adic limit of a compatible source quotient-solution
tower. Its finite residues are computed below from the chosen representatives. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    Matrix (Fin n) (Fin n) ℤ_[p] :=
  fun i j =>
    PadicInt.ofIntSeq
      (associatedBilinearDualQuotientSolutionFamilyTowerRepresentativeEntry
        L p k hk Y i j)
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
        (associatedBilinearDualQuotientSolutionFamilyTowerRepresentativeEntry
          L p k hk Y i j)
        p
        (associatedBilinearDualQuotientSolutionFamilyTowerRepresentativeEntry_succ_sub_dvd
          L p k hk Y i j))

lemma
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit_toZModPow
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (r : ℕ) (i j : Fin n) :
    PadicInt.toZModPow r
        (associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit
          L p k hk Y i j) =
      associatedBilinearDualQuotientSolutionFamilyTowerRepresentativeEntry
        L p k hk Y i j r := by
  exact
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
      (associatedBilinearDualQuotientSolutionFamilyTowerRepresentativeEntry
        L p k hk Y i j)
      p
      (associatedBilinearDualQuotientSolutionFamilyTowerRepresentativeEntry_succ_sub_dvd
        L p k hk Y i j)
      r

/-- Matrix form of the finite-reduction compatibility of the p-adic tower
limit. -/
lemma
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit_map_toZModPow
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (r : ℕ) :
    (associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit
        L p k hk Y).map (PadicInt.toZModPow r) =
      (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
        L p (k + r)
        (associatedBilinearDualQuotientSolutionFamilyTowerValue
          L p k hk Y r)).map Int.cast := by
  ext i j
  exact
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit_toZModPow
      L p k hk Y r i j

/-- The source-normalized associated-bilinear count satisfies the adjacent
quantitative Hensel recurrence. -/
lemma associatedBilinearDualQuotientCount_succ_eq
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k) :
    associatedBilinearDualQuotientCount L p (k + 1) =
      p ^ (n * (n - 1) / 2) *
        associatedBilinearDualQuotientCount L p k := by
  rw [associatedBilinearDualQuotientCount_eq_natCard_solutionFamily,
    associatedBilinearDualQuotientCount_eq_natCard_solutionFamily]
  have hcount := nat_card_eq_mul_of_fiber_card
    (associatedBilinearDualQuotientSolutionFamilySuccReduction
      L p k hk)
    (p ^ (n * (n - 1) / 2))
    (associatedBilinearDualQuotientSolutionFamilySuccReduction_fiber_natCard
      L p k hk)
  simpa [Nat.mul_comm] using hcount

/-- Quantitative Hensel lifting for the finite local-dual quotient count
(R. Schulze-Pillot, *Lecture Notes on Quadratic Forms and their Arithmetic*:
the quantitative Hensel lemma and its corollary on congruence subgroups).

For the associated-bilinear `2F`-dual count, every valid map at depth `k` has
exactly `p^(n(n-1)/2)` lifts at depth `k+1`.  The count here uses the
half-polar `F`-dual.  At odd primes the duals agree.  At `p = 2` the two counts
differ by the depth-independent factor `2^(n*n)` once the associated-bilinear
quadratic-depth condition holds (it is part of `IsLocalDensityHenselExponent`),
so the same total-count recurrence holds, although the dyadic reduction map for
this count does not have uniform fibers. -/
lemma localDualQuotientCount_succ_eq
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityHenselExponent L p k) :
    localDualQuotientCount L p (k + 1) =
      p ^ (n * (n - 1) / 2) *
        localDualQuotientCount L p k := by
  by_cases hp : p = 2
  · subst p
    rw [localDualQuotientCount_eq_two_pow_mul_associatedBilinear_dyadic
        L (k + 1) (hk.succ L 2 k),
      associatedBilinearDualQuotientCount_succ_eq
        L 2 k hk.associated_bilinear_quadratic_depth,
      localDualQuotientCount_eq_two_pow_mul_associatedBilinear_dyadic
        L k hk]
    ac_rfl
  · rw [← associatedBilinearDualQuotientCount_eq_current_of_ne_two
        L p (k + 1) hp,
      ← associatedBilinearDualQuotientCount_eq_current_of_ne_two
        L p k hp]
    exact associatedBilinearDualQuotientCount_succ_eq
      L p k hk.associated_bilinear_quadratic_depth

lemma matrix_mulVec_basisFun
    {R : Type*} [Semiring R]
    (X : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    X.mulVec ((Pi.basisFun R (Fin n)) i) = X.col i := by
  classical
  ext a
  rw [Matrix.mulVec, dotProduct]
  change (∑ x, X a x * ((Pi.basisFun R (Fin n)) i x)) = X a i
  calc
    (∑ x, X a x * ((Pi.basisFun R (Fin n)) i x)) =
        X a i * ((Pi.basisFun R (Fin n)) i i) := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro b _ hb
        have hbasis : ((Pi.basisFun R (Fin n)) i b) = 0 := by
          simp [Pi.basisFun, hb]
        rw [hbasis]
        simp
      · intro hi
        simp at hi
    _ = X a i := by simp

lemma dotProduct_basisFun
    {R : Type*} [Semiring R]
    (v : Fin n → R) (i : Fin n) :
    dotProduct ((Pi.basisFun R (Fin n)) i) v = v i := by
  classical
  rw [dotProduct]
  change (∑ x, ((Pi.basisFun R (Fin n)) i x) * v x) = v i
  calc
    (∑ x, ((Pi.basisFun R (Fin n)) i x) * v x) =
        ((Pi.basisFun R (Fin n)) i i) * v i := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro b _ hb
        have hbasis : ((Pi.basisFun R (Fin n)) i b) = 0 := by
          simp [Pi.basisFun, hb]
        rw [hbasis]
        simp
      · intro hi
        simp at hi
    _ = v i := by simp

lemma matrix_transpose_mul_mul_entry_eq_dotProduct_mulVec
    {R : Type*} [CommSemiring R]
    (A X : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Xᵀ * A * X) i j =
      dotProduct (X.col i) (A.mulVec (X.col j)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [mul_comm, mul_left_comm]

lemma matrix_entry_eq_dotProduct_mulVec_basis
    {R : Type*} [CommSemiring R]
    (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    A i j =
      dotProduct ((Pi.basisFun R (Fin n)) i)
        (A.mulVec ((Pi.basisFun R (Fin n)) j)) := by
  rw [matrix_mulVec_basisFun A j, dotProduct_basisFun]
  rfl

/-- Any integral representative matrix of a source-normalized solution family
preserves the associated Gram matrix modulo the working prime power. -/
lemma
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZMod_gram_congruence
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZMod
        L p k Y)ᵀ *
        matrixMod L.polarGramMatrix (primePowModulus p k) *
          associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZMod
            L p k Y =
      matrixMod L.polarGramMatrix (primePowModulus p k) := by
  classical
  let m : ℕ+ := primePowModulus p k
  let X :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZMod
      L p k Y
  ext i j
  change (Xᵀ * matrixMod L.polarGramMatrix m * X) i j =
    matrixMod L.polarGramMatrix m i j
  let eℤ : Fin n → Fin n → ℤ := fun i => (Pi.basisFun ℤ (Fin n)) i
  let e : Fin n → Fin n → ZMod (m : ℕ) :=
    fun i => (Pi.basisFun (ZMod (m : ℕ)) (Fin n)) i
  have he_cast (i : Fin n) :
      (fun a : Fin n => ((eℤ i a : ℤ) : ZMod (primePowModulus p k : ℕ))) =
        e i := by
    ext a
    by_cases h : a = i
    · subst a
      simp [e, eℤ]
    · simp [e, eℤ, Pi.single_eq_of_ne h]
  have he_add_cast (i j : Fin n) :
      (fun a : Fin n => (((eℤ i + eℤ j) a : ℤ) :
        ZMod (primePowModulus p k : ℕ))) =
        e i + e j := by
    ext a
    rw [Pi.add_apply, Pi.add_apply, Int.cast_add]
    rw [congr_fun (he_cast i) a, congr_fun (he_cast j) a]
  have hmul (x : Fin n → ℤ) :
      X.mulVec (fun a => (x a : ZMod (m : ℕ))) =
        fun a =>
          (((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
            L p k Y).mulVec x a : ℤ) : ZMod (m : ℕ)) := by
    ext a
    simp [X,
      associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZMod,
      Matrix.mulVec, dotProduct]
  have hquad (x : Fin n → ℤ) :
      dotProduct
          (X.mulVec (fun a : Fin n => (x a : ZMod (m : ℕ))))
          ((matrixMod L.pairingMatrix m).mulVec
            (X.mulVec (fun a : Fin n => (x a : ZMod (m : ℕ))))) =
        dotProduct (fun a : Fin n => (x a : ZMod (m : ℕ)))
          ((matrixMod L.pairingMatrix m).mulVec
            (fun a : Fin n => (x a : ZMod (m : ℕ)))) := by
    rw [hmul]
    simpa [quadForm_eq_dotProduct, matrixMod, dotProduct, Matrix.mulVec]
      using
        associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix_quadForm_zmod
          L p k Y x
  have hquad_i := hquad (eℤ i)
  have hquad_j := hquad (eℤ j)
  have hquad_add := hquad (eℤ i + eℤ j)
  rw [he_cast i] at hquad_i
  rw [he_cast j] at hquad_j
  rw [he_add_cast i j] at hquad_add
  have hcol_i : X.mulVec (e i) = X.col i := matrix_mulVec_basisFun X i
  have hcol_j : X.mulVec (e j) = X.col j := matrix_mulVec_basisFun X j
  have hpolar_X :=
    matrixMod_gram_dotProduct_eq_polarization L m
      (X.mulVec (e i)) (X.mulVec (e j))
  have hpolar_e := matrixMod_gram_dotProduct_eq_polarization L m (e i) (e j)
  have hdot :
      dotProduct (X.mulVec (e i))
          ((matrixMod L.polarGramMatrix m).mulVec (X.mulVec (e j))) =
        dotProduct (e i) ((matrixMod L.polarGramMatrix m).mulVec (e j)) := by
    rw [hpolar_X, hpolar_e]
    rw [← Matrix.mulVec_add, hquad_add, hquad_i, hquad_j]
  calc
    (Xᵀ * matrixMod L.polarGramMatrix m * X) i j =
        dotProduct (X.col i)
          ((matrixMod L.polarGramMatrix m).mulVec (X.col j)) := by
          exact matrix_transpose_mul_mul_entry_eq_dotProduct_mulVec
            (matrixMod L.polarGramMatrix m) X i j
    _ = dotProduct (X.mulVec (e i))
          ((matrixMod L.polarGramMatrix m).mulVec (X.mulVec (e j))) := by
          rw [hcol_i, hcol_j]
    _ = dotProduct (e i) ((matrixMod L.polarGramMatrix m).mulVec (e j)) := hdot
    _ = matrixMod L.polarGramMatrix m i j := by
          exact (matrix_entry_eq_dotProduct_mulVec_basis
            (matrixMod L.polarGramMatrix m) i j).symm

set_option backward.isDefEq.respectTransparency false in
/-- The compatible source-solution tower converges to an exact Gram isometry
over the p-adic integers. -/
lemma
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit_preserves_gram
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    (associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit
        L p k hk Y)ᵀ *
        L.polarGramMatrix_padic p *
      associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit
        L p k hk Y =
      L.polarGramMatrix_padic p := by
  let X :=
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit
      L p k hk Y
  ext i j
  apply PadicInt.ext_of_toZModPow.mp
  intro r
  let Z :=
    associatedBilinearDualQuotientSolutionFamilyTowerValue
      L p k hk Y r
  let R :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
      L p (k + r) Z
  have hfull :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZMod_gram_congruence
      L p (k + r) Z
  have hpow : p ^ r ∣ p ^ (k + r) :=
    pow_dvd_pow p (by omega : r ≤ k + r)
  let f : ZMod (p ^ (k + r)) →+* ZMod (p ^ r) :=
    ZMod.castHom hpow _
  have hf (z : ℤ) :
      f (z : ZMod (p ^ (k + r))) = (z : ZMod (p ^ r)) := by
    rw [ZMod.castHom_apply]
    exact ZMod.cast_intCast hpow z
  have hfun :
      (⇑f ∘ (Int.cast : ℤ → ZMod (p ^ (k + r)))) =
        (Int.cast : ℤ → ZMod (p ^ r)) := by
    funext z
    exact hf z
  have hcast := congrArg (RingHom.mapMatrix f) hfull
  have hfinite :
      (R.map (Int.castRingHom (ZMod (p ^ r))))ᵀ *
          L.polarGramMatrix.map (Int.castRingHom (ZMod (p ^ r))) *
        R.map (Int.castRingHom (ZMod (p ^ r))) =
        L.polarGramMatrix.map (Int.castRingHom (ZMod (p ^ r))) := by
    change
      (((associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZMod
          L p (k + r) Z)ᵀ *
          matrixMod L.polarGramMatrix (primePowModulus p (k + r)) *
        associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZMod
          L p (k + r) Z).map f) =
        (matrixMod L.polarGramMatrix (primePowModulus p (k + r))).map f at hcast
    rw [Matrix.map_mul (f := f), Matrix.map_mul (f := f),
      Matrix.transpose_map] at hcast
    simp only [Z,
      associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrixZMod,
      matrixMod, Matrix.map_map] at hcast
    rw [hfun] at hcast
    simpa [R, Z] using hcast
  have hX :
      X.map (PadicInt.toZModPow r) =
        R.map (Int.castRingHom (ZMod (p ^ r))) := by
    exact
      associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit_map_toZModPow
        L p k hk Y r
  have hG :
      (L.polarGramMatrix_padic p).map (PadicInt.toZModPow r) =
        L.polarGramMatrix.map (Int.castRingHom (ZMod (p ^ r))) := by
    ext a b
    simp [polarGramMatrix_padic]
  change
    (((Xᵀ * L.polarGramMatrix_padic p * X).map
      (PadicInt.toZModPow r)) i j) =
      (((L.polarGramMatrix_padic p).map (PadicInt.toZModPow r)) i j)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hX, hG]
  exact congr_fun (congr_fun hfinite i) j

/-- The source-solution tower limit preserves the original integral form over
the p-adic integers. This uses cancellation by `2`, not division by `2`, so it
also applies at the dyadic prime. -/
lemma
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit_preserves_form
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    (associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit
        L p k hk Y)ᵀ *
        L.pairingMatrix_padic p *
      associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit
        L p k hk Y =
      L.pairingMatrix_padic p := by
  have h :=
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit_preserves_gram
      L p k hk Y
  rw [L.polarGramMatrix_padic_eq_two_smul_pairingMatrix_padic p] at h
  rw [Matrix.mul_smul, Matrix.smul_mul] at h
  exact (smul_right_injective (Matrix (Fin n) (Fin n) ℤ_[p])
    (by norm_num : (2 : ℤ_[p]) ≠ 0)) h

lemma polarGramMatrix_padic_det
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (L.polarGramMatrix_padic p).det = (L.polarDeterminant : ℤ_[p]) := by
  calc
    (L.polarGramMatrix_padic p).det =
        Int.castRingHom ℤ_[p] L.polarGramMatrix.det := by
          exact (RingHom.map_det (Int.castRingHom ℤ_[p]) L.polarGramMatrix).symm
    _ = (L.polarDeterminant : ℤ_[p]) := rfl

/-- The p-adic limit of a compatible source-solution tower is an invertible
matrix over the p-adic integers. -/
lemma
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit_isUnit
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    IsUnit
      (associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit
        L p k hk Y) := by
  let X :=
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit
      L p k hk Y
  rw [Matrix.isUnit_iff_isUnit_det]
  have hpres :=
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit_preserves_gram
      L p k hk Y
  have hdet := congrArg Matrix.det hpres
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  have hGne : (L.polarGramMatrix_padic p).det ≠ 0 := by
    rw [polarGramMatrix_padic_det]
    exact Int.cast_ne_zero.mpr L.polarDeterminant_pos.ne'
  have hsquare : X.det * X.det = 1 := by
    apply mul_right_cancel₀ hGne
    simpa [X, mul_assoc, mul_comm, mul_left_comm] using hdet
  exact IsUnit.of_mul_eq_one X.det hsquare

lemma localDualQuotientFamilyMatrix_mem_gramCongruenceSolutionMatrices
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {Y : Fin n →
      localDualQuotientTarget (primePowCoordinateSubmodule (n := n) p k)}
    (hY : Y ∈ localDualQuotientSolutionFamilies L p k
      (primePowCoordinateSubmodule (n := n) p k)
      (primePowCoordinateSubmodule_rank (n := n) p k)) :
    localDualQuotientFamilyMatrix (n := n) p k Y ∈
      gramCongruenceSolutionMatrices L p k := by
  classical
  rw [mem_gramCongruenceSolutionMatrices_iff]
  let m : ℕ+ := primePowModulus p k
  let X := localDualQuotientFamilyMatrix (n := n) p k Y
  ext i j
  let eℤ : Fin n → Fin n → ℤ := fun i => (Pi.basisFun ℤ (Fin n)) i
  let e : Fin n → Fin n → ZMod (m : ℕ) :=
    fun i => (Pi.basisFun (ZMod (m : ℕ)) (Fin n)) i
  have he_cast (i : Fin n) :
      (fun a : Fin n => ((eℤ i a : ℤ) : ZMod (primePowModulus p k : ℕ))) =
        e i := by
    ext a
    by_cases h : a = i
    · subst a
      simp [e, eℤ]
    · simp [e, eℤ, Pi.single_eq_of_ne h]
  have he_add_cast (i j : Fin n) :
      (fun a : Fin n => (((eℤ i + eℤ j) a : ℤ) :
        ZMod (primePowModulus p k : ℕ))) =
        e i + e j := by
    ext a
    rw [Pi.add_apply, Pi.add_apply, Int.cast_add]
    rw [congr_fun (he_cast i) a, congr_fun (he_cast j) a]
  have hquad (x : Fin n → ℤ) :
      dotProduct
          (X.mulVec (fun a : Fin n => (x a : ZMod (m : ℕ))))
          ((matrixMod L.pairingMatrix m).mulVec
            (X.mulVec (fun a : Fin n => (x a : ZMod (m : ℕ))))) =
        dotProduct (fun a : Fin n => (x a : ZMod (m : ℕ)))
          ((matrixMod L.pairingMatrix m).mulVec
            (fun a : Fin n => (x a : ZMod (m : ℕ)))) := by
    have h := localDualQuotientFamilyMatrix_preserves_quadForm_zmod
      (L := L) (p := p) (k := k) (Y := Y) hY x
    simpa [X, m, quadForm_eq_dotProduct, matrixMod, dotProduct, Matrix.mulVec]
      using h
  have hquad_i :
      dotProduct (X.mulVec (e i))
          ((matrixMod L.pairingMatrix m).mulVec (X.mulVec (e i))) =
        dotProduct (e i) ((matrixMod L.pairingMatrix m).mulVec (e i)) := by
    have h := hquad (eℤ i)
    rw [he_cast i] at h
    exact h
  have hquad_j :
      dotProduct (X.mulVec (e j))
          ((matrixMod L.pairingMatrix m).mulVec (X.mulVec (e j))) =
        dotProduct (e j) ((matrixMod L.pairingMatrix m).mulVec (e j)) := by
    have h := hquad (eℤ j)
    rw [he_cast j] at h
    exact h
  have hquad_add :
      dotProduct (X.mulVec (e i + e j))
          ((matrixMod L.pairingMatrix m).mulVec (X.mulVec (e i + e j))) =
        dotProduct (e i + e j)
          ((matrixMod L.pairingMatrix m).mulVec (e i + e j)) := by
    have h := hquad (eℤ i + eℤ j)
    rw [he_add_cast i j] at h
    exact h
  have hcol_i : X.mulVec (e i) = X.col i := by
    exact matrix_mulVec_basisFun X i
  have hcol_j : X.mulVec (e j) = X.col j := by
    exact matrix_mulVec_basisFun X j
  have hpolar_X :=
    matrixMod_gram_dotProduct_eq_polarization L m (X.mulVec (e i)) (X.mulVec (e j))
  have hpolar_e :=
    matrixMod_gram_dotProduct_eq_polarization L m (e i) (e j)
  have hdot :
      dotProduct (X.mulVec (e i)) ((matrixMod L.polarGramMatrix m).mulVec (X.mulVec (e j))) =
        dotProduct (e i) ((matrixMod L.polarGramMatrix m).mulVec (e j)) := by
    rw [hpolar_X, hpolar_e]
    rw [← Matrix.mulVec_add, hquad_add, hquad_i, hquad_j]
  calc
    (Xᵀ * matrixMod L.polarGramMatrix (primePowModulus p k) * X) i j =
        dotProduct (X.col i) ((matrixMod L.polarGramMatrix m).mulVec (X.col j)) := by
          simpa [X, m] using
            matrix_transpose_mul_mul_entry_eq_dotProduct_mulVec
              (matrixMod L.polarGramMatrix m) X i j
    _ = dotProduct (X.mulVec (e i)) ((matrixMod L.polarGramMatrix m).mulVec (X.mulVec (e j))) := by
          rw [hcol_i, hcol_j]
    _ = dotProduct (e i) ((matrixMod L.polarGramMatrix m).mulVec (e j)) := hdot
    _ = matrixMod L.polarGramMatrix (primePowModulus p k) i j := by
          exact (matrix_entry_eq_dotProduct_mulVec_basis
            (matrixMod L.polarGramMatrix m) i j).symm

/-- Lifting the columns of a matrix over `ZMod (p^k)` gives a family of
quotient basis images in `ℤ^n / p^kℤ^n`. -/
def localDualQuotientLiftFamily
    (p k : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ))) :
    Fin n →
      localDualQuotientTarget (primePowCoordinateSubmodule (n := n) p k) :=
  fun j =>
    (primePowCoordinateSubmodule (n := n) p k).mkQ
      (fun i : Fin n => ((X i j).val : ℤ))

@[simp] lemma localDualQuotientFamilyMatrix_liftFamily
    (p k : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ))) :
    localDualQuotientFamilyMatrix (n := n) p k
        (localDualQuotientLiftFamily (n := n) p k X) = X := by
  ext i j
  rw [localDualQuotientFamilyMatrix, localDualQuotientLiftFamily,
    primePowQuotientCoordinate_mkQ]
  exact_mod_cast ZMod.natCast_zmod_val (X i j)

@[simp] lemma localDualQuotientLiftFamily_familyMatrix
    (p k : ℕ) [Fact (Nat.Prime p)]
    (Y : Fin n →
      localDualQuotientTarget (primePowCoordinateSubmodule (n := n) p k)) :
    localDualQuotientLiftFamily (n := n) p k
        (localDualQuotientFamilyMatrix (n := n) p k Y) = Y := by
  ext j
  apply primePowQuotientVector_injective (n := n) p k
  ext i
  rw [localDualQuotientLiftFamily, primePowQuotientVector_mkQ]
  change (((primePowQuotientCoordinate (n := n) p k i (Y j)).val : ℤ) :
      ZMod (primePowModulus p k : ℕ)) =
    primePowQuotientVector (n := n) p k (Y j) i
  rw [primePowQuotientVector]
  exact_mod_cast ZMod.natCast_zmod_val
    (primePowQuotientCoordinate (n := n) p k i (Y j))

lemma dotProduct_mulVec_congr_of_matrix_conj
    {R : Type*} [CommSemiring R]
    {A X : Matrix (Fin n) (Fin n) R} {v : Fin n → R}
    (hX : Xᵀ * A * X = A) :
    dotProduct (X.mulVec v) (A.mulVec (X.mulVec v)) =
      dotProduct v (A.mulVec v) := by
  calc
    dotProduct (X.mulVec v) (A.mulVec (X.mulVec v)) =
        (X.mulVec v) ᵥ* A ⬝ᵥ X.mulVec v := by
          rw [Matrix.dotProduct_mulVec]
    _ = ((v ᵥ* Xᵀ) ᵥ* A) ⬝ᵥ X.mulVec v := by
          rw [Matrix.vecMul_transpose]
    _ = (v ᵥ* (Xᵀ * A)) ⬝ᵥ X.mulVec v := by
          rw [Matrix.vecMul_vecMul]
    _ = ((v ᵥ* (Xᵀ * A)) ᵥ* X) ⬝ᵥ v := by
          rw [Matrix.dotProduct_mulVec]
    _ = (v ᵥ* (Xᵀ * A * X)) ⬝ᵥ v := by
          rw [Matrix.vecMul_vecMul]
    _ = dotProduct v ((Xᵀ * A * X).mulVec v) := by
          rw [Matrix.dotProduct_mulVec]
    _ = dotProduct v (A.mulVec v) := by rw [hX]

lemma matrix_conj_smul
    {R : Type*} [CommSemiring R] (c : R)
    (A X : Matrix (Fin n) (Fin n) R) :
    Xᵀ * (c • A) * X = c • (Xᵀ * A * X) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

lemma matrix_eq_of_smul_eq_smul_of_isUnit
    {R : Type*} [CommSemiring R] {c : R} (hc : IsUnit c)
    {A B : Matrix (Fin n) (Fin n) R} (h : c • A = c • B) :
    A = B := by
  ext i j
  have hij := congr_fun (congr_fun h i) j
  exact hc.mul_left_cancel (by simpa [smul_eq_mul] using hij)

lemma matrixMod_polarGramMatrix_eq_two_smul_pairingMatrix
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ+) :
    matrixMod L.polarGramMatrix m =
      (2 : ZMod (m : ℕ)) • matrixMod L.pairingMatrix m := by
  ext i j
  simp [matrixMod, polarGramMatrix, Matrix.transpose_apply, L.form_symm.apply, two_mul]

lemma two_isUnit_zmod_primePow
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    IsUnit (2 : ZMod (primePowModulus p k : ℕ)) := by
  have hp_prime : Nat.Prime p := Fact.out
  have hp_not_dvd_two : ¬ p ∣ 2 := by
    intro hp_dvd
    have hp_eq_two_rev : 2 = p :=
      (Nat.Prime.dvd_iff_eq Nat.prime_two hp_prime.ne_one).mp hp_dvd
    exact hp_two hp_eq_two_rev.symm
  have hpcoprime : p.Coprime 2 :=
    hp_prime.coprime_iff_not_dvd.mpr hp_not_dvd_two
  have h2coprimep : (2 : ℕ).Coprime p := hpcoprime.symm
  have h2coprimepow : (2 : ℕ).Coprime (p ^ k) :=
    Nat.Coprime.pow_right k h2coprimep
  simpa [primePowModulus] using
    (ZMod.isUnit_iff_coprime 2 (p ^ k)).mpr h2coprimepow

lemma pairingMatrix_congruence_of_mem_gramCongruenceSolutionMatrices_odd
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ))}
    (hX : X ∈ gramCongruenceSolutionMatrices L p k) :
    Xᵀ * matrixMod L.pairingMatrix (primePowModulus p k) * X =
      matrixMod L.pairingMatrix (primePowModulus p k) := by
  let m : ℕ+ := primePowModulus p k
  have hXeq :
      Xᵀ * matrixMod L.polarGramMatrix m * X = matrixMod L.polarGramMatrix m :=
    mem_gramCongruenceSolutionMatrices_iff.mp hX
  have hgram := matrixMod_polarGramMatrix_eq_two_smul_pairingMatrix L m
  have hscalar :
      (2 : ZMod (m : ℕ)) •
          (Xᵀ * matrixMod L.pairingMatrix m * X) =
        (2 : ZMod (m : ℕ)) • matrixMod L.pairingMatrix m := by
    calc
      (2 : ZMod (m : ℕ)) •
          (Xᵀ * matrixMod L.pairingMatrix m * X) =
          Xᵀ * ((2 : ZMod (m : ℕ)) • matrixMod L.pairingMatrix m) * X := by
            exact (matrix_conj_smul (n := n)
              (2 : ZMod (m : ℕ)) (matrixMod L.pairingMatrix m) X).symm
      _ = Xᵀ * matrixMod L.polarGramMatrix m * X := by rw [← hgram]
      _ = matrixMod L.polarGramMatrix m := hXeq
      _ = (2 : ZMod (m : ℕ)) • matrixMod L.pairingMatrix m := hgram
  exact matrix_eq_of_smul_eq_smul_of_isUnit (n := n)
    (two_isUnit_zmod_primePow p k hp_two) hscalar

lemma localDualQuotientLiftFamily_mem_localDualQuotientSolutionFamilies_of_pairingMatrix
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ))}
    (hX : Xᵀ * matrixMod L.pairingMatrix (primePowModulus p k) * X =
      matrixMod L.pairingMatrix (primePowModulus p k)) :
    localDualQuotientLiftFamily (n := n) p k X ∈
      localDualQuotientSolutionFamilies L p k
        (primePowCoordinateSubmodule (n := n) p k)
        (primePowCoordinateSubmodule_rank (n := n) p k) := by
  classical
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  let D : Submodule ℤ (Fin n → ℤ) := primePowCoordinateSubmodule (n := n) p k
  let Y : Fin n → localDualQuotientTarget D :=
    localDualQuotientLiftFamily (n := n) p k X
  let m : ℕ+ := primePowModulus p k
  have hmatrix : localDualQuotientFamilyMatrix (n := n) p k Y = X := by
    exact localDualQuotientFamilyMatrix_liftFamily (n := n) p k X
  have hvec :
      (fun i : Fin n => (y i : ZMod (m : ℕ))) =
        X.mulVec (fun j : Fin n => (x j : ZMod (m : ℕ))) := by
    have hmap := localDualQuotientFamilyMatrix_mulVec_eq (n := n) p k Y x
    have hq := congrArg (primePowQuotientVector (n := n) p k) hxy
    calc
      (fun i : Fin n => (y i : ZMod (m : ℕ))) =
          primePowQuotientVector (n := n) p k (D.mkQ y) := by
            exact (primePowQuotientVector_mkQ (n := n) p k y).symm
      _ = primePowQuotientVector (n := n) p k
            (quotientBasisFamilyMap D Y x) := by
            exact hq.symm
      _ = (localDualQuotientFamilyMatrix (n := n) p k Y).mulVec
            (fun j : Fin n => (x j : ZMod (m : ℕ))) := by
            exact hmap.symm
      _ = X.mulVec (fun j : Fin n => (x j : ZMod (m : ℕ))) := by
            rw [hmatrix]
  calc
    (L.quadForm y : ZMod (primePowModulus p k : ℕ)) =
        dotProduct (fun i : Fin n => (y i : ZMod (m : ℕ)))
          ((matrixMod L.pairingMatrix m).mulVec
            (fun i : Fin n => (y i : ZMod (m : ℕ)))) := by
          simp [m, quadForm_eq_dotProduct, matrixMod, dotProduct, Matrix.mulVec]
    _ = dotProduct
          (X.mulVec (fun j : Fin n => (x j : ZMod (m : ℕ))))
          ((matrixMod L.pairingMatrix m).mulVec
            (X.mulVec (fun j : Fin n => (x j : ZMod (m : ℕ))))) := by
          rw [hvec]
    _ = dotProduct (fun j : Fin n => (x j : ZMod (m : ℕ)))
          ((matrixMod L.pairingMatrix m).mulVec
            (fun j : Fin n => (x j : ZMod (m : ℕ)))) := by
          exact dotProduct_mulVec_congr_of_matrix_conj (n := n) (hX := hX)
    _ = (L.quadForm x : ZMod (primePowModulus p k : ℕ)) := by
          simp [m, quadForm_eq_dotProduct, matrixMod, dotProduct, Matrix.mulVec]

lemma localDualQuotientLiftFamily_mem_localDualQuotientSolutionFamilies_of_gram_odd
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ))}
    (hX : X ∈ gramCongruenceSolutionMatrices L p k) :
    localDualQuotientLiftFamily (n := n) p k X ∈
      localDualQuotientSolutionFamilies L p k
        (primePowCoordinateSubmodule (n := n) p k)
        (primePowCoordinateSubmodule_rank (n := n) p k) := by
  exact
    localDualQuotientLiftFamily_mem_localDualQuotientSolutionFamilies_of_pairingMatrix
      (L := L) (p := p) (k := k) (X := X)
      (pairingMatrix_congruence_of_mem_gramCongruenceSolutionMatrices_odd
        (L := L) (p := p) (k := k) hp_two hX)

lemma localDualQuotientLiftFamilyOfLE_mem_localDualQuotientSolutionFamilies_of_gram_odd
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    {E : Submodule ℤ (Fin n → ℤ)}
    (hPE : primePowCoordinateSubmodule (n := n) p k ≤ E)
    (hE : IsDualQuotientAdmissible L p k E)
    {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ))}
    (hX : X ∈ gramCongruenceSolutionMatrices L p k) :
    localDualQuotientFamilyOfLE (n := n) hPE
        (localDualQuotientLiftFamily (n := n) p k X) ∈
      localDualQuotientSolutionFamilies L p k E hE.1 := by
  exact localDualQuotientFamilyOfLE_mem_localDualQuotientSolutionFamilies
    (L := L) (p := p) (k := k) (D := primePowCoordinateSubmodule (n := n) p k)
    (E := E) (hD_rank := primePowCoordinateSubmodule_rank (n := n) p k)
    (hE := hE) hPE
    (localDualQuotientLiftFamily_mem_localDualQuotientSolutionFamilies_of_gram_odd
      (L := L) (p := p) (k := k) hp_two hX)

lemma localDualQuotientLiftFamily_to_pairingMatrixLocalDual_mem_of_gram_odd
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ))}
    (hX : X ∈ gramCongruenceSolutionMatrices L p k) :
    localDualQuotientFamilyOfLE (n := n)
        (primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule
          (n := n) L p k)
        (localDualQuotientLiftFamily (n := n) p k X) ∈
      localDualQuotientSolutionFamilies L p k
        (pairingMatrixLocalDualCoordinateSubmodule L p k)
        (pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k) := by
  exact
    localDualQuotientLiftFamilyOfLE_mem_localDualQuotientSolutionFamilies_of_gram_odd
      (L := L) (p := p) (k := k) hp_two
      (primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule
        (n := n) L p k)
      (pairingMatrixLocalDualCoordinateSubmodule_admissible (n := n) L p k)
      hX

/-- The finite map from raw odd-prime Gram congruence solutions to
Schulze--Pillot solution families for the form-matrix local-dual denominator,
obtained by lifting matrix columns to the clean quotient and then coarsening
along `p^kℤ^n ≤ ker(F mod p^k)`.

The remaining positive-valuation numerator comparison is the fiber cardinality
of this map in the non-unit coordinate model. -/
def gramCongruenceSolutionToFormMatrixLocalDualSolutionFamily
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ)) //
        X ∈ gramCongruenceSolutionMatrices L p k} →
      {Y : Fin n → localDualQuotientTarget
          (pairingMatrixLocalDualCoordinateSubmodule L p k) //
        Y ∈ localDualQuotientSolutionFamilies L p k
          (pairingMatrixLocalDualCoordinateSubmodule L p k)
          (pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k)} :=
  fun X =>
    ⟨localDualQuotientFamilyOfLE (n := n)
        (primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule
          (n := n) L p k)
        (localDualQuotientLiftFamily (n := n) p k X.1),
      localDualQuotientLiftFamily_to_pairingMatrixLocalDual_mem_of_gram_odd
        (L := L) (p := p) (k := k) hp_two X.2⟩

@[simp] lemma gramCongruenceSolutionToFormMatrixLocalDualSolutionFamily_val
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (X : {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ)) //
        X ∈ gramCongruenceSolutionMatrices L p k}) :
    (gramCongruenceSolutionToFormMatrixLocalDualSolutionFamily
        (n := n) L p k hp_two X).1 =
      localDualQuotientFamilyOfLE (n := n)
        (primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule
          (n := n) L p k)
        (localDualQuotientLiftFamily (n := n) p k X.1) := rfl

/-- Once every fiber of the raw-Gram-to-form-matrix-local-dual map has the
same cardinal `c`, the raw Gram count is the local-dual quotient count times
`c`.  The remaining positive-valuation odd-prime work is to prove this
uniform fiber cardinal with `c = p^(n * v)`, starting from the one-column
denominator-subquotient computation. -/
lemma gramCongruenceSolutionCount_eq_localDualQuotientCount_mul_of_fiber_card
    (L : PositiveDefiniteIntegralLattice n) (p k c : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (hfiber :
      ∀ Y : {Y : Fin n → localDualQuotientTarget
            (pairingMatrixLocalDualCoordinateSubmodule L p k) //
          Y ∈ localDualQuotientSolutionFamilies L p k
            (pairingMatrixLocalDualCoordinateSubmodule L p k)
            (pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k)},
        Nat.card
          {X : {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ)) //
              X ∈ gramCongruenceSolutionMatrices L p k} //
            gramCongruenceSolutionToFormMatrixLocalDualSolutionFamily
              (n := n) L p k hp_two X = Y} = c) :
    gramCongruenceSolutionCount L p k =
      localDualQuotientCount L p k * c := by
  classical
  let D : Submodule ℤ (Fin n → ℤ) :=
    pairingMatrixLocalDualCoordinateSubmodule L p k
  let hD_rank : Module.finrank ℤ D = n :=
    pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k
  have hD_rank' : Module.finrank ℤ D = Module.finrank ℤ (Fin n → ℤ) := by
    simpa [D, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hD_rank
  letI : Finite (localDualQuotientTarget D) :=
    Submodule.finiteQuotientOfFreeOfRankEq (M := Fin n → ℤ) D hD_rank'
  letI : Fintype (localDualQuotientTarget D) :=
    Fintype.ofFinite (localDualQuotientTarget D)
  let α :=
    {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ)) //
      X ∈ gramCongruenceSolutionMatrices L p k}
  let β :=
    {Y : Fin n → localDualQuotientTarget D //
      Y ∈ localDualQuotientSolutionFamilies L p k D hD_rank}
  have hcount := nat_card_eq_mul_of_fiber_card
    (α := α) (β := β)
    (gramCongruenceSolutionToFormMatrixLocalDualSolutionFamily
      (n := n) L p k hp_two) c
    (by
      intro Y
      exact hfiber Y)
  have hα : Nat.card α = gramCongruenceSolutionCount L p k := by
    simp [α, gramCongruenceSolutionCount, Nat.card_eq_fintype_card]
  have hβ :
      Nat.card β =
        coordinateLocalDualQuotientCount L p k
          (pairingMatrixLocalDualCoordinateSubmodule L p k)
          (pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k) := by
    simp [β, D, coordinateLocalDualQuotientCount, Nat.card_eq_fintype_card]
  rw [hα, hβ] at hcount
  rw [localDualQuotientCount_eq_pairingMatrixLocalDual]
  exact hcount

/-- The fiber of the raw-Gram-to-local-dual map over a fixed local-dual
solution family has the same cardinality as the corresponding fiber of the
clean quotient basis-family coarsening map.  This transfers the denominator
coarsening fiber computation to the raw matrix map; the remaining
positive-valuation input is the one-column denominator subquotient
cardinality. -/
lemma gramCongruenceSolutionToFormMatrixLocalDualSolutionFamily_fiber_card_eq_quotientFamily_fiber
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (Y : {Y : Fin n → localDualQuotientTarget
          (pairingMatrixLocalDualCoordinateSubmodule L p k) //
        Y ∈ localDualQuotientSolutionFamilies L p k
          (pairingMatrixLocalDualCoordinateSubmodule L p k)
          (pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k)}) :
    Nat.card
        {X : {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ)) //
            X ∈ gramCongruenceSolutionMatrices L p k} //
          gramCongruenceSolutionToFormMatrixLocalDualSolutionFamily
            (n := n) L p k hp_two X = Y} =
      Nat.card
        {Z : Fin n →
            localDualQuotientTarget (primePowCoordinateSubmodule (n := n) p k) //
          localDualQuotientFamilyOfLE (n := n)
            (primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule
              (n := n) L p k) Z = Y.1} := by
  classical
  let D : Submodule ℤ (Fin n → ℤ) := primePowCoordinateSubmodule (n := n) p k
  let E : Submodule ℤ (Fin n → ℤ) := pairingMatrixLocalDualCoordinateSubmodule L p k
  let hDE : D ≤ E :=
    primePowCoordinateSubmodule_le_pairingMatrixLocalDualCoordinateSubmodule
      (n := n) L p k
  let e :
      {X : {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ)) //
            X ∈ gramCongruenceSolutionMatrices L p k} //
          gramCongruenceSolutionToFormMatrixLocalDualSolutionFamily
            (n := n) L p k hp_two X = Y} ≃
        {Z : Fin n → localDualQuotientTarget D //
          localDualQuotientFamilyOfLE (n := n) hDE Z = Y.1} :=
    { toFun := fun X =>
        ⟨localDualQuotientLiftFamily (n := n) p k X.1.1, by
          have hval := congrArg Subtype.val X.2
          simpa [D, E, hDE, gramCongruenceSolutionToFormMatrixLocalDualSolutionFamily_val]
            using hval⟩
      invFun := fun Z =>
        let M := localDualQuotientFamilyMatrix (n := n) p k Z.1
        have hZ_mem :
            Z.1 ∈ localDualQuotientSolutionFamilies L p k D
              (primePowCoordinateSubmodule_rank (n := n) p k) := by
          exact
            localDualQuotientFamilyOfLE_preimage_mem_localDualQuotientSolutionFamilies
              (L := L) (p := p) (k := k)
              (D := D) (E := E)
              (hD_rank := primePowCoordinateSubmodule_rank (n := n) p k)
              (hE_rank := pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k)
              hDE Y.2 Z.2
        have hM :
            M ∈ gramCongruenceSolutionMatrices L p k := by
          exact localDualQuotientFamilyMatrix_mem_gramCongruenceSolutionMatrices
            (L := L) (p := p) (k := k) hZ_mem
        ⟨⟨M, hM⟩, by
          apply Subtype.ext
          change localDualQuotientFamilyOfLE (n := n) hDE
              (localDualQuotientLiftFamily (n := n) p k M) = Y.1
          rw [localDualQuotientLiftFamily_familyMatrix]
          exact Z.2⟩
      left_inv := by
        intro X
        apply Subtype.ext
        apply Subtype.ext
        exact localDualQuotientFamilyMatrix_liftFamily (n := n) p k X.1.1
      right_inv := by
        intro Z
        apply Subtype.ext
        exact localDualQuotientLiftFamily_familyMatrix (n := n) p k Z.1 }
  exact Nat.card_congr e

/-- A one-column denominator-subquotient cardinal computation gives the
uniform raw-Gram-to-local-dual fiber cardinal `p^(n*v)`. -/
lemma gramCongruenceSolutionToFormMatrixLocalDualSolutionFamily_fiber_card_eq_prime_pow
    (L : PositiveDefiniteIntegralLattice n) (p k v : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (Y : {Y : Fin n → localDualQuotientTarget
          (pairingMatrixLocalDualCoordinateSubmodule L p k) //
        Y ∈ localDualQuotientSolutionFamilies L p k
          (pairingMatrixLocalDualCoordinateSubmodule L p k)
          (pairingMatrixLocalDualCoordinateSubmodule_rank (n := n) L p k)})
    (hsubquot :
      Nat.card
          (pairingMatrixLocalDualCoordinateSubmodule L p k ⧸
            (primePowCoordinateSubmodule (n := n) p k).comap
              (pairingMatrixLocalDualCoordinateSubmodule L p k).subtype) =
        p ^ v) :
    Nat.card
        {X : {X : Matrix (Fin n) (Fin n) (ZMod (primePowModulus p k : ℕ)) //
            X ∈ gramCongruenceSolutionMatrices L p k} //
          gramCongruenceSolutionToFormMatrixLocalDualSolutionFamily
            (n := n) L p k hp_two X = Y} =
      p ^ (n * v) := by
  rw [gramCongruenceSolutionToFormMatrixLocalDualSolutionFamily_fiber_card_eq_quotientFamily_fiber
    (n := n) L p k hp_two Y]
  exact pairingMatrixLocalDualQuotientFamilyOfLE_fiber_card_eq_prime_pow
    (n := n) L p k v Y.1 hsubquot

/-- Under the remaining one-column denominator-subquotient cardinal
hypothesis, the positive-valuation finite numerator identity follows. -/
lemma gramCongruenceSolutionCount_eq_localDualQuotientCount_mul_prime_pow_of_subquotient_card
    (L : PositiveDefiniteIntegralLattice n) (p k v : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (hsubquot :
      Nat.card
          (pairingMatrixLocalDualCoordinateSubmodule L p k ⧸
            (primePowCoordinateSubmodule (n := n) p k).comap
              (pairingMatrixLocalDualCoordinateSubmodule L p k).subtype) =
        p ^ v) :
    gramCongruenceSolutionCount L p k =
      localDualQuotientCount L p k * p ^ (n * v) := by
  exact
    gramCongruenceSolutionCount_eq_localDualQuotientCount_mul_of_fiber_card
      (n := n) L p k (p ^ (n * v)) hp_two
      (by
        intro Y
        exact
          gramCongruenceSolutionToFormMatrixLocalDualSolutionFamily_fiber_card_eq_prime_pow
            (n := n) L p k v hp_two Y hsubquot)

/-- If unimodular row and column operations put the form matrix in truncated
unit-times-`p`-power diagonal form, then the positive-valuation finite
numerator identity follows with correction exponent `n * ∑ i, v_i`. -/
lemma gramCongruenceSolutionCount_eq_localDualQuotientCount_mul_prime_pow_of_left_right_mul_eq_diagonal_units_prime_pows_of_lt
    (L : PositiveDefiniteIntegralLattice n) (P Q : Matrix (Fin n) (Fin n) ℤ)
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (u : Fin n → ℤ) (v : Fin n → ℕ) (hv : ∀ i, v i ≤ k)
    (hunit : ∀ i : Fin n, v i < k →
      IsUnit (((u i : ℤ) : ZMod (primePowModulus p k : ℕ))))
    (hP : IsUnit P) (hQ : IsUnit Q)
    (hdiag : P * L.pairingMatrix * Q =
      Matrix.diagonal (fun i : Fin n => u i * (p ^ v i : ℤ))) :
    gramCongruenceSolutionCount L p k =
      localDualQuotientCount L p k *
        p ^ (n * (∑ i : Fin n, v i)) := by
  exact
    gramCongruenceSolutionCount_eq_localDualQuotientCount_mul_prime_pow_of_subquotient_card
      (n := n) L p k (∑ i : Fin n, v i) hp_two
      (pairingMatrixLocalDualCoordinateSubmodule_subquotient_card_of_left_right_mul_eq_diagonal_units_prime_pows_of_lt
        (n := n) L P Q p k u v hv hunit hP hQ hdiag)

/-- If a unimodular diagonalization of the form matrix has all diagonal
`p`-adic valuations bounded by `k`, then the Smith finite-count correction
exponent is the `p`-adic valuation of `det(F)`. -/
lemma gramCongruenceSolutionCount_eq_localDualQuotientCount_mul_prime_pow_of_left_right_mul_eq_diagonal_padicValInt_det
    (L : PositiveDefiniteIntegralLattice n) (P Q : Matrix (Fin n) (Fin n) ℤ)
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (d : Fin n → ℤ)
    (hP : IsUnit P) (hQ : IsUnit Q)
    (hdiag : P * L.pairingMatrix * Q = Matrix.diagonal d)
    (hdval : ∀ i : Fin n, padicValInt p (d i) ≤ k)
    (hd : ∀ i : Fin n, d i ≠ 0) :
    gramCongruenceSolutionCount L p k =
      localDualQuotientCount L p k *
        p ^ (n * padicValInt p L.pairingMatrix.det) := by
  classical
  let v : Fin n → ℕ := fun i => truncatedPadicValInt p k (d i)
  have hv : ∀ i : Fin n, v i ≤ k := fun i =>
    truncatedPadicValInt_le p k (d i)
  have hfac : ∀ i : Fin n,
      ∃ u : ℤ,
        (∀ _hv : v i < k,
          IsUnit (((u : ℤ) : ZMod (primePowModulus p k : ℕ)))) ∧
        d i = u * (p ^ v i : ℤ) := fun i =>
    exists_unit_factor_truncatedPadicValInt p k (d i)
  choose u hu using hfac
  have hunit : ∀ i : Fin n, v i < k →
      IsUnit ((((u i) : ℤ) : ZMod (primePowModulus p k : ℕ))) := by
    intro i
    exact (hu i).1
  have hfactor : ∀ i : Fin n, d i = u i * (p ^ v i : ℤ) := fun i =>
    (hu i).2
  have hdiag' :
      P * L.pairingMatrix * Q =
        Matrix.diagonal (fun i : Fin n => u i * (p ^ v i : ℤ)) := by
    rw [hdiag]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hfactor]
    · simp [Matrix.diagonal_apply_ne _ hij]
  have hcount :
      gramCongruenceSolutionCount L p k =
        localDualQuotientCount L p k *
          p ^ (n * (∑ i : Fin n, v i)) :=
    gramCongruenceSolutionCount_eq_localDualQuotientCount_mul_prime_pow_of_left_right_mul_eq_diagonal_units_prime_pows_of_lt
      (n := n) L P Q p k hp_two u v hv hunit hP hQ hdiag'
  have hsum :
      ∑ i : Fin n, v i = padicValInt p L.pairingMatrix.det := by
    exact
      sum_truncatedPadicValInt_eq_padicValInt_det_of_left_right_mul_eq_diagonal
        (n := n) L.pairingMatrix P Q p k d hP hQ hdiag hdval hd
  rwa [hsum] at hcount

/-- Smith normal form supplies a diagonalization for `L.pairingMatrix` such that,
once `k` bounds the diagonal `p`-adic valuations, the odd-prime finite-count
correction exponent is `padicValInt p L.pairingDeterminant`.  This isolates the remaining
admissible-`k` bookkeeping from the determinant-valuation computation. -/
lemma exists_integral_diagonalization_count_padicValInt_pairingDeterminant
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℤ),
      IsUnit P ∧ IsUnit Q ∧
        P * L.pairingMatrix * Q = Matrix.diagonal d ∧
        (∀ i : Fin n, d i ≠ 0) ∧
        ((∀ i : Fin n, padicValInt p (d i) ≤ k) →
          gramCongruenceSolutionCount L p k =
            localDualQuotientCount L p k *
              p ^ (n * padicValInt p L.pairingDeterminant)) := by
  have hdet : L.pairingMatrix.det ≠ 0 := by
    simpa [pairingDeterminant] using (ne_of_gt L.pairingDeterminant_pos)
  rcases exists_integral_diagonalization_of_det_ne_zero
      (n := n) L.pairingMatrix hdet with
    ⟨P, Q, d, hP, hQ, hdiag⟩
  have hPdet : IsUnit P.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hP
  have hQdet : IsUnit Q.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hQ
  have hdiagdet_ne : (Matrix.diagonal d).det ≠ 0 := by
    rw [← hdiag]
    simpa [Matrix.det_mul, mul_assoc] using
      mul_ne_zero (mul_ne_zero hPdet.ne_zero hdet) hQdet.ne_zero
  have hprod_ne : (∏ i : Fin n, d i) ≠ 0 := by
    simpa [Matrix.det_diagonal] using hdiagdet_ne
  have hd : ∀ i : Fin n, d i ≠ 0 := by
    intro i hi
    exact hprod_ne (Finset.prod_eq_zero_iff.mpr ⟨i, Finset.mem_univ i, hi⟩)
  refine ⟨P, Q, d, hP, hQ, hdiag, hd, ?_⟩
  intro hdval
  have hcount :=
    gramCongruenceSolutionCount_eq_localDualQuotientCount_mul_prime_pow_of_left_right_mul_eq_diagonal_padicValInt_det
      (n := n) L P Q p k hp_two d hP hQ hdiag hdval hd
  simpa [pairingDeterminant] using hcount

/-- Odd-prime version of the Smith finite-count input with the correction
exponent written as the bilinear Gram discriminant valuation, matching the
classical local-density normalization. -/
lemma exists_integral_diagonalization_count_padicValInt_polarDeterminant
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℤ),
      IsUnit P ∧ IsUnit Q ∧
        P * L.pairingMatrix * Q = Matrix.diagonal d ∧
        (∀ i : Fin n, d i ≠ 0) ∧
        ((∀ i : Fin n, padicValInt p (d i) ≤ k) →
          gramCongruenceSolutionCount L p k =
            localDualQuotientCount L p k *
              p ^ (n * padicValInt p L.polarDeterminant)) := by
  rcases exists_integral_diagonalization_count_padicValInt_pairingDeterminant
      (n := n) L p k hp_two with
    ⟨P, Q, d, hP, hQ, hdiag, hd, hcount⟩
  refine ⟨P, Q, d, hP, hQ, hdiag, hd, ?_⟩
  intro hdval
  have hdisc :
      padicValInt p L.polarDeterminant = padicValInt p L.pairingDeterminant :=
    padicValInt_polarDeterminant_eq_padicValInt_pairingDeterminant_of_ne_two (n := n) L p hp_two
  simpa [hdisc] using hcount hdval

/-- If the bilinear Gram discriminant valuation is bounded by the chosen
exponent `k`, then every diagonal entry in any unimodular diagonalization of
`L.pairingMatrix` has `p`-adic valuation bounded by `k`.

This is the arithmetic bookkeeping needed to discharge the bounded Smith
hypothesis in the local-density range. -/
lemma padicValInt_smith_diagonal_le_of_polarDeterminant_val_le
    (L : PositiveDefiniteIntegralLattice n) (P Q : Matrix (Fin n) (Fin n) ℤ)
    (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (d : Fin n → ℤ)
    (hP : IsUnit P) (hQ : IsUnit Q)
    (hdiag : P * L.pairingMatrix * Q = Matrix.diagonal d)
    (hd : ∀ i : Fin n, d i ≠ 0)
    (hdisc_le : padicValInt p L.polarDeterminant ≤ k) :
    ∀ i : Fin n, padicValInt p (d i) ≤ k := by
  have hsum_form :
      padicValInt p L.pairingMatrix.det = ∑ i : Fin n, padicValInt p (d i) :=
    padicValInt_det_eq_sum_diagonal_of_left_right_mul_eq_diagonal
      (n := n) L.pairingMatrix P Q p d hP hQ hdiag hd
  have hsum_disc :
      ∑ i : Fin n, padicValInt p (d i) = padicValInt p L.polarDeterminant := by
    calc
      ∑ i : Fin n, padicValInt p (d i)
          = padicValInt p L.pairingMatrix.det := hsum_form.symm
      _ = padicValInt p L.pairingDeterminant := by rfl
      _ = padicValInt p L.polarDeterminant :=
          (padicValInt_polarDeterminant_eq_padicValInt_pairingDeterminant_of_ne_two
            (n := n) L p hp_two).symm
  have hsum_le :
      ∑ i : Fin n, padicValInt p (d i) ≤ k := by
    simpa [hsum_disc] using hdisc_le
  intro i
  exact
    (Finset.single_le_sum
      (fun j _hj => Nat.zero_le (padicValInt p (d j)))
      (Finset.mem_univ i)).trans hsum_le

/-- Once `k` bounds the bilinear Gram discriminant valuation, the Smith
finite-count identity holds without a separate per-diagonal valuation
hypothesis. -/
lemma gramCongruenceSolutionCount_eq_localDualQuotientCount_mul_prime_pow_of_polarDeterminant_val_le
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (hdisc_le : padicValInt p L.polarDeterminant ≤ k) :
    gramCongruenceSolutionCount L p k =
      localDualQuotientCount L p k *
        p ^ (n * padicValInt p L.polarDeterminant) := by
  rcases exists_integral_diagonalization_count_padicValInt_polarDeterminant
      (n := n) L p k hp_two with
    ⟨P, Q, d, hP, hQ, hdiag, hd, hcount⟩
  exact hcount
    (padicValInt_smith_diagonal_le_of_polarDeterminant_val_le
      (n := n) L P Q p k hp_two d hP hQ hdiag hd hdisc_le)

/-- The real-valued non-unit count-correction hypothesis follows from the
finite cardinal identity expected in the positive-valuation case:
`A(L_p,L_p mod p^k L_p#) * p^(n v) = N_A(p^k)`.  This keeps the remaining
odd-prime numerator comparison as a finite counting problem. -/
lemma localDualQuotientCount_correction_eq_classicalGramLocalDensity_odd_of_count_mul
    (L : PositiveDefiniteIntegralLattice n) (p k v : ℕ) [Fact (Nat.Prime p)]
    (hcount :
      localDualQuotientCount L p k * p ^ (n * v) =
        gramCongruenceSolutionCount L p k) :
    ((((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
        (localDualQuotientCount L p k : ℚ) : ℚ) : ℝ) =
      (classicalGramLocalDensity L p k : ℝ) *
        localDualQuotientValuationCorrectionFactor p n v := by
  unfold classicalGramLocalDensity localDualQuotientValuationCorrectionFactor
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hp_nonneg : 0 ≤ (p : ℝ) := le_of_lt hp_pos
  have hpq_ne : (p : ℚ) ^ (n * v) ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  have hcount_q :
      (gramCongruenceSolutionCount L p k : ℚ) =
        (localDualQuotientCount L p k : ℚ) * (p : ℚ) ^ (n * v) := by
    rw [← hcount]
    norm_num [Nat.cast_mul, Nat.cast_pow]
  have hcorr :
      ((((p : ℚ) ^ (n * v) : ℚ) : ℝ))⁻¹ =
        (p : ℝ) ^ (-((n : ℝ) * (v : ℝ))) := by
    rw [show ((n : ℝ) * (v : ℝ)) = ((n * v : ℕ) : ℝ) by norm_num]
    rw [Real.rpow_neg hp_nonneg, Real.rpow_natCast]
    norm_num
  rw [hcount_q]
  calc
    ((((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
        (localDualQuotientCount L p k : ℚ) : ℚ) : ℝ)
        =
      ((((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
        ((localDualQuotientCount L p k : ℚ) * (p : ℚ) ^ (n * v)) :
          ℚ) : ℝ) *
        ((((p : ℚ) ^ (n * v) : ℚ) : ℝ))⁻¹ := by
          norm_num
          field_simp [hpq_ne]
    _ =
      ((((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
        ((localDualQuotientCount L p k : ℚ) * (p : ℚ) ^ (n * v)) :
          ℚ) : ℝ) *
        (p : ℝ) ^ (-((n : ℝ) * (v : ℝ))) := by
          rw [hcorr]

/-- If `k` bounds the bilinear Gram discriminant valuation, the finite Smith
count correction gives the real-valued non-unit local-dual quotient correction
with `v = padicValInt p L.polarDeterminant`. -/
lemma localDualQuotientCount_correction_eq_classicalGramLocalDensity_odd_of_polarDeterminant_val_le
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hp_two : p ≠ 2)
    (hdisc_le : padicValInt p L.polarDeterminant ≤ k) :
    ((((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
        (localDualQuotientCount L p k : ℚ) : ℚ) : ℝ) =
      (classicalGramLocalDensity L p k : ℝ) *
        localDualQuotientValuationCorrectionFactor
          p n (padicValInt p L.polarDeterminant) := by
  have hcount :
      localDualQuotientCount L p k *
          p ^ (n * padicValInt p L.polarDeterminant) =
        gramCongruenceSolutionCount L p k := by
    exact
      (gramCongruenceSolutionCount_eq_localDualQuotientCount_mul_prime_pow_of_polarDeterminant_val_le
        (n := n) L p k hp_two hdisc_le).symm
  exact
    localDualQuotientCount_correction_eq_classicalGramLocalDensity_odd_of_count_mul
      (n := n) L p k (padicValInt p L.polarDeterminant) hcount

lemma twoPadicNormInvPow_pos (p n : ℕ) :
    0 < twoPadicNormInvPow p n := by
  unfold twoPadicNormInvPow
  split
  · positivity
  · norm_num

lemma twoPadicNormInvPow_eq_one_of_ne_two
    {p n : ℕ} (hp_two : p ≠ 2) :
    twoPadicNormInvPow p n = 1 := by
  simp [twoPadicNormInvPow, hp_two]

lemma twoPadicNormInvPow_eq_two_pow (n : ℕ) :
    twoPadicNormInvPow 2 n = (2 : ℚ) ^ n := by
  simp [twoPadicNormInvPow]

lemma dualCountNormalizationFactor_pos (p n : ℕ) :
    0 < dualCountNormalizationFactor p n := by
  unfold dualCountNormalizationFactor
  split
  · positivity
  · norm_num

lemma dualCountNormalizationFactor_eq_one_of_ne_two
    {p n : ℕ} (hp_two : p ≠ 2) :
    dualCountNormalizationFactor p n = 1 := by
  simp [dualCountNormalizationFactor, hp_two]

lemma dualCountNormalizationFactor_eq_inv_two_pow (n : ℕ) :
    dualCountNormalizationFactor 2 n =
      ((2 : ℚ) ^ (n * n))⁻¹ := by
  simp [dualCountNormalizationFactor]

lemma gramDetPadicNormFactor_pos
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    0 < gramDetPadicNormFactor L p := by
  unfold gramDetPadicNormFactor
  have hdisc_ne : (L.polarDeterminant : ℤ_[p]) ≠ 0 := by
    exact_mod_cast (ne_of_gt L.polarDeterminant_pos)
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr hdisc_ne) _

lemma gramDetPadicValuationFactor_mul_localDualQuotientValuationCorrectionFactor
    (p n v : ℕ) [Fact (Nat.Prime p)] :
    gramDetPadicValuationFactor p n v *
        localDualQuotientValuationCorrectionFactor p n v =
      (p : ℝ) ^ (-((v : ℝ) * (((n : ℝ) + 1) / 2))) := by
  unfold gramDetPadicValuationFactor
    localDualQuotientValuationCorrectionFactor
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  rw [← Real.rpow_add hp_pos]
  congr 1
  ring

lemma gramDetPadicNormFactor_eq_valuationFactor_of_norm_eq
    (L : PositiveDefiniteIntegralLattice n) (p v : ℕ) [Fact (Nat.Prime p)]
    (hdisc_norm : ‖(L.polarDeterminant : ℤ_[p])‖ = (p : ℝ) ^ (-(v : ℝ))) :
    gramDetPadicNormFactor L p =
      gramDetPadicValuationFactor p n v := by
  unfold gramDetPadicNormFactor
  rw [hdisc_norm]
  have hp_nonneg : 0 ≤ (p : ℝ) := by positivity
  rw [← Real.rpow_mul hp_nonneg]
  unfold gramDetPadicValuationFactor
  congr 1
  ring

lemma gramDetPadicNormFactor_eq_of_isLocallyIsometricAt
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p : ℕ) [Fact (Nat.Prime p)]
    (h : L₀.IsLocallyIsometricAt L₁ p) :
    gramDetPadicNormFactor L₀ p =
      gramDetPadicNormFactor L₁ p := by
  unfold gramDetPadicNormFactor
  rw [polarDeterminant_padic_norm_eq_of_isLocallyIsometricAt L₀ L₁ p h]

lemma fixedKDensityFactor_eq_localDualQuotientCount
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    fixedKDensityFactor L p k =
      dualCountNormalizationFactor p n *
        (1 / 2 : ℚ) * twoPadicNormInvPow p n *
        ((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
        (localDualQuotientCount L p k : ℚ) := by
  unfold fixedKDensityFactor localDualQuotientFixedKDensityFactor
  have hcount :
      coordinateLocalDualQuotientCount L p k
          (localDualPadicDenominatorIntegralPreimage L p k)
          (localDualPadicDenominatorIntegralPreimage_admissible (n := n) L p k).1 =
        localDualQuotientCount L p k := by
    exact coordinateLocalDualQuotientCount_eq_of_submodule_eq L p k rfl
      (localDualPadicDenominatorIntegralPreimage_admissible (n := n) L p k).1
      (localDualPadicDenominatorIntegralPreimage_rank (n := n) L p k)
  rw [hcount]
  ring

lemma fixedKDensityFactor_eq_localDualQuotientCount_dyadic
    (L : PositiveDefiniteIntegralLattice n) (k : ℕ) :
    fixedKDensityFactor L 2 k =
      ((2 : ℚ) ^ (n * n))⁻¹ * (1 / 2 : ℚ) * (2 : ℚ) ^ n *
        ((2 : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
        (localDualQuotientCount L 2 k : ℚ) := by
  rw [fixedKDensityFactor_eq_localDualQuotientCount,
    dualCountNormalizationFactor_eq_inv_two_pow,
    twoPadicNormInvPow_eq_two_pow]
  norm_num

/-- In the quantitative Hensel range, the current-coordinate definition is
exactly Schulze--Pillot's fixed-`k` expression using the associated-bilinear
`2F`-dual quotient count.  At `2`, the dual-count normalization cancels the
proved factor `2^(n*n)` between the current and source counts; the independent
quadratic-congruence factor `|2|_2^{-n} = 2^n` remains. -/
lemma fixedKDensityFactor_eq_associatedBilinearDualQuotientCount
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityHenselExponent L p k) :
    fixedKDensityFactor L p k =
      (1 / 2 : ℚ) * twoPadicNormInvPow p n *
        ((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
        (associatedBilinearDualQuotientCount L p k : ℚ) := by
  by_cases hp_two : p = 2
  · subst p
    rw [fixedKDensityFactor_eq_localDualQuotientCount_dyadic,
      localDualQuotientCount_eq_two_pow_mul_associatedBilinear_dyadic
        L k hk,
      twoPadicNormInvPow_eq_two_pow]
    push_cast
    field_simp
  · rw [fixedKDensityFactor_eq_localDualQuotientCount,
      dualCountNormalizationFactor_eq_one_of_ne_two hp_two,
      ← associatedBilinearDualQuotientCount_eq_current_of_ne_two
        L p k hp_two]
    ring

lemma normalizedLocalDensityAtExponent_eq_fixedKDensityWithGramDetFactor
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityAdmissibleExponent L p k) :
    normalizedLocalDensityAtExponent L p k hk =
      fixedKDensityWithGramDetFactor L p k := rfl

lemma normalizedLocalDensityAtExponent_eq_localDualQuotientCount
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityAdmissibleExponent L p k) :
    normalizedLocalDensityAtExponent L p k hk =
      ((dualCountNormalizationFactor p n *
        (1 / 2 : ℚ) * twoPadicNormInvPow p n *
        ((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
        (localDualQuotientCount L p k : ℚ) : ℚ) : ℝ) *
        gramDetPadicNormFactor L p := by
  rw [normalizedLocalDensityAtExponent_eq_fixedKDensityWithGramDetFactor,
    fixedKDensityWithGramDetFactor,
    fixedKDensityFactor_eq_localDualQuotientCount]

lemma normalizedLocalDensityAtExponent_eq_associatedBilinearDualQuotientCount
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityHenselExponent L p k) :
    normalizedLocalDensityAtExponent L p k hk.admissible =
      (((1 / 2 : ℚ) * twoPadicNormInvPow p n *
        ((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
        (associatedBilinearDualQuotientCount L p k : ℚ) : ℚ) : ℝ) *
        gramDetPadicNormFactor L p := by
  rw [normalizedLocalDensityAtExponent_eq_fixedKDensityWithGramDetFactor,
    fixedKDensityWithGramDetFactor,
    fixedKDensityFactor_eq_associatedBilinearDualQuotientCount
      L p k hk]

lemma localDualQuotientNormalizedCount_succ_eq
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityHenselExponent L p k) :
    localDualQuotientNormalizedCount L p (k + 1) =
      localDualQuotientNormalizedCount L p k := by
  unfold localDualQuotientNormalizedCount
  rw [localDualQuotientCount_succ_eq L p k hk]
  push_cast
  have hexp : localDensityDenominatorExponent n (k + 1) =
      localDensityDenominatorExponent n k +
        n * (n - 1) / 2 := by
    unfold localDensityDenominatorExponent
    rw [Nat.add_mul]
    simp
  rw [hexp, pow_add]
  field_simp [show (p : ℚ) ≠ 0 by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero]

lemma localDualQuotientNormalizedCount_add_eq
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityHenselExponent L p k) :
    ∀ r : ℕ,
      localDualQuotientNormalizedCount L p (k + r) =
        localDualQuotientNormalizedCount L p k
  | 0 => by simp
  | r + 1 => by
      rw [Nat.add_succ]
      exact
        (localDualQuotientNormalizedCount_succ_eq
          L p (k + r) (hk.add L p k r)).trans
        (localDualQuotientNormalizedCount_add_eq
          L p k hk r)

lemma localDualQuotientNormalizedCount_eq_of_isLocalDensityHenselExponent
    (L : PositiveDefiniteIntegralLattice n) (p k₁ k₂ : ℕ) [Fact (Nat.Prime p)]
    (hk₁ : IsLocalDensityHenselExponent L p k₁)
    (hk₂ : IsLocalDensityHenselExponent L p k₂) :
    localDualQuotientNormalizedCount L p k₁ =
      localDualQuotientNormalizedCount L p k₂ := by
  calc
    localDualQuotientNormalizedCount L p k₁ =
        localDualQuotientNormalizedCount L p (k₁ + k₂) :=
      (localDualQuotientNormalizedCount_add_eq
        L p k₁ hk₁ k₂).symm
    _ = localDualQuotientNormalizedCount L p (k₂ + k₁) := by
      rw [Nat.add_comm]
    _ = localDualQuotientNormalizedCount L p k₂ :=
      localDualQuotientNormalizedCount_add_eq
        L p k₂ hk₂ k₁

lemma fixedKDensityFactor_eq_of_admissible
    (L : PositiveDefiniteIntegralLattice n) (p k₁ k₂ : ℕ) [Fact (Nat.Prime p)]
    (hk₁ : IsLocalDensityHenselExponent L p k₁)
    (hk₂ : IsLocalDensityHenselExponent L p k₂) :
    fixedKDensityFactor L p k₁ =
      fixedKDensityFactor L p k₂ := by
  rw [fixedKDensityFactor_eq_localDualQuotientCount,
    fixedKDensityFactor_eq_localDualQuotientCount]
  have hcount :=
    localDualQuotientNormalizedCount_eq_of_isLocalDensityHenselExponent
      (n := n) L p k₁ k₂ hk₁ hk₂
  unfold localDualQuotientNormalizedCount at hcount
  calc
    dualCountNormalizationFactor p n *
        (1 / 2 : ℚ) * twoPadicNormInvPow p n *
        ((p : ℚ) ^ localDensityDenominatorExponent n k₁)⁻¹ *
        (localDualQuotientCount L p k₁ : ℚ)
        =
      dualCountNormalizationFactor p n *
        (1 / 2 : ℚ) * twoPadicNormInvPow p n *
        (((p : ℚ) ^ localDensityDenominatorExponent n k₁)⁻¹ *
        (localDualQuotientCount L p k₁ : ℚ)) := by
          ring
    _ =
      dualCountNormalizationFactor p n *
        (1 / 2 : ℚ) * twoPadicNormInvPow p n *
        (((p : ℚ) ^ localDensityDenominatorExponent n k₂)⁻¹ *
        (localDualQuotientCount L p k₂ : ℚ)) := by
          rw [hcount]
    _ =
      dualCountNormalizationFactor p n *
        (1 / 2 : ℚ) * twoPadicNormInvPow p n *
        ((p : ℚ) ^ localDensityDenominatorExponent n k₂)⁻¹ *
        (localDualQuotientCount L p k₂ : ℚ) := by
          ring

lemma normalizedLocalDensityAtExponent_eq_of_admissible
    (L : PositiveDefiniteIntegralLattice n) (p k₁ k₂ : ℕ) [Fact (Nat.Prime p)]
    (hk₁ : IsLocalDensityHenselExponent L p k₁)
    (hk₂ : IsLocalDensityHenselExponent L p k₂) :
    normalizedLocalDensityAtExponent L p k₁ hk₁.admissible =
      normalizedLocalDensityAtExponent L p k₂ hk₂.admissible := by
  rw [normalizedLocalDensityAtExponent_eq_fixedKDensityWithGramDetFactor,
    normalizedLocalDensityAtExponent_eq_fixedKDensityWithGramDetFactor,
    fixedKDensityWithGramDetFactor,
    fixedKDensityWithGramDetFactor,
    fixedKDensityFactor_eq_of_admissible
      (n := n) L p k₁ k₂ hk₁ hk₂]

lemma normalizedLocalDensity_eq_fixedK
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityHenselExponent L p k) :
    normalizedLocalDensity L p = normalizedLocalDensityAtExponent L p k hk.admissible := by
  unfold normalizedLocalDensity
  exact normalizedLocalDensityAtExponent_eq_of_admissible
    (n := n) L p (localDensityHenselExponent L p) k
    (isLocalDensityHenselExponent_preferred (n := n) L p) hk

lemma normalizedLocalDensity_eq_associatedBilinearDualQuotientCount
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityHenselExponent L p k) :
    normalizedLocalDensity L p =
      (((1 / 2 : ℚ) * twoPadicNormInvPow p n *
        ((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
        (associatedBilinearDualQuotientCount L p k : ℚ) : ℚ) : ℝ) *
        gramDetPadicNormFactor L p := by
  rw [normalizedLocalDensity_eq_fixedK L p k hk]
  exact normalizedLocalDensityAtExponent_eq_associatedBilinearDualQuotientCount
    L p k hk

/-- If the non-unit count comparison `hcount` supplies the expected
`p^{-n v}` correction, then the odd-prime conversion has exactly the
denominator exponent `v(n+1)/2`. -/
lemma normalizedLocalDensity_eq_half_classicalGramLocalDensity_mul_target_odd_of_count_correction
    (L : PositiveDefiniteIntegralLattice n) (p k v : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityHenselExponent L p k)
    (hp_two : p ≠ 2)
    (hdisc_norm : ‖(L.polarDeterminant : ℤ_[p])‖ = (p : ℝ) ^ (-(v : ℝ)))
    (hcount :
      ((((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
          (localDualQuotientCount L p k : ℚ) : ℚ) : ℝ) =
        (classicalGramLocalDensity L p k : ℝ) *
          (localDualQuotientValuationCorrectionFactor p n v)) :
    normalizedLocalDensity L p =
      (((1 / 2 : ℚ) * classicalGramLocalDensity L p k : ℚ) : ℝ) *
        (p : ℝ) ^ (-((v : ℝ) * (((n : ℝ) + 1) / 2))) := by
  rw [normalizedLocalDensity_eq_fixedK L p k hk,
    normalizedLocalDensityAtExponent_eq_localDualQuotientCount,
    dualCountNormalizationFactor_eq_one_of_ne_two hp_two,
    twoPadicNormInvPow_eq_one_of_ne_two hp_two,
    gramDetPadicNormFactor_eq_valuationFactor_of_norm_eq
      (n := n) L p v hdisc_norm]
  calc
    (((1 : ℚ) * (1 / 2 : ℚ) * 1 *
        ((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
        (localDualQuotientCount L p k : ℚ) : ℚ) : ℝ) *
        gramDetPadicValuationFactor p n v
        =
      ((1 / 2 : ℚ) : ℝ) *
        ((((p : ℚ) ^ localDensityDenominatorExponent n k)⁻¹ *
          (localDualQuotientCount L p k : ℚ) : ℚ) : ℝ) *
        gramDetPadicValuationFactor p n v := by
          norm_num
          ring_nf
          exact Or.inl trivial
    _ =
      ((1 / 2 : ℚ) : ℝ) *
        ((classicalGramLocalDensity L p k : ℝ) *
          localDualQuotientValuationCorrectionFactor p n v) *
        gramDetPadicValuationFactor p n v := by
          rw [hcount]
    _ =
      (((1 / 2 : ℚ) * classicalGramLocalDensity L p k : ℚ) : ℝ) *
        (gramDetPadicValuationFactor p n v *
          localDualQuotientValuationCorrectionFactor p n v) := by
          norm_num
          ring_nf
    _ =
      (((1 / 2 : ℚ) * classicalGramLocalDensity L p k : ℚ) : ℝ) *
        (p : ℝ) ^ (-((v : ℝ) * (((n : ℝ) + 1) / 2))) := by
          rw [gramDetPadicValuationFactor_mul_localDualQuotientValuationCorrectionFactor]

/-- Odd-prime target comparison after the Smith finite-count correction has
been discharged by the concrete bound `padicValInt p L.polarDeterminant ≤ k`.
The p-adic norm of the bilinear Gram determinant is now translated to its
integer valuation by `polarDeterminant_padic_norm_eq_padicValInt`. -/
lemma normalizedLocalDensity_eq_half_classicalGramLocalDensity_mul_target_odd_of_polarDeterminant_val_le
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityHenselExponent L p k)
    (hp_two : p ≠ 2)
    (hdisc_le : padicValInt p L.polarDeterminant ≤ k) :
    normalizedLocalDensity L p =
      (((1 / 2 : ℚ) * classicalGramLocalDensity L p k : ℚ) : ℝ) *
        (p : ℝ) ^
          (-((padicValInt p L.polarDeterminant : ℝ) * (((n : ℝ) + 1) / 2))) := by
  exact
    normalizedLocalDensity_eq_half_classicalGramLocalDensity_mul_target_odd_of_count_correction
      (n := n) L p k (padicValInt p L.polarDeterminant) hk hp_two
      (polarDeterminant_padic_norm_eq_padicValInt (n := n) L p)
      (localDualQuotientCount_correction_eq_classicalGramLocalDensity_odd_of_polarDeterminant_val_le
        (n := n) L p k hp_two hdisc_le)

/-- Odd-prime target comparison through the final fixed-`k` exponent interface
for the classical matrix-count conversion. -/
lemma normalizedLocalDensity_eq_half_classicalGramLocalDensity_mul_target_odd_of_classicalComparisonExponent
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityClassicalComparisonExponent L p k)
    (hp_two : p ≠ 2) :
    normalizedLocalDensity L p =
      (((1 / 2 : ℚ) * classicalGramLocalDensity L p k : ℚ) : ℝ) *
        (p : ℝ) ^
          (-((padicValInt p L.polarDeterminant : ℝ) * (((n : ℝ) + 1) / 2))) := by
  exact normalizedLocalDensity_eq_half_classicalGramLocalDensity_mul_target_odd_of_polarDeterminant_val_le
    (n := n) L p k hk.hensel hp_two (Nat.le_of_lt hk.disc_val_lt)

/-- The odd-prime target expression obtained from the classical matrix count
does not depend on the sufficiently large exponent used in the comparison. -/
lemma classicalComparisonValue_eq_of_classicalComparisonExponent
    (L : PositiveDefiniteIntegralLattice n) (p k₁ k₂ : ℕ) [Fact (Nat.Prime p)]
    (hk₁ : IsLocalDensityClassicalComparisonExponent L p k₁)
    (hk₂ : IsLocalDensityClassicalComparisonExponent L p k₂)
    (hp_two : p ≠ 2) :
    (((1 / 2 : ℚ) * classicalGramLocalDensity L p k₁ : ℚ) : ℝ) *
        (p : ℝ) ^
          (-((padicValInt p L.polarDeterminant : ℝ) * (((n : ℝ) + 1) / 2))) =
      (((1 / 2 : ℚ) * classicalGramLocalDensity L p k₂ : ℚ) : ℝ) *
        (p : ℝ) ^
          (-((padicValInt p L.polarDeterminant : ℝ) * (((n : ℝ) + 1) / 2))) := by
  exact
    (normalizedLocalDensity_eq_half_classicalGramLocalDensity_mul_target_odd_of_classicalComparisonExponent
      (n := n) L p k₁ hk₁ hp_two).symm.trans
      (normalizedLocalDensity_eq_half_classicalGramLocalDensity_mul_target_odd_of_classicalComparisonExponent
        (n := n) L p k₂ hk₂ hp_two)

/-- A canonical sufficiently large exponent for the odd-prime classical
matrix-count comparison. -/
def classicalComparisonExponent
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  localDensityHenselExponent L p

lemma isLocalDensityClassicalComparisonExponent_preferred
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_two : p ≠ 2) :
    IsLocalDensityClassicalComparisonExponent L p
      (classicalComparisonExponent L p) :=
  isLocalDensityClassicalComparisonExponent_of_polarDeterminant_val_lt
    (n := n) L p (classicalComparisonExponent L p)
    (by simp [classicalComparisonExponent,
      localDensityHenselExponent]) hp_two

/-- The preferred exponent-independent odd-prime classical comparison value.

The definition uses the canonical large exponent above; the theorem
`classicalComparisonValue_eq_expression_of_classicalComparisonExponent`
shows that any other sufficiently large exponent gives the same value. -/
noncomputable def classicalComparisonValue
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℝ :=
  (((1 / 2 : ℚ) *
      classicalGramLocalDensity L p (classicalComparisonExponent L p) :
        ℚ) : ℝ) *
    (p : ℝ) ^
      (-((padicValInt p L.polarDeterminant : ℝ) * (((n : ℝ) + 1) / 2)))

/-- The preferred exponent-independent classical matrix solution-count density
`α_p^cl(L)` from the odd-prime comparison statement.  It uses the same
canonical sufficiently large exponent as
`classicalComparisonValue`. -/
noncomputable def classicalSolutionCountLocalDensity
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℚ :=
  classicalGramLocalDensity L p (classicalComparisonExponent L p)

lemma classicalComparisonValue_eq_expression_of_classicalComparisonExponent
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityClassicalComparisonExponent L p k)
    (hp_two : p ≠ 2) :
    classicalComparisonValue L p =
      (((1 / 2 : ℚ) * classicalGramLocalDensity L p k : ℚ) : ℝ) *
        (p : ℝ) ^
          (-((padicValInt p L.polarDeterminant : ℝ) * (((n : ℝ) + 1) / 2))) := by
  unfold classicalComparisonValue
  exact classicalComparisonValue_eq_of_classicalComparisonExponent
    (n := n) L p (classicalComparisonExponent L p) k
    (isLocalDensityClassicalComparisonExponent_preferred (n := n) L p hp_two)
    hk hp_two

lemma classicalComparisonValue_eq_classicalSolutionCountLocalDensity
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    classicalComparisonValue L p =
      (((1 / 2 : ℚ) * classicalSolutionCountLocalDensity L p : ℚ) : ℝ) *
        (p : ℝ) ^
          (-((padicValInt p L.polarDeterminant : ℝ) * (((n : ℝ) + 1) / 2))) := by
  rfl

lemma normalizedLocalDensity_eq_classicalComparisonValue_odd
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_two : p ≠ 2) :
    normalizedLocalDensity L p = classicalComparisonValue L p := by
  unfold classicalComparisonValue
  exact
    normalizedLocalDensity_eq_half_classicalGramLocalDensity_mul_target_odd_of_classicalComparisonExponent
      (n := n) L p (classicalComparisonExponent L p)
      (isLocalDensityClassicalComparisonExponent_preferred (n := n) L p hp_two)
      hp_two

/-- Final odd-prime conversion written with the preferred classical
solution-count density notation from the TeX statement. -/
lemma normalizedLocalDensity_eq_classicalSolutionCountLocalDensity_odd
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hp_two : p ≠ 2) :
    normalizedLocalDensity L p =
      (((1 / 2 : ℚ) * classicalSolutionCountLocalDensity L p : ℚ) : ℝ) *
        (p : ℝ) ^
          (-((padicValInt p L.polarDeterminant : ℝ) * (((n : ℝ) + 1) / 2))) := by
  rw [normalizedLocalDensity_eq_classicalComparisonValue_odd (n := n) L p hp_two,
    classicalComparisonValue_eq_classicalSolutionCountLocalDensity]

/-- Under the quotient admissibility hypotheses, the identity map contributes
one solution to the Schulze--Pillot coordinate local-dual quotient count. -/
lemma quotientIdentityBasisFamily_mem_localDualQuotientSolutionFamilies
    {L : PositiveDefiniteIntegralLattice n} {p k : ℕ} [Fact (Nat.Prime p)]
    {D : Submodule ℤ (Fin n → ℤ)}
    (hD : IsDualQuotientAdmissible L p k D) :
    quotientIdentityBasisFamily D ∈
      localDualQuotientSolutionFamilies L p k D hD.1 := by
  classical
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  have hquot : D.mkQ x = D.mkQ y := by
    simpa [quotientBasisFamilyMap_identity D x] using hxy
  have hxyD : x - y ∈ D := by
    change Submodule.Quotient.mk x = Submodule.Quotient.mk y at hquot
    rwa [Submodule.Quotient.eq] at hquot
  have hyxD : y - x ∈ D := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using D.neg_mem hxyD
  exact hD.2 hyxD

/-- The Schulze--Pillot coordinate local-dual quotient count is nonzero under
the visible admissibility hypotheses. -/
lemma coordinateLocalDualQuotientCount_pos_of_admissible
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ (Fin n → ℤ))
    (hD : IsDualQuotientAdmissible L p k D) :
    0 < coordinateLocalDualQuotientCount L p k D hD.1 := by
  rw [coordinateLocalDualQuotientCount]
  exact Finset.card_pos.mpr
    ⟨quotientIdentityBasisFamily D,
      quotientIdentityBasisFamily_mem_localDualQuotientSolutionFamilies hD⟩

lemma localDualQuotientFixedKDensityFactor_pos
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (D : Submodule ℤ (Fin n → ℤ))
    (hD : IsDualQuotientAdmissible L p k D) :
    0 < localDualQuotientFixedKDensityFactor L p k D hD := by
  unfold localDualQuotientFixedKDensityFactor
  have hp : 0 < (p : ℚ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpow : 0 < (p : ℚ) ^ localDensityDenominatorExponent n k :=
    pow_pos hp _
  have hcount : 0 < (coordinateLocalDualQuotientCount L p k D hD.1 : ℚ) := by
    exact_mod_cast coordinateLocalDualQuotientCount_pos_of_admissible L p k D hD
  exact mul_pos
    (mul_pos
      (mul_pos (by norm_num) (twoPadicNormInvPow_pos p n))
      (inv_pos.mpr hpow))
    hcount

lemma fixedKDensityFactor_pos
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    0 < fixedKDensityFactor L p k := by
  unfold fixedKDensityFactor
  exact mul_pos (dualCountNormalizationFactor_pos p n)
    (localDualQuotientFixedKDensityFactor_pos L p k
      (localDualPadicDenominatorIntegralPreimage L p k)
      (localDualPadicDenominatorIntegralPreimage_admissible (n := n) L p k))

lemma fixedKDensityWithGramDetFactor_pos
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    0 < fixedKDensityWithGramDetFactor L p k := by
  unfold fixedKDensityWithGramDetFactor
  have hbase : 0 < (fixedKDensityFactor L p k : ℝ) := by
    exact_mod_cast fixedKDensityFactor_pos L p k
  exact mul_pos hbase (gramDetPadicNormFactor_pos L p)

lemma normalizedLocalDensityAtExponent_pos
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : IsLocalDensityAdmissibleExponent L p k) :
    0 < normalizedLocalDensityAtExponent L p k hk := by
  rw [normalizedLocalDensityAtExponent_eq_fixedKDensityWithGramDetFactor]
  exact fixedKDensityWithGramDetFactor_pos L p k

lemma normalizedLocalDensity_pos
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    0 < normalizedLocalDensity L p := by
  unfold normalizedLocalDensity
  exact normalizedLocalDensityAtExponent_pos L p (localDensityHenselExponent L p)
    (isLocalDensityHenselExponent_preferred (n := n) L p).admissible

lemma fixedKDensityFactor_eq_of_isLocallyIsometricAt
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p k : ℕ) [Fact (Nat.Prime p)]
    (h : L₀.IsLocallyIsometricAt L₁ p) :
    fixedKDensityFactor L₀ p k =
      fixedKDensityFactor L₁ p k := by
  rw [fixedKDensityFactor_eq_localDualQuotientCount,
    fixedKDensityFactor_eq_localDualQuotientCount,
    localDualQuotientCount_eq_of_isLocallyIsometricAt p k h]

lemma fixedKDensityWithGramDetFactor_eq_of_isLocallyIsometricAt
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p k : ℕ) [Fact (Nat.Prime p)]
    (h : L₀.IsLocallyIsometricAt L₁ p) :
    fixedKDensityWithGramDetFactor L₀ p k =
      fixedKDensityWithGramDetFactor L₁ p k := by
  rw [fixedKDensityWithGramDetFactor,
    fixedKDensityWithGramDetFactor,
    fixedKDensityFactor_eq_of_isLocallyIsometricAt p k h,
    gramDetPadicNormFactor_eq_of_isLocallyIsometricAt p h]

lemma normalizedLocalDensityAtExponent_eq_of_isLocallyIsometricAt
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p k : ℕ) [Fact (Nat.Prime p)]
    (h : L₀.IsLocallyIsometricAt L₁ p)
    (hk₀ : IsLocalDensityAdmissibleExponent L₀ p k)
    (hk₁ : IsLocalDensityAdmissibleExponent L₁ p k) :
    normalizedLocalDensityAtExponent L₀ p k hk₀ =
      normalizedLocalDensityAtExponent L₁ p k hk₁ := by
  unfold normalizedLocalDensityAtExponent
  exact fixedKDensityWithGramDetFactor_eq_of_isLocallyIsometricAt p k h

lemma normalizedLocalDensity_eq_of_isLocallyIsometricAt
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (p k : ℕ) [Fact (Nat.Prime p)]
    (h : L₀.IsLocallyIsometricAt L₁ p)
    (hk₀ : IsLocalDensityHenselExponent L₀ p k)
    (hk₁ : IsLocalDensityHenselExponent L₁ p k) :
    normalizedLocalDensity L₀ p = normalizedLocalDensity L₁ p := by
  rw [normalizedLocalDensity_eq_fixedK L₀ p k hk₀,
    normalizedLocalDensity_eq_fixedK L₁ p k hk₁]
  exact normalizedLocalDensityAtExponent_eq_of_isLocallyIsometricAt p k h
    hk₀.admissible hk₁.admissible

lemma normalizedLocalDensity_eq_of_isSameGenus
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (h : L₀.IsSameGenus L₁)
    (p : ℕ) [Fact (Nat.Prime p)] :
    normalizedLocalDensity L₀ p = normalizedLocalDensity L₁ p := by
  let k := max (padicValInt p L₀.polarDeterminant) (padicValInt p L₁.polarDeterminant) + 3
  exact normalizedLocalDensity_eq_of_isLocallyIsometricAt p k (h.1 p)
    (isLocalDensityHenselExponent_of_polarDeterminant_val_add_two_lt (n := n) L₀ p k (by
      dsimp [k]
      omega))
    (isLocalDensityHenselExponent_of_polarDeterminant_val_add_two_lt (n := n) L₁ p k (by
      dsimp [k]
      omega))

end PositiveDefiniteIntegralLattice

end

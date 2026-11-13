import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
import Mathlib.LinearAlgebra.Matrix.Symmetric
import SMSFormula.StandardAxiomsGuard

/-!
# Direct Type II hyperbolic peeling: arithmetic and bilinear core

No arbitrary-matrix normal-form theorem
is claimed by this file. The split step and the recursive residual certificates are
in `SplitStep` and `RecursiveAllH`. The arguments below are proof
scripts, not external computation.

The only finite tests in the Lean core have fixed, small domains.
-/

noncomputable section

namespace TypeIIDirectPeeling

abbrev R := ZMod 8
abbrev F := ZMod 2

def Even8 (a : R) : Prop := ∃ b : R, a = 2 * b

def Four8 (a : R) : Prop := a = 0 ∨ a = 4

instance (a : R) : Decidable (Even8 a) := by
  unfold Even8
  infer_instance

instance (a : R) : Decidable (Four8 a) := by
  unfold Four8
  infer_instance

/-- A tiny residue fact, with no division by two in `ZMod 8`. -/
theorem even_not_four (a : R) (ha : Even8 a) (h4 : ¬ Four8 a) :
    a = 2 ∨ a = 6 := by
  have h : ∀ a : R, Even8 a → ¬ Four8 a → a = 2 ∨ a = 6 := by
    decide
  exact h a ha h4

/-- Seven tests suffice. The last expression is the norm of `u+v+w` when
`a,b,c,ab,ac,bc` are the six preceding norm values. -/
theorem seven_even_values (a b c ab ac bc : R)
    (ha : Even8 a) (hb : Even8 b) (hc : Even8 c)
    (hab : Even8 ab) (hac : Even8 ac) (hbc : Even8 bc) :
    Four8 a ∨ Four8 b ∨ Four8 c ∨ Four8 ab ∨ Four8 ac ∨ Four8 bc ∨
      Four8 (ab + ac + bc - a - b - c) := by
  by_cases h : Four8 a
  · exact Or.inl h
  right
  have hA := even_not_four a ha h
  by_cases h : Four8 b
  · exact Or.inl h
  right
  have hB := even_not_four b hb h
  by_cases h : Four8 c
  · exact Or.inl h
  right
  have hC := even_not_four c hc h
  by_cases h : Four8 ab
  · exact Or.inl h
  right
  have hAB := even_not_four ab hab h
  by_cases h : Four8 ac
  · exact Or.inl h
  right
  have hAC := even_not_four ac hac h
  by_cases h : Four8 bc
  · exact Or.inl h
  right
  have hBC := even_not_four bc hbc h
  rcases hA with rfl | rfl <;>
    rcases hB with rfl | rfl <;>
    rcases hC with rfl | rfl <;>
    rcases hAB with rfl | rfl <;>
    rcases hAC with rfl | rfl <;>
    rcases hBC with rfl | rfl <;>
    decide

/-- Independent 64-case formulation of the three-coordinate test over F₂. -/
theorem ternary_binary_zero :
    ∀ a b c d e f : F, ∃ x y z : F,
      (x = 1 ∨ y = 1 ∨ z = 1) ∧
      a * x + b * y + c * z + d * x * y + e * x * z + f * y * z = 0 := by
  decide

/-- If a norm is already divisible by four, a single correction `2*t*z`
removes its remaining mod-eight bit. The new pairing is still a unit.
Here `q(z)=2*a`; the term involving its square is retained, not discarded
without proof. -/
theorem one_bit_correction :
    ∀ q b a : R, Four8 q → b ^ 2 = 1 → ∃ t : Fin 2,
      q + 2 * (2 * (t.val : R)) * b + (2 * (t.val : R)) ^ 2 * (2 * a) = 0 ∧
      (b + (2 * (t.val : R)) * (2 * a)) ^ 2 = 1 := by
  decide

/-- In F₂, nonzero means one. -/
theorem f2_eq_one_of_ne_zero : ∀ a : F, a ≠ 0 → a = 1 := by
  decide

/-- Reduction from the direct-H `ZMod 8` coefficient ring to `ZMod 2`. -/
def red8to2 : R →+* F := ZMod.castHom (by norm_num : 2 ∣ 8) F

/-- Internal evenness in `ZMod 8` is the same as vanishing after reduction to `ZMod 2`. -/
theorem even8_iff_red8to2_eq_zero (a : R) : Even8 a ↔ red8to2 a = 0 := by
  fin_cases a <;> decide

/-- A symmetric zero-diagonal matrix over `ZMod 2` has identically zero quadratic diagonal. -/
theorem zmod2_dot_mulVec_zero_of_isSymm_zero_diag {n : ℕ}
    (G : Matrix (Fin n) (Fin n) F) (hsymm : G.IsSymm) (hdiag : ∀ i, G i i = 0)
    (x : Fin n → F) :
    x ⬝ᵥ G.mulVec x = 0 := by
  induction n with
  | zero =>
      simp [dotProduct]
  | succ n ih =>
      let T : Matrix (Fin n) (Fin n) F := fun i j => G i.succ j.succ
      let t : Fin n → F := fun i => x i.succ
      have hTsymm : T.IsSymm := by
        rw [Matrix.IsSymm.ext_iff]
        intro i j
        exact hsymm.apply i.succ j.succ
      have hTdiag : ∀ i, T i i = 0 := by
        intro i
        exact hdiag i.succ
      have iht : t ⬝ᵥ T.mulVec t = 0 := ih T hTsymm hTdiag t
      have h00 : G 0 0 = 0 := hdiag 0
      simp only [dotProduct, Matrix.mulVec] at iht ⊢
      rw [Fin.sum_univ_succ]
      rw [show (∑ x_1 : Fin (n + 1), G 0 x_1 * x x_1) =
          G 0 0 * x 0 + ∑ j : Fin n, G 0 j.succ * x j.succ by
        rw [Fin.sum_univ_succ]]
      rw [h00]
      simp only [zero_mul, zero_add]
      rw [show (∑ x_1 : Fin n, x x_1.succ * ∑ x_2 : Fin (n + 1), G x_1.succ x_2 * x x_2) =
          (∑ i : Fin n, x i.succ * (G i.succ 0 * x 0)) +
          (∑ i : Fin n, x i.succ * ∑ j : Fin n, G i.succ j.succ * x j.succ) by
        simp only [Fin.sum_univ_succ]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
      ]
      rw [show (∑ i : Fin n, x i.succ * ∑ j : Fin n, G i.succ j.succ * x j.succ) = 0 by
        simpa [T, t, dotProduct, Matrix.mulVec] using iht]
      simp only [add_zero]
      have hcolrow : (∑ i : Fin n, x i.succ * (G i.succ 0 * x 0)) =
          x 0 * ∑ j : Fin n, G 0 j.succ * x j.succ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hsymm.apply i.succ 0]
        ring
      rw [hcolrow]
      rw [← two_mul]
      rw [show (2 : F) = 0 by decide]
      ring

/-- An alternating pairing cannot have its only nonzero coordinate at a
chosen unit coordinate of the original vector. This is the precise off-pivot
partner lemma needed to preserve the pivot entry during the mod-eight lift.
In the matrix adapter use `w = (G mod 2) * x`, nonsingularity for `w ≠ 0`,
and alternatingness for `x dot w = 0`. -/

theorem exists_partner_away_from_pivot
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x w : ι → F) (r : ι)
    (hxr : x r = 1) (hw : w ≠ 0)
    (horth : ∑ i, x i * w i = 0) :
    ∃ j, j ≠ r ∧ w j = 1 := by
  classical
  by_contra h
  have hzero : ∀ j, j ≠ r → w j = 0 := by
    intro j hj
    by_contra hjzero
    exact h ⟨j, hj, f2_eq_one_of_ne_zero (w j) hjzero⟩
  have hsum : (∑ i, x i * w i) = x r * w r := by
    apply Finset.sum_eq_single r
    · intro i _ hir
      rw [hzero i hir, mul_zero]
    · simp
  have hwr : w r = 0 := by
    rw [hxr, one_mul] at hsum
    exact hsum.symm.trans horth
  apply hw
  funext i
  by_cases hi : i = r
  · subst i
    exact hwr
  · exact hzero i hi

section Bilinear

variable {V : Type*} [AddCommGroup V] [Module R V]

abbrev Bil (V : Type*) [AddCommGroup V] [Module R V] := V →ₗ[R] V →ₗ[R] R

def quad (B : Bil V) (v : V) : R := B v v

def BilinearSymmetric (B : Bil V) : Prop := ∀ x y, B x y = B y x

/-- The third finite difference of a quadratic diagonal is zero. -/
theorem quad_three (B : Bil V) (u v w : V) :
    quad B (u + v + w) =
      quad B (u + v) + quad B (u + w) + quad B (v + w) -
        quad B u - quad B v - quad B w := by
  simp only [quad, map_add, LinearMap.add_apply]
  ring

/-- A support-at-most-three zero modulo four; the matrix adapter supplies
three distinct coordinate vectors, so every listed vector is primitive. -/
theorem seven_vector_test (B : Bil V) (heven : ∀ x, Even8 (quad B x)) (u v w : V) :
    Four8 (quad B u) ∨ Four8 (quad B v) ∨ Four8 (quad B w) ∨
    Four8 (quad B (u + v)) ∨ Four8 (quad B (u + w)) ∨
    Four8 (quad B (v + w)) ∨ Four8 (quad B (u + v + w)) := by
  rw [quad_three B u v w]
  exact seven_even_values _ _ _ _ _ _
    (heven u) (heven v) (heven w)
    (heven (u + v)) (heven (u + w)) (heven (v + w))

/-- Literal quadratic expansion, retaining the even diagonal term. -/
theorem quad_add_smul (B : Bil V) (hB : BilinearSymmetric B) (x z : V) (c : R) :
    quad B (x + c • z) = quad B x + 2 * c * B x z + c ^ 2 * quad B z := by
  simp only [quad, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hB z x]
  ring

def HyperbolicPair (B : Bil V) (x y : V) : Prop :=
  quad B x = 0 ∧ B x y = 1 ∧ quad B y = 0

/-- The partner can be isotropized explicitly. A unit in Z/8Z is its own
inverse. Given `B(z,z)=2*a`, use `y=B(x,z)*z-a*x`. -/
theorem explicit_partner (B : Bil V) (hB : BilinearSymmetric B) (x z : V) (a : R)
    (hx : quad B x = 0) (hz : quad B z = 2 * a) (hb : (B x z) ^ 2 = 1) :
    HyperbolicPair B x ((B x z) • z - a • x) := by
  refine ⟨hx, ?_, ?_⟩
  · calc
      B x ((B x z) • z - a • x) = (B x z) ^ 2 - a * quad B x := by
        simp only [map_sub, map_smul, smul_eq_mul, quad]
        ring
      _ = 1 := by rw [hx, hb]; ring
  · simp only [quad, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul]
    change B x x = 0 at hx
    change B z z = 2 * a at hz
    rw [hB z x, hx, hz]
    ring

/-- The whole one-bit-lift-and-partner operation, with no local classification
and no division by a nonunit. Primitive-coordinate preservation is a separate
coordinate fact: choose z=e_j with j different from the pivot. -/
theorem lift_to_hyperbolic_pair (B : Bil V) (hB : BilinearSymmetric B)
    (x₀ z : V) (a : R) (hq : Four8 (quad B x₀))
    (hz : quad B z = 2 * a) (hb : (B x₀ z) ^ 2 = 1) :
    ∃ t : Fin 2,
      let x := x₀ + (2 * (t.val : R)) • z
      HyperbolicPair B x ((B x z) • z - a • x) := by
  obtain ⟨t, htq, htb⟩ := one_bit_correction (quad B x₀) (B x₀ z) a hq hb
  refine ⟨t, ?_⟩
  dsimp only
  apply explicit_partner B hB _ z a
  · rw [quad_add_smul B hB, hz]
    exact htq
  · exact hz
  · have hzz : B z z = 2 * a := by simpa [quad] using hz
    simpa [quad, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, hzz] using htb

/-- Projection to the perpendicular complement of a hyperbolic pair. -/
def perpendicularProjection (B : Bil V) (x y v : V) : V :=
  v - (B v y) • x - (B v x) • y

/-- First orthogonality equation. -/
theorem projection_pair_left (B : Bil V) (hB : BilinearSymmetric B)
    (x y v : V) (hp : HyperbolicPair B x y) :
    B x (perpendicularProjection B x y v) = 0 := by
  rcases hp with ⟨hxx, hxy, hyy⟩
  change B x x = 0 at hxx
  simp only [perpendicularProjection, map_sub, map_smul, smul_eq_mul]
  rw [hxx, hxy, hB x v]
  ring

/-- Second orthogonality equation. -/
theorem projection_pair_right (B : Bil V) (hB : BilinearSymmetric B)
    (x y v : V) (hp : HyperbolicPair B x y) :
    B y (perpendicularProjection B x y v) = 0 := by
  rcases hp with ⟨hxx, hxy, hyy⟩
  change B y y = 0 at hyy
  simp only [perpendicularProjection, map_sub, map_smul, smul_eq_mul]
  rw [hB y x, hxy, hyy, hB y v]
  ring

/-- The exact rank-two Schur-complement formula. The future matrix adapter
sets u,v to the remaining coordinate vectors. This formula also proves the
residual evenness, since its diagonal correction is twice a product. -/
theorem projection_pairing (B : Bil V) (hB : BilinearSymmetric B)
    (x y u v : V) (hp : HyperbolicPair B x y) :
    B (perpendicularProjection B x y u) (perpendicularProjection B x y v) =
      B u v - B u x * B v y - B u y * B v x := by
  rcases hp with ⟨hxx, hxy, hyy⟩
  change B x x = 0 at hxx
  change B y y = 0 at hyy
  simp only [perpendicularProjection, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hB y x, hB x v, hB y v, hxx, hxy, hyy]
  ring

/-- Any linear functional killing the chosen plane is unchanged by projection.
For the explicit inverse matrix use f_l(v)=v_l-x_l*v_r. The partner formula
implies that f_l kills both x and y for l outside the two pivot coordinates. -/
theorem projection_coordinate (B : Bil V) (x y v : V) (f : V →ₗ[R] R)
    (hx : f x = 0) (hy : f y = 0) :
    f (perpendicularProjection B x y v) = f v := by
  simp [perpendicularProjection, map_sub, map_smul, hx, hy]

/-- A rank-one unipotent shear has an explicit inverse over any module. In
the coordinate adapter take f(v)=v_r and d=x-e_r with x_r=1. It sends e_r
to x and fixes every other coordinate vector. No projective-module freeness
or arbitrary basis-extension theorem is required. -/
def primitiveColumnShear (f : V →ₗ[R] R) (d : V) (hd : f d = 0) : V ≃ₗ[R] V where
  toFun v := v + (f v) • d
  invFun v := v - (f v) • d
  left_inv v := by simp [map_add, map_smul, hd]
  right_inv v := by simp [map_sub, map_smul, hd]
  map_add' u v := by
    simp only [map_add, add_smul]
    abel
  map_smul' c v := by
    simp [map_smul, smul_add, smul_smul]

end Bilinear

section MatrixAdapter

open Matrix

/-- The bilinear form associated to a finite matrix, written on coordinate functions. -/
def matrixBilinear {n : ℕ} (G : Matrix (Fin n) (Fin n) R) : Bil (Fin n → R) where
  toFun x :=
    { toFun := fun y => x ⬝ᵥ G.mulVec y
      map_add' := by
        intro y z
        rw [Matrix.mulVec_add]
        simp [dotProduct, Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro c y
        rw [Matrix.mulVec_smul]
        simp [dotProduct, Finset.mul_sum, mul_left_comm] }
  map_add' := by
    intro x y
    ext z
    simp [dotProduct, Finset.sum_add_distrib, add_mul]
  map_smul' := by
    intro c x
    ext z
    simp [dotProduct, Finset.mul_sum, mul_assoc, mul_comm]

@[simp] theorem matrixBilinear_apply {n : ℕ} (G : Matrix (Fin n) (Fin n) R)
    (x y : Fin n → R) :
    matrixBilinear G x y = x ⬝ᵥ G.mulVec y := rfl

/-- For symmetric matrices, row-vector multiplication matches column multiplication. -/
theorem matrix_vecMul_eq_mulVec_of_isSymm {n : ℕ} {G : Matrix (Fin n) (Fin n) R}
    (hG : G.IsSymm) (x : Fin n → R) :
    Matrix.vecMul x G = G.mulVec x := by
  ext i
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, hG.apply, mul_comm]

/-- The matrix bilinear form is symmetric when the matrix is symmetric. -/
theorem matrixBilinear_symmetric {n : ℕ} {G : Matrix (Fin n) (Fin n) R}
    (hG : G.IsSymm) : BilinearSymmetric (matrixBilinear G) := by
  intro x y
  simp only [matrixBilinear_apply]
  rw [Matrix.dotProduct_mulVec]
  rw [matrix_vecMul_eq_mulVec_of_isSymm hG]
  simp [dotProduct, mul_comm]

/-- The standard coordinate vector in the matrix adapter. -/
def basisVec (n : ℕ) (i : Fin n) : Fin n → R := Pi.single i 1

@[simp] theorem basisVec_apply_same {n : ℕ} (i : Fin n) : basisVec n i i = 1 := by
  simp [basisVec]

@[simp] theorem basisVec_apply_ne {n : ℕ} {i j : Fin n} (h : j ≠ i) :
    basisVec n i j = 0 := by
  simp [basisVec, Pi.single_eq_of_ne h]

/-- Matrix entries are the pairings of standard coordinate vectors. -/
theorem matrixBilinear_basis_basis {n : ℕ} (G : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    matrixBilinear G (basisVec n i) (basisVec n j) = G i j := by
  simp [matrixBilinear, basisVec, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Pairing a standard vector on the left reads the corresponding row evaluation. -/
theorem matrixBilinear_basis_left {n : ℕ} (G : Matrix (Fin n) (Fin n) R)
    (i : Fin n) (v : Fin n → R) :
    matrixBilinear G (basisVec n i) v = G.mulVec v i := by
  simp [matrixBilinear, basisVec, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Pairing a standard vector on the right reads the corresponding column evaluation. -/
theorem matrixBilinear_basis_right {n : ℕ} (G : Matrix (Fin n) (Fin n) R)
    (v : Fin n → R) (j : Fin n) :
    matrixBilinear G v (basisVec n j) = Matrix.vecMul v G j := by
  simp [matrixBilinear, basisVec, Matrix.vecMul, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- For symmetric matrices, right standard-vector pairings are row evaluations too. -/
theorem matrixBilinear_basis_right_of_isSymm {n : ℕ} {G : Matrix (Fin n) (Fin n) R}
    (hG : G.IsSymm) (v : Fin n → R) (j : Fin n) :
    matrixBilinear G v (basisVec n j) = G.mulVec v j := by
  rw [matrixBilinear_basis_right]
  exact congrFun (matrix_vecMul_eq_mulVec_of_isSymm hG v) j

/-- Diagonal entries are the norms of standard coordinate vectors. -/
theorem matrixBilinear_quad_basis {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    quad (matrixBilinear G) (basisVec n i) = G i i := by
  exact matrixBilinear_basis_basis G i i


/-- Reduction modulo two of the matrix quadratic value attached to `G`. -/
theorem red8to2_matrixBilinear_quad {n : ℕ} (G : Matrix (Fin n) (Fin n) R)
    (x : Fin n → R) :
    red8to2 (quad (matrixBilinear G) x) =
      (fun i => red8to2 (x i)) ⬝ᵥ (G.map red8to2).mulVec (fun i => red8to2 (x i)) := by
  simp [quad, matrixBilinear, Matrix.mulVec, dotProduct, map_sum]

/-- Even symmetric mod-eight Gram matrices satisfy the abstract evenness hypothesis of the peeling core. -/
theorem matrixBilinear_quad_even_of_isSymm_even_diag {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (x : Fin n → R) :
    Even8 (quad (matrixBilinear G) x) := by
  rw [even8_iff_red8to2_eq_zero]
  rw [red8to2_matrixBilinear_quad]
  apply zmod2_dot_mulVec_zero_of_isSymm_zero_diag
  · rw [Matrix.IsSymm.ext_iff]
    intro i j
    simp [Matrix.map_apply, hsymm.apply i j]
  · intro i
    exact (even8_iff_red8to2_eq_zero (G i i)).mp (hdiag i)


/-- The seven-vector test specialized to a symmetric even mod-eight Gram matrix. -/
theorem matrixBilinear_seven_vector_test {n : ℕ} {G : Matrix (Fin n) (Fin n) R}
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i)) (u v w : Fin n → R) :
    Four8 (quad (matrixBilinear G) u) ∨ Four8 (quad (matrixBilinear G) v) ∨
    Four8 (quad (matrixBilinear G) w) ∨ Four8 (quad (matrixBilinear G) (u + v)) ∨
    Four8 (quad (matrixBilinear G) (u + w)) ∨
    Four8 (quad (matrixBilinear G) (v + w)) ∨
    Four8 (quad (matrixBilinear G) (u + v + w)) := by
  exact seven_vector_test (matrixBilinear G)
    (matrixBilinear_quad_even_of_isSymm_even_diag hsymm hdiag) u v w

/-- The seven-vector test for three concrete coordinate vectors. -/
theorem matrixBilinear_seven_coordinate_test {n : ℕ} {G : Matrix (Fin n) (Fin n) R}
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i)) (i j k : Fin n) :
    Four8 (quad (matrixBilinear G) (basisVec n i)) ∨
    Four8 (quad (matrixBilinear G) (basisVec n j)) ∨
    Four8 (quad (matrixBilinear G) (basisVec n k)) ∨
    Four8 (quad (matrixBilinear G) (basisVec n i + basisVec n j)) ∨
    Four8 (quad (matrixBilinear G) (basisVec n i + basisVec n k)) ∨
    Four8 (quad (matrixBilinear G) (basisVec n j + basisVec n k)) ∨
    Four8 (quad (matrixBilinear G) (basisVec n i + basisVec n j + basisVec n k)) := by
  exact matrixBilinear_seven_vector_test hsymm hdiag (basisVec n i) (basisVec n j) (basisVec n k)

/-- A mod-two matrix with a left inverse supplies the off-pivot partner used by the peeling core. -/
theorem exists_matrix_partner_away_from_pivot_of_left_inverse {n : ℕ}
    (G W : Matrix (Fin n) (Fin n) F) (hWG : W * G = 1)
    (hsymm : G.IsSymm) (hdiag : ∀ i, G i i = 0)
    (x : Fin n → F) (r : Fin n) (hxr : x r = 1) :
    ∃ j, j ≠ r ∧ G.mulVec x j = 1 := by
  apply exists_partner_away_from_pivot x (G.mulVec x) r hxr
  · intro hw
    have hxzero : x = 0 := by
      calc
        x = W.mulVec (G.mulVec x) := by
          symm
          rw [Matrix.mulVec_mulVec, hWG, Matrix.one_mulVec]
        _ = 0 := by
          rw [hw]
          simp
    have hzero : x r = 0 := by
      rw [hxzero]
      rfl
    have hbad : (1 : F) = 0 := by
      rw [hxr] at hzero
      exact hzero
    exact (by decide : (1 : F) ≠ 0) hbad
  · simpa [dotProduct] using zmod2_dot_mulVec_zero_of_isSymm_zero_diag G hsymm hdiag x

/-- The off-pivot partner statement transported back to the original mod-eight matrix. -/
theorem exists_matrix_partner_away_from_pivot_mod8 {n : ℕ}
    (G W : Matrix (Fin n) (Fin n) R)
    (hWG : (W.map red8to2) * (G.map red8to2) = 1)
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (x : Fin n → R) (r : Fin n) (hxr : red8to2 (x r) = 1) :
    ∃ j, j ≠ r ∧ red8to2 (G.mulVec x j) = 1 := by
  let x₂ : Fin n → F := fun i => red8to2 (x i)
  have hsymm₂ : (G.map red8to2).IsSymm := by
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    simp [Matrix.map_apply, hsymm.apply i j]
  have hdiag₂ : ∀ i, (G.map red8to2) i i = 0 := by
    intro i
    exact (even8_iff_red8to2_eq_zero (G i i)).mp (hdiag i)
  obtain ⟨j, hjr, hj⟩ := exists_matrix_partner_away_from_pivot_of_left_inverse
    (G.map red8to2) (W.map red8to2) hWG hsymm₂ hdiag₂ x₂ r hxr
  refine ⟨j, hjr, ?_⟩
  calc
    red8to2 (G.mulVec x j) =
        (fun i => red8to2 (G j i)) ⬝ᵥ (fun i => red8to2 (x i)) := by
      simp [Matrix.mulVec, dotProduct, map_sum]
    _ = 1 := hj

/-- Symmetry turns a right inverse over `ZMod 8` into the mod-two left inverse needed above. -/
theorem mod2_left_inverse_transpose_of_isSymm_right_inverse {n : ℕ}
    {G V : Matrix (Fin n) (Fin n) R} (hGV : G * V = 1) (hsymm : G.IsSymm) :
    (V.transpose.map red8to2) * (G.map red8to2) = 1 := by
  have hleft : V.transpose * G = 1 := by
    calc
      V.transpose * G = (G * V).transpose := by
        rw [Matrix.transpose_mul]
        ext i j
        simp [Matrix.mul_apply, Matrix.transpose_apply, hsymm.apply]
      _ = 1 := by
        rw [hGV]
        simp
  rw [← Matrix.map_mul, hleft]
  simp

/-- The off-pivot partner statement from a symmetric mod-eight matrix with a right inverse. -/
theorem exists_matrix_partner_away_from_pivot_of_right_inverse_mod8 {n : ℕ}
    (G V : Matrix (Fin n) (Fin n) R) (hGV : G * V = 1)
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (x : Fin n → R) (r : Fin n) (hxr : red8to2 (x r) = 1) :
    ∃ j, j ≠ r ∧ red8to2 (G.mulVec x j) = 1 := by
  exact exists_matrix_partner_away_from_pivot_mod8 G V.transpose
    (mod2_left_inverse_transpose_of_isSymm_right_inverse hGV hsymm) hsymm hdiag x r hxr

/-- In `ZMod 8`, every element reducing to one modulo two has square one. -/
theorem sq_eq_one_of_red8to2_eq_one (a : R) (ha : red8to2 a = 1) : a ^ 2 = 1 := by
  have h : ∀ a : R, red8to2 a = 1 → a ^ 2 = 1 := by
    decide
  exact h a ha

/-- The off-pivot partner can be chosen as a coordinate vector with unit pairing. -/
theorem exists_basis_partner_sq_eq_one_of_right_inverse_mod8 {n : ℕ}
    (G V : Matrix (Fin n) (Fin n) R) (hGV : G * V = 1)
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (x : Fin n → R) (r : Fin n) (hxr : red8to2 (x r) = 1) :
    ∃ j, j ≠ r ∧ (matrixBilinear G x (basisVec n j)) ^ 2 = 1 := by
  obtain ⟨j, hjr, hj⟩ := exists_matrix_partner_away_from_pivot_of_right_inverse_mod8
    G V hGV hsymm hdiag x r hxr
  refine ⟨j, hjr, ?_⟩
  apply sq_eq_one_of_red8to2_eq_one
  simpa [matrixBilinear_basis_right_of_isSymm hsymm x j] using hj

/-- A primitive vector with norm divisible by four extends to an explicit hyperbolic pair. -/
theorem exists_hyperbolic_pair_from_four8_vector_of_right_inverse_mod8 {n : ℕ}
    (G V : Matrix (Fin n) (Fin n) R) (hGV : G * V = 1)
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (x₀ : Fin n → R) (r : Fin n) (hxr : red8to2 (x₀ r) = 1)
    (hq : Four8 (quad (matrixBilinear G) x₀)) :
    ∃ j, j ≠ r ∧ ∃ a : R, ∃ t : Fin 2,
      let z := basisVec n j
      let x := x₀ + (2 * (t.val : R)) • z
      quad (matrixBilinear G) z = 2 * a ∧
        HyperbolicPair (matrixBilinear G) x
          ((matrixBilinear G x z) • z - a • x) := by
  obtain ⟨j, hjr, hb⟩ := exists_basis_partner_sq_eq_one_of_right_inverse_mod8
    G V hGV hsymm hdiag x₀ r hxr
  rcases hdiag j with ⟨a, ha⟩
  have hz : quad (matrixBilinear G) (basisVec n j) = 2 * a := by
    simpa [matrixBilinear_quad_basis] using ha
  obtain ⟨t, ht⟩ := lift_to_hyperbolic_pair (matrixBilinear G)
    (matrixBilinear_symmetric hsymm) x₀ (basisVec n j) a hq hz hb
  refine ⟨j, hjr, a, t, ?_⟩
  exact ⟨hz, ht⟩

/-- A standard coordinate vector has odd pivot coordinate at its own index. -/
theorem red8to2_basisVec_self {n : ℕ} (i : Fin n) :
    red8to2 (basisVec n i i) = 1 := by
  simp [basisVec, red8to2]

/-- Adding a different coordinate vector preserves the left pivot modulo two. -/
theorem red8to2_basisVec_add_left {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    red8to2 ((basisVec n i + basisVec n j) i) = 1 := by
  have hj : basisVec n j i = 0 := basisVec_apply_ne hij
  simp [hj, red8to2]

/-- Adding two different coordinate vectors preserves the left pivot modulo two. -/
theorem red8to2_basisVec_add_add_left {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) :
    red8to2 ((basisVec n i + basisVec n j + basisVec n k) i) = 1 := by
  have hj : basisVec n j i = 0 := basisVec_apply_ne hij
  have hk : basisVec n k i = 0 := basisVec_apply_ne hik
  simp [hj, hk, red8to2]

/-- The seven-coordinate test and the partner bridge produce a local hyperbolic pair.
This is the first all-matrix selection layer before the future split/residual
certificate construction. -/
theorem exists_hyperbolic_pair_from_three_coordinates_of_right_inverse_mod8 {n : ℕ}
    (G V : Matrix (Fin n) (Fin n) R) (hGV : G * V = 1)
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ x₀ : Fin n → R, ∃ r : Fin n,
      red8to2 (x₀ r) = 1 ∧ Four8 (quad (matrixBilinear G) x₀) ∧
        ∃ j', j' ≠ r ∧ ∃ a : R, ∃ t : Fin 2,
          let z := basisVec n j'
          let x := x₀ + (2 * (t.val : R)) • z
          quad (matrixBilinear G) z = 2 * a ∧
            HyperbolicPair (matrixBilinear G) x
              ((matrixBilinear G x z) • z - a • x) := by
  have hseven := matrixBilinear_seven_coordinate_test hsymm hdiag i j k
  let finish (x₀ : Fin n → R) (r : Fin n)
      (hxr : red8to2 (x₀ r) = 1)
      (hq : Four8 (quad (matrixBilinear G) x₀)) :
      ∃ x₀ : Fin n → R, ∃ r : Fin n,
        red8to2 (x₀ r) = 1 ∧ Four8 (quad (matrixBilinear G) x₀) ∧
          ∃ j', j' ≠ r ∧ ∃ a : R, ∃ t : Fin 2,
            let z := basisVec n j'
            let x := x₀ + (2 * (t.val : R)) • z
            quad (matrixBilinear G) z = 2 * a ∧
              HyperbolicPair (matrixBilinear G) x
                ((matrixBilinear G x z) • z - a • x) := by
    refine ⟨x₀, r, hxr, hq, ?_⟩
    exact exists_hyperbolic_pair_from_four8_vector_of_right_inverse_mod8
      G V hGV hsymm hdiag x₀ r hxr hq
  rcases hseven with hq | hq | hq | hq | hq | hq | hq
  · exact finish (basisVec n i) i (red8to2_basisVec_self i) hq
  · exact finish (basisVec n j) j (red8to2_basisVec_self j) hq
  · exact finish (basisVec n k) k (red8to2_basisVec_self k) hq
  · exact finish (basisVec n i + basisVec n j) i
      (red8to2_basisVec_add_left hij) hq
  · exact finish (basisVec n i + basisVec n k) i
      (red8to2_basisVec_add_left hik) hq
  · exact finish (basisVec n j + basisVec n k) j
      (red8to2_basisVec_add_left hjk) hq
  · exact finish (basisVec n i + basisVec n j + basisVec n k) i
      (red8to2_basisVec_add_add_left hij hik) hq

/-- The coordinates remaining after the chosen hyperbolic pair pivots. -/
abbrev RemainingIndex (n : ℕ) (r j : Fin n) := {l : Fin n // l ≠ r ∧ l ≠ j}

/-- The split index type, consisting of the two chosen hyperbolic coordinates and the
remaining coordinates, is equivalent to the original coordinate index once the pivots are
distinct. -/
def splitPairIndexEquiv {n : ℕ} {r j : Fin n} (hrj : r ≠ j) :
    (Fin 2 ⊕ RemainingIndex n r j) ≃ Fin n where
  toFun a :=
    match a with
    | Sum.inl p => if p = 0 then r else j
    | Sum.inr l => l.1
  invFun i :=
    if hir : i = r then Sum.inl 0
    else if hij : i = j then Sum.inl 1
    else Sum.inr ⟨i, hir, hij⟩
  left_inv a := by
    cases a with
    | inl p =>
        fin_cases p
        · simp
        · have hjr : j ≠ r := Ne.symm hrj
          simp [hjr]
    | inr l =>
        simp [l.2.1, l.2.2]
  right_inv i := by
    by_cases hir : i = r
    · simp [hir]
    · by_cases hij : i = j
      · have hjr : j ≠ r := Ne.symm hrj
        simp [hij, hjr]
      · simp [hir, hij]

@[simp] theorem splitPairIndexEquiv_inl_zero {n : ℕ} {r j : Fin n} (hrj : r ≠ j) :
    splitPairIndexEquiv (n := n) hrj (Sum.inl 0) = r := by
  simp [splitPairIndexEquiv]

@[simp] theorem splitPairIndexEquiv_inl_one {n : ℕ} {r j : Fin n} (hrj : r ≠ j) :
    splitPairIndexEquiv (n := n) hrj (Sum.inl 1) = j := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp [splitPairIndexEquiv, h10]

@[simp] theorem splitPairIndexEquiv_inr {n : ℕ} {r j : Fin n} (hrj : r ≠ j)
    (l : RemainingIndex n r j) :
    splitPairIndexEquiv (n := n) hrj (Sum.inr l) = l.1 := by
  simp [splitPairIndexEquiv]

/-- The coordinate selector can be strengthened to the exact hypotheses needed by the
split-step certificate: the chosen corrected vector still has pivot coordinate exactly
one, and the explicit partner satisfies the residual inverse-row coordinate relation. -/
theorem exists_split_pair_from_three_coordinates_of_right_inverse_mod8 {n : ℕ}
    (G V : Matrix (Fin n) (Fin n) R) (hGV : G * V = 1)
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ x y : Fin n → R, ∃ r s : Fin n,
      r ≠ s ∧ HyperbolicPair (matrixBilinear G) x y ∧ x r = 1 ∧
        (∀ l : RemainingIndex n r s, y l.1 = x l.1 * y r) := by
  have hseven := matrixBilinear_seven_coordinate_test hsymm hdiag i j k
  let finish (x₀ : Fin n → R) (r : Fin n)
      (hxr1 : x₀ r = 1)
      (hq : Four8 (quad (matrixBilinear G) x₀)) :
      ∃ x y : Fin n → R, ∃ r s : Fin n,
        r ≠ s ∧ HyperbolicPair (matrixBilinear G) x y ∧ x r = 1 ∧
          (∀ l : RemainingIndex n r s, y l.1 = x l.1 * y r) := by
    have hxr_red : red8to2 (x₀ r) = 1 := by
      simp [hxr1, red8to2]
    obtain ⟨s, hsr, a, t, _hz, hp⟩ :=
      exists_hyperbolic_pair_from_four8_vector_of_right_inverse_mod8
        G V hGV hsymm hdiag x₀ r hxr_red hq
    let z := basisVec n s
    let x := x₀ + (2 * (t.val : R)) • z
    let y := (matrixBilinear G x z) • z - a • x
    have hrz : z r = 0 := basisVec_apply_ne (Ne.symm hsr)
    have hxr : x r = 1 := by
      simp [x, z, hrz, hxr1]
    have hy : ∀ l : RemainingIndex n r s, y l.1 = x l.1 * y r := by
      intro l
      have hzl : z l.1 = 0 := basisVec_apply_ne l.2.2
      simp [y, hzl, hrz, hxr]
      ring
    exact ⟨x, y, r, s, Ne.symm hsr, hp, hxr, hy⟩
  rcases hseven with hq | hq | hq | hq | hq | hq | hq
  · exact finish (basisVec n i) i (by simp [basisVec]) hq
  · exact finish (basisVec n j) j (by simp [basisVec]) hq
  · exact finish (basisVec n k) k (by simp [basisVec]) hq
  · exact finish (basisVec n i + basisVec n j) i (by
      have hj : basisVec n j i = 0 := basisVec_apply_ne hij
      simp [hj]) hq
  · exact finish (basisVec n i + basisVec n k) i (by
      have hk : basisVec n k i = 0 := basisVec_apply_ne hik
      simp [hk]) hq
  · exact finish (basisVec n j + basisVec n k) j (by
      have hk : basisVec n k j = 0 := basisVec_apply_ne hjk
      simp [hk]) hq
  · exact finish (basisVec n i + basisVec n j + basisVec n k) i (by
      have hj : basisVec n j i = 0 := basisVec_apply_ne hij
      have hk : basisVec n k i = 0 := basisVec_apply_ne hik
      simp [hj, hk]) hq

/-- The column family for the first split step: the hyperbolic pair followed by
projected remaining coordinate vectors. -/
def splitPairColumn {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R)
    (r j : Fin n) : Fin 2 ⊕ RemainingIndex n r j → Fin n → R
  | Sum.inl a => if a = 0 then x else y
  | Sum.inr l => perpendicularProjection (matrixBilinear G) x y (basisVec n l.1)

/-- The corresponding square change-of-basis matrix, before reindexing the residual block. -/
def splitPairChangeMatrix {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R)
    (r j : Fin n) : Matrix (Fin n) (Fin 2 ⊕ RemainingIndex n r j) R :=
  fun i a => splitPairColumn G x y r j a i

/-- The split target matrix: one hyperbolic plane plus the projected residual block. -/
def splitPairTargetMatrix {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R)
    (r j : Fin n) : Matrix (Fin 2 ⊕ RemainingIndex n r j)
      (Fin 2 ⊕ RemainingIndex n r j) R :=
  fun a b =>
    match a, b with
    | Sum.inl p, Sum.inl q => if p = q then 0 else 1
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr l, Sum.inr m =>
        matrixBilinear G
          (perpendicularProjection (matrixBilinear G) x y (basisVec n l.1))
          (perpendicularProjection (matrixBilinear G) x y (basisVec n m.1))

/-- Row-vector multiplication paired with a column is the matrix bilinear form. -/
theorem vecMul_dotProduct_eq_matrixBilinear {n : ℕ}
    (G : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) :
    Matrix.vecMul u G ⬝ᵥ v = matrixBilinear G u v := by
  calc
    Matrix.vecMul u G ⬝ᵥ v = ∑ i, (∑ k, u k * G k i) * v i := by
      simp [Matrix.vecMul, dotProduct]
    _ = ∑ i, ∑ k, (u k * G k i) * v i := by
      simp [Finset.sum_mul]
    _ = ∑ k, ∑ i, (u k * G k i) * v i := by
      rw [Finset.sum_comm]
    _ = ∑ k, u k * (∑ i, G k i * v i) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = matrixBilinear G u v := by
      simp [matrixBilinear, Matrix.mulVec, dotProduct]

/-- The residual inverse rows are the functionals `v_l - x_l v_r`. -/
def residualCoordinateFunctional {n : ℕ} (x : Fin n → R) (r l : Fin n) :
    (Fin n → R) →ₗ[R] R where
  toFun v := v l - x l * v r
  map_add' u v := by
    simp [Pi.add_apply, mul_add]
    ring
  map_smul' c v := by
    simp [Pi.smul_apply, smul_eq_mul]
    ring

/-- The coefficient row for a residual coordinate realizes `residualCoordinateFunctional`. -/
theorem residualRow_dotProduct {n : ℕ} (x v : Fin n → R) (r l : Fin n) :
    (fun i => basisVec n l i - x l * basisVec n r i) ⬝ᵥ v =
      residualCoordinateFunctional x r l v := by
  have hleft : (∑ i, basisVec n l i * v i) = v l := by
    rw [Finset.sum_eq_single l]
    · simp [basisVec]
    · intro b _ hb
      simp [basisVec, Pi.single_eq_of_ne hb]
    · simp
  have hright : (∑ i, x l * (basisVec n r i * v i)) = x l * v r := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_eq_single r]
    · simp [basisVec]
    · intro b _ hb
      simp [basisVec, Pi.single_eq_of_ne hb]
    · simp
  calc
    (fun i => basisVec n l i - x l * basisVec n r i) ⬝ᵥ v =
        (∑ i, basisVec n l i * v i) - ∑ i, x l * (basisVec n r i * v i) := by
      simp [dotProduct, sub_mul, Finset.sum_sub_distrib, mul_assoc]
    _ = v l - x l * v r := by rw [hleft, hright]
    _ = residualCoordinateFunctional x r l v := rfl

/-- The explicit inverse rows for the first split step.  The first two rows are
`yᵀG` and `xᵀG`; the residual rows are `e_lᵀ - x_l e_rᵀ`. -/
def splitPairInverseMatrix {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R)
    (r j : Fin n) : Matrix (Fin 2 ⊕ RemainingIndex n r j) (Fin n) R
  | Sum.inl a, i => if a = 0 then Matrix.vecMul y G i else Matrix.vecMul x G i
  | Sum.inr l, i => basisVec n l.1 i - x l.1 * basisVec n r i

/-- The explicit inverse rows are a left inverse for the split-pair columns, assuming
the coordinate relation supplied by the concrete partner formula. -/
theorem splitPairInverseMatrix_mul_change {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n}
    (hsymm : G.IsSymm) (hp : HyperbolicPair (matrixBilinear G) x y)
    (hxr : x r = 1)
    (hy : ∀ l : RemainingIndex n r j, y l.1 = x l.1 * y r) :
    splitPairInverseMatrix G x y r j * splitPairChangeMatrix G x y r j = 1 := by
  ext a b
  rcases hp with ⟨hxx, hxy, hyy⟩
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          fin_cases a <;> fin_cases b
          · have hyx : matrixBilinear G y x = 1 := by
              rw [matrixBilinear_symmetric hsymm y x, hxy]
            rw [Matrix.mul_apply]
            change Matrix.vecMul y G ⬝ᵥ x = 1
            rw [vecMul_dotProduct_eq_matrixBilinear]
            exact hyx
          · rw [Matrix.mul_apply]
            change Matrix.vecMul y G ⬝ᵥ y = 0
            rw [vecMul_dotProduct_eq_matrixBilinear]
            simpa [quad] using hyy
          · rw [Matrix.mul_apply]
            change Matrix.vecMul x G ⬝ᵥ x = 0
            rw [vecMul_dotProduct_eq_matrixBilinear]
            simpa [quad] using hxx
          · rw [Matrix.mul_apply]
            change Matrix.vecMul x G ⬝ᵥ y = 1
            rw [vecMul_dotProduct_eq_matrixBilinear]
            exact hxy
      | inr b =>
          fin_cases a
          · have h := projection_pair_right (matrixBilinear G) (matrixBilinear_symmetric hsymm) x y
                (basisVec n b.1) ⟨hxx, hxy, hyy⟩
            rw [Matrix.mul_apply]
            change Matrix.vecMul y G ⬝ᵥ
              perpendicularProjection (matrixBilinear G) x y (basisVec n b.1) = 0
            rw [vecMul_dotProduct_eq_matrixBilinear]
            exact h
          · have h := projection_pair_left (matrixBilinear G) (matrixBilinear_symmetric hsymm) x y
                (basisVec n b.1) ⟨hxx, hxy, hyy⟩
            rw [Matrix.mul_apply]
            change Matrix.vecMul x G ⬝ᵥ
              perpendicularProjection (matrixBilinear G) x y (basisVec n b.1) = 0
            rw [vecMul_dotProduct_eq_matrixBilinear]
            exact h
  | inr a =>
      let f := residualCoordinateFunctional x r a.1
      have hfx : f x = 0 := by
        simp [f, residualCoordinateFunctional, hxr]
      have hfy : f y = 0 := by
        simp [f, residualCoordinateFunctional, hy a]
      cases b with
      | inl b =>
          fin_cases b
          · rw [Matrix.mul_apply]
            change (fun i => basisVec n a.1 i - x a.1 * basisVec n r i) ⬝ᵥ x = 0
            rw [residualRow_dotProduct]
            exact hfx
          · rw [Matrix.mul_apply]
            change (fun i => basisVec n a.1 i - x a.1 * basisVec n r i) ⬝ᵥ y = 0
            rw [residualRow_dotProduct]
            exact hfy
      | inr b =>
          rw [Matrix.mul_apply]
          change (fun i => basisVec n a.1 i - x a.1 * basisVec n r i) ⬝ᵥ
              perpendicularProjection (matrixBilinear G) x y (basisVec n b.1) =
            ((1 : Matrix (Fin 2 ⊕ RemainingIndex n r j)
                (Fin 2 ⊕ RemainingIndex n r j) R) (Sum.inr a) (Sum.inr b))
          rw [residualRow_dotProduct]
          change f (perpendicularProjection (matrixBilinear G) x y (basisVec n b.1)) =
            ((1 : Matrix (Fin 2 ⊕ RemainingIndex n r j)
                (Fin 2 ⊕ RemainingIndex n r j) R) (Sum.inr a) (Sum.inr b))
          rw [projection_coordinate (matrixBilinear G) x y (basisVec n b.1) f hfx hfy]
          by_cases hab : a = b
          · subst b
            have har : a.1 ≠ r := a.2.1
            simp [f, residualCoordinateFunctional, basisVec, har]
          · have hcoord : b.1 ≠ a.1 := by
              intro hba
              apply hab
              exact Subtype.ext hba.symm
            have hbr : r ≠ b.1 := Ne.symm b.2.1
            simp [f, residualCoordinateFunctional, basisVec, hcoord, hbr, hab]

/-- The split-pair change matrix with rows reindexed by the new split coordinates. -/
def splitPairSquareChangeMatrix {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R)
    {r j : Fin n} (hrj : r ≠ j) :
    Matrix (Fin 2 ⊕ RemainingIndex n r j) (Fin 2 ⊕ RemainingIndex n r j) R :=
  (splitPairChangeMatrix G x y r j).submatrix (splitPairIndexEquiv hrj) id

/-- The explicit inverse rows with columns reindexed by the new split coordinates. -/
def splitPairSquareInverseMatrix {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R)
    {r j : Fin n} (hrj : r ≠ j) :
    Matrix (Fin 2 ⊕ RemainingIndex n r j) (Fin 2 ⊕ RemainingIndex n r j) R :=
  (splitPairInverseMatrix G x y r j).submatrix id (splitPairIndexEquiv hrj)

/-- After reindexing rows and columns to the same split-coordinate type, the explicit
inverse rows are a left inverse for the split-pair change matrix. -/
theorem splitPairSquareInverseMatrix_mul_change {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n} (hrj : r ≠ j)
    (hsymm : G.IsSymm) (hp : HyperbolicPair (matrixBilinear G) x y)
    (hxr : x r = 1)
    (hy : ∀ l : RemainingIndex n r j, y l.1 = x l.1 * y r) :
    splitPairSquareInverseMatrix G x y hrj * splitPairSquareChangeMatrix G x y hrj = 1 := by
  ext a b
  have h := congrArg (fun M => M a b) (splitPairInverseMatrix_mul_change hsymm hp hxr hy)
  change (splitPairInverseMatrix G x y r j * splitPairChangeMatrix G x y r j) a b =
    ((1 : Matrix (Fin 2 ⊕ RemainingIndex n r j) (Fin 2 ⊕ RemainingIndex n r j) R) a b) at h
  rw [Matrix.mul_apply] at h
  rw [Matrix.mul_apply]
  simpa [splitPairSquareInverseMatrix, splitPairSquareChangeMatrix, Matrix.one_apply,
    ← (splitPairIndexEquiv hrj).sum_comp
      (fun i => splitPairInverseMatrix G x y r j a i * splitPairChangeMatrix G x y r j i b)] using h

/-- The reindexed split-pair change matrix is also a right inverse to the reindexed
explicit inverse rows. -/
theorem splitPairSquareChangeMatrix_mul_inverse {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n} (hrj : r ≠ j)
    (hsymm : G.IsSymm) (hp : HyperbolicPair (matrixBilinear G) x y)
    (hxr : x r = 1)
    (hy : ∀ l : RemainingIndex n r j, y l.1 = x l.1 * y r) :
    splitPairSquareChangeMatrix G x y hrj * splitPairSquareInverseMatrix G x y hrj = 1 := by
  exact mul_eq_one_comm.mp (splitPairSquareInverseMatrix_mul_change hrj hsymm hp hxr hy)

/-- The split target matrix is symmetric when the original Gram matrix is symmetric. -/
theorem splitPairTargetMatrix_isSymm {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n}
    (hsymm : G.IsSymm) :
    (splitPairTargetMatrix G x y r j).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro a b
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          fin_cases a <;> fin_cases b <;> simp [splitPairTargetMatrix]
      | inr b =>
          fin_cases a <;> simp [splitPairTargetMatrix]
  | inr a =>
      cases b with
      | inl b =>
          fin_cases b <;> simp [splitPairTargetMatrix]
      | inr b =>
          simpa [splitPairTargetMatrix] using
            (matrixBilinear_symmetric hsymm
              (perpendicularProjection (matrixBilinear G) x y (basisVec n a.1))
              (perpendicularProjection (matrixBilinear G) x y (basisVec n b.1))).symm

/-- Matrix multiplication by the split-pair column matrix computes the bilinear pairing
of the selected columns. -/
theorem splitPairChangeMatrix_contraction {n : ℕ}
    (G : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) (r j : Fin n)
    (a b : Fin 2 ⊕ RemainingIndex n r j) :
    ((splitPairChangeMatrix G x y r j).transpose * G * splitPairChangeMatrix G x y r j) a b =
      matrixBilinear G (splitPairColumn G x y r j a) (splitPairColumn G x y r j b) := by
  let T := splitPairChangeMatrix G x y r j
  calc
    (T.transpose * G * T) a b = ∑ i, (∑ k, T k a * G k i) * T i b := by
      simp [Matrix.mul_apply]
    _ = ∑ i, ∑ k, (T k a * G k i) * T i b := by
      simp [Finset.sum_mul]
    _ = ∑ k, ∑ i, (T k a * G k i) * T i b := by
      rw [Finset.sum_comm]
    _ = ∑ k, T k a * (∑ i, G k i * T i b) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = matrixBilinear G (splitPairColumn G x y r j a) (splitPairColumn G x y r j b) := by
      simp [T, splitPairChangeMatrix, matrixBilinear, Matrix.mulVec, dotProduct]

/-- The selected columns split off one hyperbolic plane and the projected residual block. -/
theorem splitPairChangeMatrix_congruence {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n}
    (hsymm : G.IsSymm) (hp : HyperbolicPair (matrixBilinear G) x y) :
    (splitPairChangeMatrix G x y r j).transpose * G * splitPairChangeMatrix G x y r j =
      splitPairTargetMatrix G x y r j := by
  ext a b
  rw [splitPairChangeMatrix_contraction]
  rcases hp with ⟨hxx, hxy, hyy⟩
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          fin_cases a <;> fin_cases b
          · simpa [splitPairColumn, splitPairTargetMatrix, quad] using hxx
          · simpa [splitPairColumn, splitPairTargetMatrix] using hxy
          · have hyx : matrixBilinear G y x = 1 := by
              rw [matrixBilinear_symmetric hsymm y x, hxy]
            simpa [splitPairColumn, splitPairTargetMatrix] using hyx
          · simpa [splitPairColumn, splitPairTargetMatrix, quad] using hyy
      | inr b =>
          fin_cases a
          · simpa [splitPairColumn, splitPairTargetMatrix] using
              projection_pair_left (matrixBilinear G) (matrixBilinear_symmetric hsymm) x y
                (basisVec n b.1) ⟨hxx, hxy, hyy⟩
          · simpa [splitPairColumn, splitPairTargetMatrix] using
              projection_pair_right (matrixBilinear G) (matrixBilinear_symmetric hsymm) x y
                (basisVec n b.1) ⟨hxx, hxy, hyy⟩
  | inr a =>
      cases b with
      | inl b =>
          fin_cases b
          · have h := projection_pair_left (matrixBilinear G) (matrixBilinear_symmetric hsymm) x y
                (basisVec n a.1) ⟨hxx, hxy, hyy⟩
            rw [matrixBilinear_symmetric hsymm]
            simpa [splitPairColumn, splitPairTargetMatrix] using h
          · have h := projection_pair_right (matrixBilinear G) (matrixBilinear_symmetric hsymm) x y
                (basisVec n a.1) ⟨hxx, hxy, hyy⟩
            rw [matrixBilinear_symmetric hsymm]
            simpa [splitPairColumn, splitPairTargetMatrix] using h
      | inr b =>
          rfl

/-- Reindexing the source form to the split-coordinate type turns the split-pair
change matrix congruence into a square congruence. -/
theorem splitPairSquareChangeMatrix_congruence {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n} (hrj : r ≠ j)
    (hsymm : G.IsSymm) (hp : HyperbolicPair (matrixBilinear G) x y) :
    (splitPairSquareChangeMatrix G x y hrj).transpose *
        (G.submatrix (splitPairIndexEquiv hrj) (splitPairIndexEquiv hrj)) *
        splitPairSquareChangeMatrix G x y hrj =
      splitPairTargetMatrix G x y r j := by
  ext a b
  let e := splitPairIndexEquiv hrj
  let C := splitPairChangeMatrix G x y r j
  have hnew :
      ((splitPairSquareChangeMatrix G x y hrj).transpose *
          (G.submatrix e e) * splitPairSquareChangeMatrix G x y hrj) a b =
        ∑ i : Fin 2 ⊕ RemainingIndex n r j,
          (∑ k : Fin 2 ⊕ RemainingIndex n r j, C (e k) a * G (e k) (e i)) * C (e i) b := by
    simp only [splitPairSquareChangeMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.submatrix_apply, id_eq, C, e]
  have hsum_inner (i : Fin 2 ⊕ RemainingIndex n r j) :
      (∑ k : Fin 2 ⊕ RemainingIndex n r j, C (e k) a * G (e k) (e i)) =
        ∑ k : Fin n, C k a * G k (e i) :=
    e.sum_comp (fun k : Fin n => C k a * G k (e i))
  have hsum_outer :
      (∑ i : Fin 2 ⊕ RemainingIndex n r j, (∑ k : Fin n, C k a * G k (e i)) * C (e i) b) =
        ∑ i : Fin n, (∑ k : Fin n, C k a * G k i) * C i b :=
    e.sum_comp (fun i : Fin n => (∑ k : Fin n, C k a * G k i) * C i b)
  have hold :
      ((C.transpose * G * C) a b) =
        ∑ i : Fin n, (∑ k : Fin n, C k a * G k i) * C i b := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hentry :
      ((splitPairSquareChangeMatrix G x y hrj).transpose *
          (G.submatrix e e) * splitPairSquareChangeMatrix G x y hrj) a b =
        ((C.transpose * G * C) a b) := by
    rw [hnew]
    calc
      (∑ i : Fin 2 ⊕ RemainingIndex n r j,
          (∑ k : Fin 2 ⊕ RemainingIndex n r j, C (e k) a * G (e k) (e i)) * C (e i) b) =
          ∑ i : Fin 2 ⊕ RemainingIndex n r j, (∑ k : Fin n, C k a * G k (e i)) * C (e i) b := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hsum_inner i]
      _ = ∑ i : Fin n, (∑ k : Fin n, C k a * G k i) * C i b := hsum_outer
      _ = ((C.transpose * G * C) a b) := hold.symm
  rw [hentry]
  exact congrArg (fun M => M a b) (splitPairChangeMatrix_congruence hsymm hp)

/-- The residual block has the expected Schur-complement entries. -/
theorem splitPairTargetMatrix_residual_apply {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n}
    (hsymm : G.IsSymm) (hp : HyperbolicPair (matrixBilinear G) x y)
    (l m : RemainingIndex n r j) :
    splitPairTargetMatrix G x y r j (Sum.inr l) (Sum.inr m) =
      G l.1 m.1 - matrixBilinear G (basisVec n l.1) x * matrixBilinear G (basisVec n m.1) y -
        matrixBilinear G (basisVec n l.1) y * matrixBilinear G (basisVec n m.1) x := by
  calc
    splitPairTargetMatrix G x y r j (Sum.inr l) (Sum.inr m) =
        matrixBilinear G
          (perpendicularProjection (matrixBilinear G) x y (basisVec n l.1))
          (perpendicularProjection (matrixBilinear G) x y (basisVec n m.1)) := rfl
    _ = matrixBilinear G (basisVec n l.1) (basisVec n m.1) -
          matrixBilinear G (basisVec n l.1) x * matrixBilinear G (basisVec n m.1) y -
          matrixBilinear G (basisVec n l.1) y * matrixBilinear G (basisVec n m.1) x :=
        projection_pairing (matrixBilinear G) (matrixBilinear_symmetric hsymm) x y
          (basisVec n l.1) (basisVec n m.1) hp
    _ = G l.1 m.1 - matrixBilinear G (basisVec n l.1) x * matrixBilinear G (basisVec n m.1) y -
          matrixBilinear G (basisVec n l.1) y * matrixBilinear G (basisVec n m.1) x := by
        rw [matrixBilinear_basis_basis]

/-- The projected residual block keeps even diagonal entries. -/
theorem splitPairTargetMatrix_residual_diag_even {n : ℕ}
    {G : Matrix (Fin n) (Fin n) R} {x y : Fin n → R} {r j : Fin n}
    (hsymm : G.IsSymm) (hdiag : ∀ i, Even8 (G i i))
    (hp : HyperbolicPair (matrixBilinear G) x y)
    (l : RemainingIndex n r j) :
    Even8 (splitPairTargetMatrix G x y r j (Sum.inr l) (Sum.inr l)) := by
  rcases hdiag l.1 with ⟨a, ha⟩
  refine ⟨a - matrixBilinear G (basisVec n l.1) x * matrixBilinear G (basisVec n l.1) y, ?_⟩
  rw [splitPairTargetMatrix_residual_apply hsymm hp l l, ha]
  ring

/-- Even diagonal entries give even norms for the standard coordinate vectors. -/
theorem matrixBilinear_quad_basis_even {n : ℕ} {G : Matrix (Fin n) (Fin n) R}
    (hdiag : ∀ i, Even8 (G i i)) (i : Fin n) :
    Even8 (quad (matrixBilinear G) (basisVec n i)) := by
  simpa [matrixBilinear_quad_basis] using hdiag i

end MatrixAdapter

#assert_standard_axioms even_not_four
#assert_standard_axioms seven_even_values
#assert_standard_axioms ternary_binary_zero
#assert_standard_axioms one_bit_correction
#assert_standard_axioms red8to2
#assert_standard_axioms even8_iff_red8to2_eq_zero
#assert_standard_axioms zmod2_dot_mulVec_zero_of_isSymm_zero_diag
#assert_standard_axioms exists_partner_away_from_pivot
#assert_standard_axioms quad_three
#assert_standard_axioms seven_vector_test
#assert_standard_axioms quad_add_smul
#assert_standard_axioms explicit_partner
#assert_standard_axioms lift_to_hyperbolic_pair
#assert_standard_axioms projection_pair_left
#assert_standard_axioms projection_pair_right
#assert_standard_axioms projection_pairing
#assert_standard_axioms projection_coordinate
#assert_standard_axioms primitiveColumnShear

#assert_standard_axioms matrixBilinear
#assert_standard_axioms matrix_vecMul_eq_mulVec_of_isSymm
#assert_standard_axioms matrixBilinear_symmetric
#assert_standard_axioms basisVec
#assert_standard_axioms matrixBilinear_basis_basis
#assert_standard_axioms matrixBilinear_basis_left
#assert_standard_axioms matrixBilinear_basis_right
#assert_standard_axioms matrixBilinear_basis_right_of_isSymm
#assert_standard_axioms red8to2_matrixBilinear_quad
#assert_standard_axioms matrixBilinear_quad_even_of_isSymm_even_diag
#assert_standard_axioms matrixBilinear_seven_vector_test
#assert_standard_axioms matrixBilinear_seven_coordinate_test
#assert_standard_axioms exists_matrix_partner_away_from_pivot_of_left_inverse
#assert_standard_axioms exists_matrix_partner_away_from_pivot_mod8
#assert_standard_axioms mod2_left_inverse_transpose_of_isSymm_right_inverse
#assert_standard_axioms exists_matrix_partner_away_from_pivot_of_right_inverse_mod8
#assert_standard_axioms sq_eq_one_of_red8to2_eq_one
#assert_standard_axioms exists_basis_partner_sq_eq_one_of_right_inverse_mod8
#assert_standard_axioms exists_hyperbolic_pair_from_four8_vector_of_right_inverse_mod8
#assert_standard_axioms red8to2_basisVec_self
#assert_standard_axioms red8to2_basisVec_add_left
#assert_standard_axioms red8to2_basisVec_add_add_left
#assert_standard_axioms exists_hyperbolic_pair_from_three_coordinates_of_right_inverse_mod8
#assert_standard_axioms RemainingIndex
#assert_standard_axioms splitPairIndexEquiv
#assert_standard_axioms splitPairIndexEquiv_inl_zero
#assert_standard_axioms splitPairIndexEquiv_inl_one
#assert_standard_axioms splitPairIndexEquiv_inr
#assert_standard_axioms exists_split_pair_from_three_coordinates_of_right_inverse_mod8
#assert_standard_axioms splitPairColumn
#assert_standard_axioms splitPairChangeMatrix
#assert_standard_axioms splitPairTargetMatrix
#assert_standard_axioms vecMul_dotProduct_eq_matrixBilinear
#assert_standard_axioms residualCoordinateFunctional
#assert_standard_axioms residualRow_dotProduct
#assert_standard_axioms splitPairInverseMatrix
#assert_standard_axioms splitPairInverseMatrix_mul_change
#assert_standard_axioms splitPairSquareChangeMatrix
#assert_standard_axioms splitPairSquareInverseMatrix
#assert_standard_axioms splitPairSquareInverseMatrix_mul_change
#assert_standard_axioms splitPairSquareChangeMatrix_mul_inverse
#assert_standard_axioms splitPairTargetMatrix_isSymm
#assert_standard_axioms splitPairChangeMatrix_contraction
#assert_standard_axioms splitPairChangeMatrix_congruence
#assert_standard_axioms splitPairSquareChangeMatrix_congruence
#assert_standard_axioms splitPairTargetMatrix_residual_apply
#assert_standard_axioms splitPairTargetMatrix_residual_diag_even
#assert_standard_axioms matrixBilinear_quad_basis_even

end TypeIIDirectPeeling

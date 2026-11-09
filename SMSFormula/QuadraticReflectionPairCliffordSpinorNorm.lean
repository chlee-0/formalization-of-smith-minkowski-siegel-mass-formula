import SMSFormula.QuadraticReflectionWordSpinorNormPrecursor
import SMSFormula.RationalCliffordReflectionPairNormalization
import SMSFormula.ExteriorAlgebraJointContractionKernel

/-!
# Clifford proof of reflection-pair spinor-norm independence

For a list of consecutive anisotropic reflection pairs, this file constructs
the corresponding unit in the Clifford algebra.  The factor for the pair
`(v, w)` is `ι(w) * ι(v)`, and list factors are multiplied in reverse list
order; these conventions make Clifford conjugation agree literally with the
existing left-to-right reflection-word evaluator.

The product with its Clifford reverse is the scalar product of all paired
quadratic values.  If two pair words evaluate to the same isometry, the ratio
of their Clifford units is even and commutes with every vector.  The joint
contraction theorem therefore makes that ratio scalar.  Comparing reverse
norms shows that the two quadratic-value products differ by a square, proving
`ReflectionPairSpinorNormFactorizationIndependent` without a source theorem.

No Spin-image kernel, local continuity, local measure, or Tamagawa statement
is made here.
-/

open CliffordAlgebra

noncomputable section

namespace QuadraticMap.ReflectionWord

variable {K M : Type*} [Field K] [CharZero K]
variable [AddCommGroup M] [Module K M] [FiniteDimensional K M]
variable (Q : QuadraticForm K M)

noncomputable def anisotropicCliffordUnit (x : Q.AnisotropicVector) :
    (CliffordAlgebra Q)ˣ :=
  (CliffordAlgebra.isUnit_ι_of_isUnit Q
    (isUnit_iff_ne_zero.mpr x.property)).unit

omit [CharZero K] [FiniteDimensional K M] in
@[simp]
theorem coe_anisotropicCliffordUnit (x : Q.AnisotropicVector) :
    (anisotropicCliffordUnit Q x : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q x := by
  exact (CliffordAlgebra.isUnit_ι_of_isUnit Q
    (isUnit_iff_ne_zero.mpr x.property)).unit_spec

noncomputable def reflectionPairCliffordUnit (p : ReflectionPair Q) :
    (CliffordAlgebra Q)ˣ :=
  anisotropicCliffordUnit Q p.2 * anisotropicCliffordUnit Q p.1

omit [CharZero K] [FiniteDimensional K M] in
@[simp]
theorem coe_reflectionPairCliffordUnit (p : ReflectionPair Q) :
    (reflectionPairCliffordUnit Q p : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q p.2 * CliffordAlgebra.ι Q p.1 := by
  simp [reflectionPairCliffordUnit]

noncomputable def reflectionPairsCliffordUnit :
    List (ReflectionPair Q) → (CliffordAlgebra Q)ˣ
  | [] => 1
  | p :: ps => reflectionPairsCliffordUnit ps * reflectionPairCliffordUnit Q p

omit [CharZero K] [FiniteDimensional K M] in
@[simp]
theorem reflectionPairsCliffordUnit_nil :
    reflectionPairsCliffordUnit Q [] = 1 := rfl

omit [CharZero K] [FiniteDimensional K M] in
@[simp]
theorem reflectionPairsCliffordUnit_cons (p : ReflectionPair Q)
    (ps : List (ReflectionPair Q)) :
    reflectionPairsCliffordUnit Q (p :: ps) =
      reflectionPairsCliffordUnit Q ps * reflectionPairCliffordUnit Q p := rfl

def reflectionPairQuadraticUnit (p : ReflectionPair Q) : Kˣ :=
  Units.mk0 (Q p.1) p.1.property * Units.mk0 (Q p.2) p.2.property

def reflectionPairsQuadraticUnit (ps : List (ReflectionPair Q)) : Kˣ :=
  (ps.map (reflectionPairQuadraticUnit Q)).prod

omit [CharZero K] [FiniteDimensional K M] in
@[simp]
theorem reflectionPairsQuadraticUnit_nil :
    reflectionPairsQuadraticUnit Q [] = 1 := rfl

omit [CharZero K] [FiniteDimensional K M] in
@[simp]
theorem reflectionPairsQuadraticUnit_cons (p : ReflectionPair Q)
    (ps : List (ReflectionPair Q)) :
    reflectionPairsQuadraticUnit Q (p :: ps) =
      reflectionPairQuadraticUnit Q p * reflectionPairsQuadraticUnit Q ps := rfl

omit [CharZero K] [FiniteDimensional K M] in
theorem reflectionPairsCliffordUnit_mem_even
    (ps : List (ReflectionPair Q)) :
    (reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q 0 := by
  induction ps with
  | nil => exact Submodule.one_le.mp (CliffordAlgebra.one_le_evenOdd_zero Q)
  | cons p ps ih =>
      change (reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) *
          (CliffordAlgebra.ι Q p.2 * CliffordAlgebra.ι Q p.1) ∈ _
      simpa using SetLike.GradedMul.mul_mem ih
        (CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q p.2 p.1)

omit [CharZero K] [FiniteDimensional K M] in
theorem reflectionPairsCliffordUnit_mul_reverse
    (ps : List (ReflectionPair Q)) :
    (reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) *
        CliffordAlgebra.reverse
          (reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) =
      algebraMap K (CliffordAlgebra Q)
        (reflectionPairsQuadraticUnit Q ps : K) := by
  induction ps with
  | nil =>
      change (1 : CliffordAlgebra Q) * CliffordAlgebra.reverse 1 =
        algebraMap K (CliffordAlgebra Q) (1 : K)
      simp
  | cons p ps ih =>
      change
        ((reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) *
          (CliffordAlgebra.ι Q p.2 * CliffordAlgebra.ι Q p.1)) *
          CliffordAlgebra.reverse
            ((reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) *
              (CliffordAlgebra.ι Q p.2 * CliffordAlgebra.ι Q p.1)) = _
      rw [CliffordAlgebra.reverse.map_mul]
      rw [show CliffordAlgebra.reverse
          (CliffordAlgebra.ι Q p.2 * CliffordAlgebra.ι Q p.1) =
          CliffordAlgebra.ι Q p.1 * CliffordAlgebra.ι Q p.2 by simp]
      rw [show
          ((reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) *
              (CliffordAlgebra.ι Q p.2 * CliffordAlgebra.ι Q p.1)) *
            ((CliffordAlgebra.ι Q p.1 * CliffordAlgebra.ι Q p.2) *
              CliffordAlgebra.reverse
                (reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q)) =
          (reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) *
            ((CliffordAlgebra.ι Q p.2 * CliffordAlgebra.ι Q p.1) *
              (CliffordAlgebra.ι Q p.1 * CliffordAlgebra.ι Q p.2)) *
            CliffordAlgebra.reverse
              (reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) by
            noncomm_ring]
      rw [show (CliffordAlgebra.ι Q p.2 * CliffordAlgebra.ι Q p.1) *
              (CliffordAlgebra.ι Q p.1 * CliffordAlgebra.ι Q p.2) =
            algebraMap K (CliffordAlgebra Q) (Q p.1 * Q p.2) by
        simpa [CliffordAlgebra.normalizedReflectionPair, mul_comm] using
          (CliffordAlgebra.normalizedReflectionPair_mul_reverse
            Q (1 : K) (p.2 : M) (p.1 : M))]
      rw [← Algebra.commutes (Q p.1 * Q p.2)
        (reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q),
        mul_assoc, ih, ← map_mul]
      congr 1

omit [CharZero K] [FiniteDimensional K M] in
theorem coe_reflectionPairsCliffordUnit_inv
    (ps : List (ReflectionPair Q)) :
    (↑((reflectionPairsCliffordUnit Q ps)⁻¹) : CliffordAlgebra Q) =
      algebraMap K (CliffordAlgebra Q)
          ((reflectionPairsQuadraticUnit Q ps)⁻¹ : K) *
        CliffordAlgebra.reverse
          (reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) := by
  let u := reflectionPairsCliffordUnit Q ps
  let a : K := ((reflectionPairsQuadraticUnit Q ps)⁻¹ : K)
  let z := algebraMap K (CliffordAlgebra Q) a *
    CliffordAlgebra.reverse (u : CliffordAlgebra Q)
  have hau : a * (reflectionPairsQuadraticUnit Q ps : K) = 1 := by
    dsimp only [a]
    exact inv_mul_cancel₀ (reflectionPairsQuadraticUnit Q ps).ne_zero
  have huz : (u : CliffordAlgebra Q) * z = 1 := by
    change (u : CliffordAlgebra Q) *
      (algebraMap K (CliffordAlgebra Q) a *
        CliffordAlgebra.reverse (u : CliffordAlgebra Q)) = 1
    rw [← mul_assoc,
      ← Algebra.commutes a (u : CliffordAlgebra Q), mul_assoc,
      reflectionPairsCliffordUnit_mul_reverse, ← map_mul, hau, map_one]
  calc
    (↑(u⁻¹) : CliffordAlgebra Q) =
        (↑(u⁻¹) : CliffordAlgebra Q) * 1 := by simp
    _ = (↑(u⁻¹) : CliffordAlgebra Q) *
        ((u : CliffordAlgebra Q) * z) := by rw [huz]
    _ = z := by rw [← mul_assoc, u.inv_mul, one_mul]

omit [CharZero K] [FiniteDimensional K M] in
theorem reflectionPairsCliffordUnit_inv_mem_even
    (ps : List (ReflectionPair Q)) :
    (↑((reflectionPairsCliffordUnit Q ps)⁻¹) : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q 0 := by
  rw [coe_reflectionPairsCliffordUnit_inv]
  have hscalar :
      algebraMap K (CliffordAlgebra Q)
          ((reflectionPairsQuadraticUnit Q ps)⁻¹ : K) ∈
        CliffordAlgebra.evenOdd Q 0 := by
    apply CliffordAlgebra.one_le_evenOdd_zero Q
    exact Submodule.mem_one.mpr ⟨_, rfl⟩
  have hreverse :
      CliffordAlgebra.reverse
          (reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) ∈
        CliffordAlgebra.evenOdd Q 0 :=
    (CliffordAlgebra.reverse_mem_evenOdd_iff Q).mpr
      (reflectionPairsCliffordUnit_mem_even Q ps)
  simpa using SetLike.GradedMul.mul_mem hscalar hreverse

omit [CharZero K] [FiniteDimensional K M] in
theorem reflectionPairsQuadraticUnit_squareClass
    (ps : List (ReflectionPair Q)) :
    ((reflectionPairsQuadraticUnit Q ps : Kˣ) : Rat.SquareClass K) =
      reflectionPairSquareClassProduct Q ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [reflectionPairsQuadraticUnit_cons,
        reflectionPairSquareClassProduct_cons, reflectionPairQuadraticUnit,
        reflectionPairSquareClass, quadraticValueSquareClass]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      rw [ih]

theorem exists_eq_algebraMap_of_mem_even_of_commute_ι_all
    (x : CliffordAlgebra Q) (hx : x ∈ CliffordAlgebra.evenOdd Q 0)
    (hQ : Q.associated.Nondegenerate)
    (hcomm : ∀ v : M, CliffordAlgebra.ι Q v * x =
      x * CliffordAlgebra.ι Q v) :
    ∃ r : K, x = algebraMap K (CliffordAlgebra Q) r := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have hcontract :=
    (CliffordAlgebra.commute_ι_all_iff_contractLeft_all_eq_zero_of_mem_even
      Q x hx hQ).mp hcomm
  have hcontractExterior (d : Module.Dual K M) :
      CliffordAlgebra.contractLeft d
        (CliffordAlgebra.equivExterior Q x) = 0 := by
    rw [← CliffordAlgebra.equivExterior_contractLeft, hcontract d, map_zero]
  obtain ⟨r, hr⟩ :=
    ExteriorAlgebra.exists_eq_algebraMap_of_contractLeft_eq_zero
      (Module.finBasis K M) (CliffordAlgebra.equivExterior Q x)
        hcontractExterior
  refine ⟨r, ?_⟩
  apply (CliffordAlgebra.equivExterior Q).injective
  rw [hr]
  simp

omit [CharZero K] [FiniteDimensional K M] in
theorem coe_anisotropicCliffordUnit_inv (x : Q.AnisotropicVector) :
    (↑((anisotropicCliffordUnit Q x)⁻¹) : CliffordAlgebra Q) =
      algebraMap K (CliffordAlgebra Q) (Q x)⁻¹ *
        CliffordAlgebra.ι Q x := by
  let u := anisotropicCliffordUnit Q x
  let z := algebraMap K (CliffordAlgebra Q) (Q x)⁻¹ *
    CliffordAlgebra.ι Q x
  have huz : (u : CliffordAlgebra Q) * z = 1 := by
    change CliffordAlgebra.ι Q x *
      (algebraMap K (CliffordAlgebra Q) (Q x)⁻¹ *
        CliffordAlgebra.ι Q x) = 1
    rw [← mul_assoc,
      ← Algebra.commutes (Q x)⁻¹ (CliffordAlgebra.ι Q x),
      mul_assoc, CliffordAlgebra.ι_sq_scalar, ← map_mul,
      inv_mul_cancel₀ x.property, map_one]
  calc
    (↑(u⁻¹) : CliffordAlgebra Q) =
        (↑(u⁻¹) : CliffordAlgebra Q) * 1 := by simp
    _ = (↑(u⁻¹) : CliffordAlgebra Q) *
        ((u : CliffordAlgebra Q) * z) := by
      rw [huz]
    _ = z := by rw [← mul_assoc, u.inv_mul, one_mul]

omit [CharZero K] [FiniteDimensional K M] in
theorem anisotropicCliffordUnit_conjugation
    (x : Q.AnisotropicVector) (m : M) :
    (anisotropicCliffordUnit Q x : CliffordAlgebra Q) *
        CliffordAlgebra.ι Q m *
          (↑((anisotropicCliffordUnit Q x)⁻¹) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q
        (-(CliffordAlgebra.quadraticReflectionOfNeZero
          Q x x.property m)) := by
  rw [coe_anisotropicCliffordUnit,
    coe_anisotropicCliffordUnit_inv]
  rw [show CliffordAlgebra.ι Q x * CliffordAlgebra.ι Q m *
        (algebraMap K (CliffordAlgebra Q) (Q x)⁻¹ *
          CliffordAlgebra.ι Q x) =
      algebraMap K (CliffordAlgebra Q) (Q x)⁻¹ *
        (CliffordAlgebra.ι Q x * CliffordAlgebra.ι Q m *
          CliffordAlgebra.ι Q x) by
      rw [← mul_assoc,
        ← Algebra.commutes (Q x)⁻¹
          (CliffordAlgebra.ι Q x * CliffordAlgebra.ι Q m)];
      noncomm_ring]
  rw [CliffordAlgebra.ι_mul_ι_mul_ι,
    ← Algebra.smul_def, ← map_smul]
  rw [CliffordAlgebra.quadraticReflectionOfNeZero_apply]
  congr 1
  have hx : (Q x)⁻¹ * Q x = 1 := inv_mul_cancel₀ x.property
  rw [smul_sub, smul_smul, smul_smul, hx, one_smul]
  module

omit [CharZero K] [FiniteDimensional K M] in
theorem reflectionPairCliffordUnit_conjugation
    (p : ReflectionPair Q) (m : M) :
    (reflectionPairCliffordUnit Q p : CliffordAlgebra Q) *
        CliffordAlgebra.ι Q m *
          (↑((reflectionPairCliffordUnit Q p)⁻¹) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q (eval Q [p.1, p.2] m) := by
  change
    ((anisotropicCliffordUnit Q p.2 : CliffordAlgebra Q) *
      (anisotropicCliffordUnit Q p.1 : CliffordAlgebra Q)) *
      CliffordAlgebra.ι Q m *
      (((anisotropicCliffordUnit Q p.2 *
        anisotropicCliffordUnit Q p.1)⁻¹ :
          (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = _
  change
    ((anisotropicCliffordUnit Q p.2 : CliffordAlgebra Q) *
      (anisotropicCliffordUnit Q p.1 : CliffordAlgebra Q)) *
      CliffordAlgebra.ι Q m *
      ((↑((anisotropicCliffordUnit Q p.1)⁻¹) : CliffordAlgebra Q) *
        (↑((anisotropicCliffordUnit Q p.2)⁻¹) : CliffordAlgebra Q)) = _
  rw [show
      ((anisotropicCliffordUnit Q p.2 : CliffordAlgebra Q) *
        (anisotropicCliffordUnit Q p.1 : CliffordAlgebra Q)) *
        CliffordAlgebra.ι Q m *
        ((↑((anisotropicCliffordUnit Q p.1)⁻¹) : CliffordAlgebra Q) *
          (↑((anisotropicCliffordUnit Q p.2)⁻¹) : CliffordAlgebra Q)) =
      (anisotropicCliffordUnit Q p.2 : CliffordAlgebra Q) *
        ((anisotropicCliffordUnit Q p.1 : CliffordAlgebra Q) *
          CliffordAlgebra.ι Q m *
          (↑((anisotropicCliffordUnit Q p.1)⁻¹) : CliffordAlgebra Q)) *
        (↑((anisotropicCliffordUnit Q p.2)⁻¹) : CliffordAlgebra Q) by
      noncomm_ring]
  rw [anisotropicCliffordUnit_conjugation,
    anisotropicCliffordUnit_conjugation]
  simp only [map_neg, neg_neg]
  rfl

omit [CharZero K] [FiniteDimensional K M] in
theorem reflectionPairsCliffordUnit_conjugation
    (ps : List (ReflectionPair Q)) (m : M) :
    (reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) *
        CliffordAlgebra.ι Q m *
          (↑((reflectionPairsCliffordUnit Q ps)⁻¹) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q (eval Q (flattenPairs Q ps) m) := by
  induction ps generalizing m with
  | nil =>
      change (1 : CliffordAlgebra Q) * CliffordAlgebra.ι Q m * 1 =
        CliffordAlgebra.ι Q m
      simp
  | cons p ps ih =>
      change
        ((reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) *
          (reflectionPairCliffordUnit Q p : CliffordAlgebra Q)) *
          CliffordAlgebra.ι Q m *
          ((↑((reflectionPairCliffordUnit Q p)⁻¹) : CliffordAlgebra Q) *
            (↑((reflectionPairsCliffordUnit Q ps)⁻¹) :
              CliffordAlgebra Q)) = _
      rw [show
          ((reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) *
            (reflectionPairCliffordUnit Q p : CliffordAlgebra Q)) *
            CliffordAlgebra.ι Q m *
            ((↑((reflectionPairCliffordUnit Q p)⁻¹) : CliffordAlgebra Q) *
              (↑((reflectionPairsCliffordUnit Q ps)⁻¹ :
                (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
          (reflectionPairsCliffordUnit Q ps : CliffordAlgebra Q) *
            ((reflectionPairCliffordUnit Q p : CliffordAlgebra Q) *
              CliffordAlgebra.ι Q m *
              (↑((reflectionPairCliffordUnit Q p)⁻¹) :
                CliffordAlgebra Q)) *
            (↑((reflectionPairsCliffordUnit Q ps)⁻¹) :
              CliffordAlgebra Q) by noncomm_ring]
      rw [reflectionPairCliffordUnit_conjugation, ih]
      rfl

theorem exists_scalar_ratio_of_reflectionPairs_eval_eq
    (hQ : Q.associated.Nondegenerate)
    (ps qs : List (ReflectionPair Q))
    (heval : eval Q (flattenPairs Q ps) =
      eval Q (flattenPairs Q qs)) :
    ∃ r : K,
      (↑((reflectionPairsCliffordUnit Q qs)⁻¹ *
          reflectionPairsCliffordUnit Q ps) : CliffordAlgebra Q) =
        algebraMap K (CliffordAlgebra Q) r := by
  let up := reflectionPairsCliffordUnit Q ps
  let uq := reflectionPairsCliffordUnit Q qs
  have hp (m : M) :
      (up : CliffordAlgebra Q) * CliffordAlgebra.ι Q m =
        CliffordAlgebra.ι Q (eval Q (flattenPairs Q ps) m) *
          (up : CliffordAlgebra Q) := by
    calc
      (up : CliffordAlgebra Q) * CliffordAlgebra.ι Q m =
          (((up : CliffordAlgebra Q) * CliffordAlgebra.ι Q m) *
            (↑(up⁻¹) : CliffordAlgebra Q)) *
              (up : CliffordAlgebra Q) := by
        rw [mul_assoc, up.inv_mul, mul_one]
      _ = _ := by rw [reflectionPairsCliffordUnit_conjugation]
  have hqinv (m : M) :
      CliffordAlgebra.ι Q m * (↑(uq⁻¹) : CliffordAlgebra Q) =
        (↑(uq⁻¹) : CliffordAlgebra Q) *
          CliffordAlgebra.ι Q (eval Q (flattenPairs Q qs) m) := by
    calc
      CliffordAlgebra.ι Q m * (↑(uq⁻¹) : CliffordAlgebra Q) =
          ((↑(uq⁻¹) : CliffordAlgebra Q) * (uq : CliffordAlgebra Q)) *
            (CliffordAlgebra.ι Q m *
              (↑(uq⁻¹) : CliffordAlgebra Q)) := by rw [uq.inv_mul, one_mul]
      _ = (↑(uq⁻¹) : CliffordAlgebra Q) *
          (((uq : CliffordAlgebra Q) * CliffordAlgebra.ι Q m) *
            (↑(uq⁻¹) : CliffordAlgebra Q)) := by noncomm_ring
      _ = _ := by rw [reflectionPairsCliffordUnit_conjugation]
  have hcomm (m : M) :
      CliffordAlgebra.ι Q m *
          (↑(uq⁻¹ * up) : CliffordAlgebra Q) =
        (↑(uq⁻¹ * up) : CliffordAlgebra Q) *
          CliffordAlgebra.ι Q m := by
    change CliffordAlgebra.ι Q m *
        ((↑(uq⁻¹) : CliffordAlgebra Q) * (up : CliffordAlgebra Q)) =
      ((↑(uq⁻¹) : CliffordAlgebra Q) * (up : CliffordAlgebra Q)) *
        CliffordAlgebra.ι Q m
    have heval_m : eval Q (flattenPairs Q ps) m =
        eval Q (flattenPairs Q qs) m :=
      congrArg (fun g : Q.IsometryEquiv Q => g m) heval
    rw [← mul_assoc, hqinv, ← heval_m, mul_assoc, ← hp]
    rw [mul_assoc]
  have heven :
      (↑(uq⁻¹ * up) : CliffordAlgebra Q) ∈
        CliffordAlgebra.evenOdd Q 0 := by
    change (↑(uq⁻¹) : CliffordAlgebra Q) *
        (up : CliffordAlgebra Q) ∈ _
    simpa using SetLike.GradedMul.mul_mem
      (reflectionPairsCliffordUnit_inv_mem_even Q qs)
      (reflectionPairsCliffordUnit_mem_even Q ps)
  exact exists_eq_algebraMap_of_mem_even_of_commute_ι_all
    Q _ heven hQ hcomm

theorem exists_reflectionPairsQuadraticUnit_eq_sq_mul_of_eval_eq
    (hQ : Q.associated.Nondegenerate)
    (ps qs : List (ReflectionPair Q))
    (heval : eval Q (flattenPairs Q ps) =
      eval Q (flattenPairs Q qs)) :
    ∃ r : K, (reflectionPairsQuadraticUnit Q ps : K) =
      r ^ 2 * (reflectionPairsQuadraticUnit Q qs : K) := by
  obtain ⟨r, hr⟩ :=
    exists_scalar_ratio_of_reflectionPairs_eval_eq Q hQ ps qs heval
  let up := reflectionPairsCliffordUnit Q ps
  let uq := reflectionPairsCliffordUnit Q qs
  have hup : (up : CliffordAlgebra Q) =
      (uq : CliffordAlgebra Q) * algebraMap K (CliffordAlgebra Q) r := by
    calc
      (up : CliffordAlgebra Q) =
          ((uq : CliffordAlgebra Q) * (↑(uq⁻¹) : CliffordAlgebra Q)) *
            (up : CliffordAlgebra Q) := by rw [uq.mul_inv, one_mul]
      _ = (uq : CliffordAlgebra Q) *
          (↑(uq⁻¹ * up) : CliffordAlgebra Q) := by noncomm_ring
      _ = _ := by rw [hr]
  refine ⟨r, ?_⟩
  apply (algebraMap K (CliffordAlgebra Q)).injective
  calc
    algebraMap K (CliffordAlgebra Q)
          (reflectionPairsQuadraticUnit Q ps : K) =
        (up : CliffordAlgebra Q) *
          CliffordAlgebra.reverse (up : CliffordAlgebra Q) :=
      (reflectionPairsCliffordUnit_mul_reverse Q ps).symm
    _ = ((uq : CliffordAlgebra Q) *
          algebraMap K (CliffordAlgebra Q) r) *
        CliffordAlgebra.reverse
          ((uq : CliffordAlgebra Q) *
            algebraMap K (CliffordAlgebra Q) r) := by rw [hup]
    _ = algebraMap K (CliffordAlgebra Q) (r ^ 2) *
        ((uq : CliffordAlgebra Q) *
          CliffordAlgebra.reverse (uq : CliffordAlgebra Q)) := by
      rw [CliffordAlgebra.reverse.map_mul]
      simp only [CliffordAlgebra.reverse.commutes]
      rw [show
          ((uq : CliffordAlgebra Q) * algebraMap K (CliffordAlgebra Q) r) *
            (algebraMap K (CliffordAlgebra Q) r *
              CliffordAlgebra.reverse (uq : CliffordAlgebra Q)) =
          (algebraMap K (CliffordAlgebra Q) r *
            algebraMap K (CliffordAlgebra Q) r) *
              ((uq : CliffordAlgebra Q) *
                CliffordAlgebra.reverse (uq : CliffordAlgebra Q)) by
        let ar := algebraMap K (CliffordAlgebra Q) r
        change ((uq : CliffordAlgebra Q) * ar) *
            (ar * CliffordAlgebra.reverse (uq : CliffordAlgebra Q)) =
          (ar * ar) * ((uq : CliffordAlgebra Q) *
            CliffordAlgebra.reverse (uq : CliffordAlgebra Q))
        calc
          ((uq : CliffordAlgebra Q) * ar) *
                (ar * CliffordAlgebra.reverse (uq : CliffordAlgebra Q)) =
              (ar * (uq : CliffordAlgebra Q)) *
                (ar * CliffordAlgebra.reverse (uq : CliffordAlgebra Q)) := by
            rw [← Algebra.commutes r]
          _ = ar * ((uq : CliffordAlgebra Q) * ar) *
                CliffordAlgebra.reverse (uq : CliffordAlgebra Q) := by
            noncomm_ring
          _ = ar * (ar * (uq : CliffordAlgebra Q)) *
                CliffordAlgebra.reverse (uq : CliffordAlgebra Q) := by
            rw [← Algebra.commutes r]
          _ = _ := by noncomm_ring]
      rw [← map_mul, ← pow_two]
    _ = algebraMap K (CliffordAlgebra Q)
        (r ^ 2 * (reflectionPairsQuadraticUnit Q qs : K)) := by
      rw [reflectionPairsCliffordUnit_mul_reverse, ← map_mul]

theorem reflectionPairSpinorNormFactorizationIndependent
    (hQ : Q.associated.Nondegenerate) :
    ReflectionPairSpinorNormFactorizationIndependent Q := by
  intro ps qs heval
  obtain ⟨r, hr⟩ :=
    exists_reflectionPairsQuadraticUnit_eq_sq_mul_of_eval_eq
      Q hQ ps qs heval
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz] at hr
    norm_num at hr
  let ur : Kˣ := Units.mk0 r hr0
  have hunit : reflectionPairsQuadraticUnit Q ps =
      ur ^ 2 * reflectionPairsQuadraticUnit Q qs := by
    apply Units.ext
    simpa [ur] using hr
  rw [← reflectionPairsQuadraticUnit_squareClass,
    ← reflectionPairsQuadraticUnit_squareClass, hunit,
    QuotientGroup.mk_mul]
  have hsquare : ((ur ^ 2 : Kˣ) : Rat.SquareClass K) = 1 := by
    apply (QuotientGroup.eq_one_iff (ur ^ 2)).mpr
    exact ⟨ur, pow_two ur⟩
  rw [hsquare, one_mul]

end QuadraticMap.ReflectionWord

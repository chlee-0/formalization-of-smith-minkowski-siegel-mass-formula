import SMSFormula.CliffordEvenCentralizer
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# The joint kernel of exterior contractions

For a finite free module over a commutative rational algebra, an exterior-
algebra element killed by contraction against every covector is a scalar.

The proof uses the Euler operator

`E(x) = ∑ i, ι(b i) * contractLeft (b.coord i) x`.

The contraction Leibniz rule shows that `E` acts by the scalar `k` on the
degree-`k` exterior power.  Since the exterior algebra is the direct sum of
its homogeneous pieces, it suffices to inspect each graded projection of
`E(x) = 0`. Every positive integer is a unit in a rational algebra, so every
positive-degree component vanishes and only degree zero remains.
-/

noncomputable section

open BigOperators

namespace ExteriorAlgebra

variable {K M ι : Type*} [CommRing K]
variable [AddCommGroup M] [Module K M]
variable [Fintype ι]

/-- The Euler operator on an exterior algebra, expressed in a finite basis. -/
def eulerOperator (b : Module.Basis ι K M) :
    ExteriorAlgebra K M →ₗ[K] ExteriorAlgebra K M :=
  ∑ i, (LinearMap.mulLeft K (ExteriorAlgebra.ι K (b i))).comp
    (CliffordAlgebra.contractLeft (b.coord i))

/-- The Euler operator gains one copy of a left exterior generator. -/
theorem eulerOperator_ι_mul (b : Module.Basis ι K M)
    (m : M) (x : ExteriorAlgebra K M) :
    eulerOperator b (ExteriorAlgebra.ι K m * x) =
      ExteriorAlgebra.ι K m * x +
        ExteriorAlgebra.ι K m * eulerOperator b x := by
  rw [eulerOperator]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply,
    CliffordAlgebra.contractLeft_ι_mul]
  have hterm (i : ι) :
      ExteriorAlgebra.ι K (b i) *
          (b.coord i m • x - ExteriorAlgebra.ι K m *
            CliffordAlgebra.contractLeft (b.coord i) x) =
        b.coord i m • (ExteriorAlgebra.ι K (b i) * x) +
          ExteriorAlgebra.ι K m *
            (ExteriorAlgebra.ι K (b i) *
              CliffordAlgebra.contractLeft (b.coord i) x) := by
    have hanti := ExteriorAlgebra.ι_add_mul_swap (R := K) (b i) m
    have hab :
        ExteriorAlgebra.ι K (b i) * ExteriorAlgebra.ι K m =
          -(ExteriorAlgebra.ι K m * ExteriorAlgebra.ι K (b i)) :=
      eq_neg_of_add_eq_zero_left hanti
    rw [mul_sub, mul_smul_comm, ← mul_assoc, hab]
    noncomm_ring
  change
    (∑ i, ExteriorAlgebra.ι K (b i) *
      (b.coord i m • x - ExteriorAlgebra.ι K m *
        CliffordAlgebra.contractLeft (b.coord i) x)) =
      ExteriorAlgebra.ι K m * x + ExteriorAlgebra.ι K m *
        ∑ i, ExteriorAlgebra.ι K (b i) *
          CliffordAlgebra.contractLeft (b.coord i) x
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp_rw [← smul_mul_assoc]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hbasis :
      ∑ i, b.coord i m • ExteriorAlgebra.ι K (b i) =
        ExteriorAlgebra.ι K m := by
    simp_rw [← map_smul]
    rw [← map_sum]
    exact congrArg (ExteriorAlgebra.ι K) (b.sum_repr m)
  rw [hbasis]

/-- On the `k`th homogeneous exterior power, the Euler operator is
multiplication by `k`. -/
theorem eulerOperator_eq_nat_smul_of_mem_exteriorPower
    (b : Module.Basis ι K M) (k : ℕ) (x : ExteriorAlgebra K M)
    (hx : x ∈ ⋀[K]^k M) :
    eulerOperator b x = (k : K) • x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [eulerOperator]
  | add x y k hx hy ihx ihy => rw [map_add, ihx, ihy, smul_add]
  | mem_mul m hm k x hx ih =>
      obtain ⟨m, rfl⟩ := hm
      rw [eulerOperator_ι_mul, ih]
      simp only [Nat.cast_succ, add_smul]
      rw [one_smul, mul_smul_comm]
      ac_rfl

/-- Projection to degree `k` intertwines the Euler operator with scalar
multiplication by `k`. -/
theorem proj_eulerOperator (b : Module.Basis ι K M) (k : ℕ) :
    (GradedAlgebra.proj (fun j : ℕ => ⋀[K]^j M) k).comp
        (eulerOperator b) =
      (k : K) • GradedAlgebra.proj (fun j : ℕ => ⋀[K]^j M) k := by
  apply DirectSum.decompose_lhom_ext (fun j : ℕ => ⋀[K]^j M)
  intro j
  ext y
  change GradedAlgebra.proj (fun j : ℕ => ⋀[K]^j M) k
      (eulerOperator b (y : ExteriorAlgebra K M)) =
    (k : K) • GradedAlgebra.proj (fun j : ℕ => ⋀[K]^j M) k
      (y : ExteriorAlgebra K M)
  rw [eulerOperator_eq_nat_smul_of_mem_exteriorPower b j y y.property,
    map_smul]
  by_cases hjk : j = k
  · subst j
    rfl
  · rw [GradedAlgebra.proj_apply,
      DirectSum.decompose_of_mem_ne (fun j : ℕ => ⋀[K]^j M) y.property hjk,
      smul_zero, smul_zero]

/-- The common kernel of all left contractions on a finite free exterior
algebra over a commutative rational algebra consists of scalars. -/
theorem exists_eq_algebraMap_of_contractLeft_eq_zero [Algebra ℚ K]
    (b : Module.Basis ι K M) (x : ExteriorAlgebra K M)
    (hx : ∀ d : Module.Dual K M, CliffordAlgebra.contractLeft d x = 0) :
    ∃ r : K, x = algebraMap K (ExteriorAlgebra K M) r := by
  let Agrade : ℕ → Submodule K (ExteriorAlgebra K M) := fun k => ⋀[K]^k M
  have hE : eulerOperator b x = 0 := by
    rw [eulerOperator]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, hx, map_zero,
      Finset.sum_const_zero]
  have hcomponent (k : ℕ) (hk : k ≠ 0) :
      GradedAlgebra.proj Agrade k x = 0 := by
    have happ := LinearMap.congr_fun (proj_eulerOperator b k) x
    change GradedAlgebra.proj Agrade k (eulerOperator b x) =
      (k : K) • GradedAlgebra.proj Agrade k x at happ
    rw [hE, map_zero] at happ
    have hk_unit : IsUnit (k : K) := by
      simpa using (Nat.cast_ne_zero.mpr hk : (k : ℚ) ≠ 0).isUnit.map
        (algebraMap ℚ K)
    exact hk_unit.smul_eq_zero.mp happ.symm
  let x₀ : ExteriorAlgebra K M := GradedAlgebra.proj Agrade 0 x
  have hx₀_mem : x₀ ∈ Agrade 0 := (DirectSum.decompose Agrade x 0).property
  have hxx₀ : x = x₀ := by
    apply (DirectSum.decompose Agrade).injective
    ext k
    change GradedAlgebra.proj Agrade k x =
      (DirectSum.decompose Agrade x₀ k : ExteriorAlgebra K M)
    by_cases hk : k = 0
    · subst k
      exact (DirectSum.decompose_of_mem_same Agrade hx₀_mem).symm
    · rw [hcomponent k hk,
        DirectSum.decompose_of_mem_ne Agrade hx₀_mem (fun h => hk h.symm)]
  change x₀ ∈ (1 : Submodule K (ExteriorAlgebra K M)) at hx₀_mem
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hx₀_mem
  exact ⟨r, hxx₀.trans hr.symm⟩

end ExteriorAlgebra

import SMSFormula.CliffordSpinAction
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Even Clifford centralizers and contractions

The kernel of the Spin conjugation representation consists of the Spin
elements commuting with every Clifford vector.  This file begins the
central-kernel calculation by converting that commutation
condition into a contraction condition.

For an arbitrary Clifford element `x`, the graded commutator with a vector is
twice contraction by the associated bilinear form:

```text
ι(v) * x - involute(x) * ι(v) = 2 • contractLeft (Q.associated v) x.
```

For an even element, `involute x = x`, so ordinary commutation with every
vector is equivalent to the vanishing of the corresponding contractions.  If
the associated bilinear form is nondegenerate in finite dimension, its map to
the dual is onto, and the condition is equivalent to vanishing under every
left contraction.

The remaining algebraic input for the Spin kernel is the statement that an
element of a finite-dimensional exterior algebra killed by every contraction
is scalar.  Through `CliffordAlgebra.equivExterior`, that statement identifies
the even vector centralizer with the scalar algebra map.
-/

noncomputable section

namespace CliffordAlgebra

variable {K M : Type*} [Field K]
variable [AddCommGroup M] [Module K M]
variable (Q : QuadraticForm K M) [Invertible (2 : K)]

/-- The graded commutator of a Clifford vector with an arbitrary element is
twice left contraction by the associated bilinear form. -/
theorem ι_mul_sub_involute_mul_ι_eq_two_smul_contractLeft
    (v : M) (x : CliffordAlgebra Q) :
    ι Q v * x - involute x * ι Q v =
      (2 : K) • contractLeft (Q.associated v) x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp [Algebra.commutes]
  | add x y hx hy =>
      rw [mul_add, map_add, add_mul, map_add, smul_add]
      calc
        ι Q v * x + ι Q v * y -
              (involute x * ι Q v + involute y * ι Q v) =
            (ι Q v * x - involute x * ι Q v) +
              (ι Q v * y - involute y * ι Q v) := by abel
        _ = (2 : K) • contractLeft (Q.associated v) x +
              (2 : K) • contractLeft (Q.associated v) y := by rw [hx, hy]
  | ι_mul a m hx =>
      rw [map_mul, involute_ι, neg_mul, neg_mul, sub_neg_eq_add]
      rw [contractLeft_ι_mul, smul_sub, smul_smul]
      have hpolar : QuadraticMap.polar Q v m =
          (2 : K) * Q.associated v m := by
        change Q (v + m) - Q v - Q m =
          (2 : K) * (⅟(2 : K) * (Q (v + m) - Q v - Q m))
        rw [← mul_assoc, mul_invOf_self, one_mul]
      have hcliff := ι_mul_ι_add_swap (Q := Q) v m
      rw [hpolar] at hcliff
      calc
        ι Q v * (ι Q m * a) +
              ι Q m * involute a * ι Q v =
            (ι Q v * ι Q m + ι Q m * ι Q v) * a +
              -(ι Q m *
                (ι Q v * a - involute a * ι Q v)) := by
                  noncomm_ring
        _ = algebraMap K (CliffordAlgebra Q)
              ((2 : K) * Q.associated v m) * a +
              -(ι Q m * ((2 : K) •
                contractLeft (Q.associated v) a)) := by rw [hcliff, hx]
        _ = (2 * Q.associated v m) • a -
              (2 : K) • (ι Q m *
                contractLeft (Q.associated v) a) := by
                  change algebraMap K (CliffordAlgebra Q)
                      (2 * Q.associated v m) * a +
                        -(ι Q m *
                          (algebraMap K (CliffordAlgebra Q) 2 *
                            contractLeft (Q.associated v) a)) =
                    algebraMap K (CliffordAlgebra Q)
                        (2 * Q.associated v m) * a -
                      algebraMap K (CliffordAlgebra Q) 2 *
                        (ι Q m * contractLeft (Q.associated v) a)
                  rw [← mul_assoc (ι Q m)
                    (algebraMap K (CliffordAlgebra Q) 2)
                    (contractLeft (Q.associated v) a),
                    ← Algebra.commutes (2 : K) (ι Q m)]
                  noncomm_ring

/-- For an even Clifford element, commutation with a vector is equivalent to
vanishing of contraction by the associated linear functional. -/
theorem commute_ι_iff_contractLeft_associated_eq_zero_of_mem_even
    (x : CliffordAlgebra Q) (hx : x ∈ even Q) (v : M) :
    ι Q v * x = x * ι Q v ↔
      contractLeft (Q.associated v) x = 0 := by
  have hinvolute : involute x = x := involute_eq_of_mem_even hx
  have hgraded := ι_mul_sub_involute_mul_ι_eq_two_smul_contractLeft Q v x
  rw [hinvolute] at hgraded
  constructor
  · intro hcomm
    have hzero : (2 : K) • contractLeft (Q.associated v) x = 0 := by
      rw [← hgraded, hcomm, sub_self]
    exact (smul_eq_zero.mp hzero).resolve_left two_ne_zero
  · intro hcontract
    apply sub_eq_zero.mp
    rw [hgraded, hcontract, smul_zero]

/-- For an even Clifford element and a nondegenerate associated form,
commutation with every vector is equivalent to vanishing under every left
contraction. -/
theorem commute_ι_all_iff_contractLeft_all_eq_zero_of_mem_even
    [FiniteDimensional K M]
    (x : CliffordAlgebra Q) (hx : x ∈ even Q)
    (hQ : Q.associated.Nondegenerate) :
    (∀ v : M, ι Q v * x = x * ι Q v) ↔
      ∀ d : Module.Dual K M, contractLeft d x = 0 := by
  constructor
  · intro hcomm d
    let v : M := (LinearMap.BilinForm.toDual Q.associated hQ).symm d
    have hv : Q.associated v = d := by
      apply LinearMap.ext
      intro w
      exact LinearMap.BilinForm.apply_toDual_symm_apply d w
    rw [← hv]
    exact (commute_ι_iff_contractLeft_associated_eq_zero_of_mem_even
      Q x hx v).mp (hcomm v)
  · intro hcontract v
    exact (commute_ι_iff_contractLeft_associated_eq_zero_of_mem_even
      Q x hx v).mpr (hcontract (Q.associated v))

/-- The module equivalence from a Clifford algebra to the exterior algebra
commutes with every left contraction. -/
theorem equivExterior_contractLeft
    (d : Module.Dual K M) (x : CliffordAlgebra Q) :
    equivExterior Q (contractLeft d x) =
      contractLeft d (equivExterior Q x) := by
  exact changeForm_contractLeft changeForm.associated_neg_proof d x

end CliffordAlgebra

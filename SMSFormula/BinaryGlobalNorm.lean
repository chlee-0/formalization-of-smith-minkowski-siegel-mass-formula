import SMSFormula.BinaryKernelNorm
import SMSFormula.RationalTernaryHasseMinkowski

/-!
# Global quadratic norms for binary kernel classes

The ternary Hasse--Minkowski theorem supplies a
rational point of the exact conic. It is applied to the same positive
rational leading coefficient already represented at every place. The
result lives in the canonical FractionRing, not in a replacement field.
-/

namespace BinaryNormIdeal

/-- The exact completed-square identity for the actual coefficient norm. -/
lemma four_norm_eq_trace_square {R : Type*} [CommRing R] (a b c : R)
    (z : CoefficientAlgebra a b c) :
    4*z.norm=(2*z.re+b*z.im)^2-(b^2-4*a*c)*z.im^2 := by
  rw [QuadraticAlgebra.norm_def]
  ring

/-- A nonzero rational locally represented by the actual quadratic norm is
an actual canonical fraction-field unit norm. Hasse--Minkowski is supplied
by the existing native proof, with no caller local-global certificate. -/
theorem exists_fractionNorm_unit_eq_of_real_and_padic
    (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]
    (hD : b^2-4*a*c<0) (q : ℚ) (hq : q ≠ 0)
    (hreal : ∃ z : CoefficientAlgebra (a : ℝ) (b : ℝ) (c : ℝ), z.norm=(q : ℝ))
    (hpadic : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      ∃ z : CoefficientAlgebra (a : ℚ_[p]) (b : ℚ_[p]) (c : ℚ_[p]), z.norm=(q : ℚ_[p])) :
    ∃ z : (FractionRing (CoefficientOrder a b c))ˣ, fractionNorm a b c hD z.val=q := by
  let d : ℚ := (b : ℚ)^2-4*(a : ℚ)*(c : ℚ)
  let A : Matrix (Fin 2) (Fin 2) ℚ := Matrix.diagonal ![1,-d]
  have hd : d ≠ 0 := ne_of_lt (by dsimp only [d]; exact_mod_cast hD)
  have hs : A.IsSymm := Matrix.isSymm_diagonal _
  have hdet : A.det ≠ 0 := by
    simpa [A,Matrix.det_fin_two] using neg_ne_zero.mpr hd
  have hvalue (R : Type) [Field R] [CharZero R]
      (z : CoefficientAlgebra (a : R) (b : R) (c : R)) :
      PositiveDefiniteIntegralLattice.gramQuadraticValue (A.map (algebraMap ℚ R))
        ![2*z.re+(b : R)*z.im,z.im]=4*z.norm := by
    rw [four_norm_eq_trace_square]
    simp [A,d,PositiveDefiniteIntegralLattice.gramQuadraticValue,Matrix.mulVec,dotProduct,
      Fin.sum_univ_two]
    ring
  have hR : ∃ v : Fin 2 → ℝ,
      PositiveDefiniteIntegralLattice.gramQuadraticValue (A.map (algebraMap ℚ ℝ)) v=((4*q : ℚ) : ℝ) := by
    obtain ⟨z,hz⟩ := hreal
    refine ⟨![2*z.re+(b : ℝ)*z.im,z.im],?_⟩
    rw [hvalue ℝ z,hz]
    push_cast
    rfl
  have hP : ∀ (p : ℕ) [Fact (Nat.Prime p)], ∃ v : Fin 2 → ℚ_[p],
      PositiveDefiniteIntegralLattice.gramQuadraticValue (A.map (algebraMap ℚ ℚ_[p])) v=((4*q : ℚ) : ℚ_[p]) := by
    intro p hp
    obtain ⟨z,hz⟩ := hpadic p
    refine ⟨![2*z.re+(b : ℚ_[p])*z.im,z.im],?_⟩
    rw [hvalue ℚ_[p] z,hz]
    push_cast
    rfl
  obtain ⟨v,hv⟩ := Rat.exists_binary_gramQuadraticValue_eq_rat_of_real_and_padic
    A hs hdet (4*q) (mul_ne_zero (by norm_num) hq) hR hP
  have hconic : ∃ s t : ℚ, s^2+(b : ℚ)*s*t+(a : ℚ)*(c : ℚ)*t^2=q := by
    refine ⟨(v 0-(b : ℚ)*v 1)/2,v 1,?_⟩
    simp [A,d,PositiveDefiniteIntegralLattice.gramQuadraticValue,Matrix.mulVec,dotProduct,Fin.sum_univ_two] at hv
    linear_combination (1/4 : ℚ)*hv
  obtain ⟨z,hz⟩ := (exists_fractionNorm_eq_iff_conic a b c hD q).mpr hconic
  have hn : z ≠ 0 := by
    intro hzero
    subst z
    change (fractionRationalMap a b c hD 0).norm=q at hz
    rw [map_zero,QuadraticAlgebra.norm_zero] at hz
    exact hq hz.symm
  exact ⟨Units.mk0 z hn,hz⟩

/-- Quadratic Hilbert90 over a scalar field with nonzero discriminant.
The quadratic algebra itself may split. The witness is an AMBIENT unit;
this theorem does not assert that it is integral in the local order. -/
theorem exists_unit_mul_star_of_norm_eq_one {R : Type*} [Field R] [CharZero R]
    (a b c : R) (hD : b^2-4*a*c ≠ 0)
    (x : CoefficientAlgebra a b c) (hx : x.norm=1) :
    ∃ y : (CoefficientAlgebra a b c)ˣ, y.val=x*star y.val := by
  by_cases hm : x=-1
  · subst x
    let j : CoefficientAlgebra a b c := ⟨-b,2⟩
    have hn : j.norm ≠ 0 := by
      have he : j.norm=-(b^2-4*a*c) := by
        simp [j,QuadraticAlgebra.norm_def]
        ring
      rw [he]
      exact neg_ne_zero.mpr hD
    obtain ⟨y,hy⟩ := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (isUnit_iff_ne_zero.mpr hn)
    refine ⟨y,?_⟩
    change y.val=(-1 : CoefficientAlgebra a b c)*star y.val
    rw [hy]
    apply QuadraticAlgebra.ext
    · simp [j]
      ring
    · simp [j]
  · have hn : (1+x).norm ≠ 0 := by
      intro hn
      have ht : 2*x.re+b*x.im = -2 := by
        rw [QuadraticAlgebra.norm_def] at hx hn
        simp only [QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
          QuadraticAlgebra.re_one,QuadraticAlgebra.im_one] at hn
        linear_combination hn-hx
      have hid := four_norm_eq_trace_square a b c x
      rw [hx,ht] at hid
      have hi : x.im=0 := by
        have hz : (b^2-4*a*c)*x.im^2=0 := by linear_combination hid
        exact mul_self_eq_zero.mp (by simpa only [pow_two] using (mul_eq_zero.mp hz).resolve_left hD)
      apply hm
      apply QuadraticAlgebra.ext
      · simp only [QuadraticAlgebra.re_neg,QuadraticAlgebra.re_one]
        rw [hi] at ht
        linear_combination (1/2 : R)*ht
      · simpa only [QuadraticAlgebra.im_neg,QuadraticAlgebra.im_one,neg_zero] using hi
    obtain ⟨y,hy⟩ := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (isUnit_iff_ne_zero.mpr hn)
    have hmul : x*star x=1 := by
      rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star,hx,map_one]
    refine ⟨y,?_⟩
    rw [hy,star_add,star_one,mul_add,mul_one,hmul]
    ring

/-- Equal nonzero norms differ by an actual Hilbert90 coboundary, also
in a split quadratic algebra. This is the local comparison used in patching. -/
theorem exists_unit_norm_comparison {R : Type*} [Field R] [CharZero R]
    (a b c : R) (hD : b^2-4*a*c ≠ 0)
    (z w : (CoefficientAlgebra a b c)ˣ) (hzw : z.val.norm=w.val.norm) :
    ∃ y : (CoefficientAlgebra a b c)ˣ, z.val*star y.val=w.val*y.val := by
  have hn : (w⁻¹).val.norm*w.val.norm=1 := by
    rw [← map_mul,← Units.val_mul,inv_mul_cancel,Units.val_one,map_one]
  have hx : (z*(w⁻¹)).val.norm=1 := by
    rw [Units.val_mul,map_mul,hzw,mul_comm]
    exact hn
  obtain ⟨y,hy⟩ := exists_unit_mul_star_of_norm_eq_one a b c hD (z*(w⁻¹)).val hx
  refine ⟨y,?_⟩
  have hh := congrArg (fun t => w.val*t) hy
  simp only [Units.val_mul] at hh
  calc
    z.val*star y.val = (w.val*(z.val*(w⁻¹).val))*star y.val := by
      congr 1
      rw [mul_comm z.val,← mul_assoc,← Units.val_mul,mul_inv_cancel,Units.val_one,one_mul]
    _ = w.val*y.val := by rw [mul_assoc,← hh]

/-- Compare an actual global norm witness with an actual local witness.
Only the scalar ring is a field. No integrality of the Hilbert90 factor is claimed. -/
theorem exists_unit_compare_fractionScalarMap
    (a b c : ℤ) [IsDomain (CoefficientOrder a b c)] (hD : b^2-4*a*c<0)
    (R : Type*) [Field R] [CharZero R]
    (beta : (FractionRing (CoefficientOrder a b c))ˣ)
    (z : (CoefficientAlgebra (a : R) (b : R) (c : R))ˣ)
    (hz : z.val.norm=(fractionNorm a b c hD beta.val : R)) :
    ∃ y : (CoefficientAlgebra (a : R) (b : R) (c : R))ˣ,
      z.val*star y.val=fractionScalarMap a b c hD R beta.val*y.val := by
  have hd : (b : R)^2-4*(a : R)*(c : R) ≠ 0 := by
    have hn : b^2-4*a*c ≠ 0 := ne_of_lt hD
    exact_mod_cast hn
  let w := Units.map (fractionScalarMap a b c hD R).toMonoidHom beta
  have hn : z.val.norm=w.val.norm := by
    change z.val.norm=(fractionScalarMap a b c hD R beta.val).norm
    rw [norm_fractionScalarMap]
    exact hz
  exact exists_unit_norm_comparison (a : R) (b : R) (c : R) hd z w hn

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- One actual representative of a kernel class has a global canonical
fraction-field unit of norm equal to its same positive rational leading
coefficient. This discharges the Hasse norm input; ideal patching remains. -/
theorem exists_binaryKernelClass_global_norm (K : PositiveDefiniteIntegralLattice 2)
    (xi : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    (hxi : letI := K.binaryDiscriminantOrder_isDomain
      xi ∈ K.binaryIdealLocalNormKernel) :
    letI := K.binaryDiscriminantOrder_isDomain
    ∃ L : PositiveDefiniteIntegralLattice 2, L.binaryContent=K.binaryContent ∧
      ∃ hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant,
        L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD=xi ∧
        ∃ beta : (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))ˣ,
          K.binaryFractionNorm beta.val=(L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) ∧
          ∀ (p : ℕ) [Fact (Nat.Prime p)],
            ∃ z : (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ,
              z.val.norm=((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℚ_[p]) := by
  letI := K.binaryDiscriminantOrder_isDomain
  obtain ⟨L,hg,hD,hclass,hA,hfinite,zReal,hReal⟩ := K.exists_binaryKernelClass_local_norms xi hxi
  obtain ⟨beta,hbeta⟩ := exists_fractionNorm_unit_eq_of_real_and_padic
    1 (K.binaryPrimitiveDiscriminant%2)
    (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)
    K.binaryDiscriminantOrder_discriminant_neg
    ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℚ) (ne_of_gt hA)
    (by exact ⟨zReal.val,by simpa only [Rat.cast_intCast] using hReal⟩)
    (by intro p hp; obtain ⟨z,hz⟩ := hfinite p; exact ⟨z.val,by simpa only [Rat.cast_intCast] using hz⟩)
  exact ⟨L,hg,hD,hclass,beta,hbeta,hfinite⟩

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.four_norm_eq_trace_square
#assert_standard_axioms BinaryNormIdeal.exists_fractionNorm_unit_eq_of_real_and_padic
#assert_standard_axioms BinaryNormIdeal.exists_unit_mul_star_of_norm_eq_one
#assert_standard_axioms BinaryNormIdeal.exists_unit_norm_comparison
#assert_standard_axioms BinaryNormIdeal.exists_unit_compare_fractionScalarMap
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryKernelClass_global_norm

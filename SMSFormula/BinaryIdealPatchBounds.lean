import SMSFormula.BinaryIdealLocalFullness

/-!
# Bounds for the original binary ideal patch

Scalar p-power bounds clear both coefficients in the genuine quadratic
local algebra. Finite support gives one positive integer denominator for
the original-field intersection ideals and their reciprocal candidates.
-/

namespace BinaryNormIdeal

open scoped QuadraticAlgebra nonZeroDivisors

/-- A scalar p-power clears an actual p-adic number. -/
theorem exists_pow_mul_padicInt (p : ℕ) [Fact (Nat.Prime p)] (x : ℚ_[p]) :
    ∃ n : ℕ, ∃ u : ℤ_[p], (u : ℚ_[p])=(p : ℚ_[p])^n*x := by
  obtain ⟨n,hn⟩ := PadicInt.exists_pow_neg_lt p
    (by positivity : 0<(‖x‖+1)⁻¹)
  have hb : ‖(p : ℚ_[p])^n*x‖ ≤ 1 := by
    rw [norm_mul,Padic.norm_p_pow]
    calc
      (p : ℝ)^(-(n : ℤ))*‖x‖ ≤ (‖x‖+1)⁻¹*(‖x‖+1) :=
        mul_le_mul (le_of_lt hn) (by linarith) (norm_nonneg _) (by positivity)
      _=1 := inv_mul_cancel₀ (by positivity)
  exact ⟨n,⟨_,hb⟩,rfl⟩

/-- Clearing two scalar coefficients suffices even if the local algebra
splits or has nilpotents. The exponent can be strictly positive. -/
theorem exists_pos_pow_mul_mem_padicOrder (p : ℕ) [Fact (Nat.Prime p)]
    (D : ℤ) (z : DiscriminantAlgebra ℚ_[p] D) :
    letI := padicOrderAlgebra p D
    ∃ n : ℕ, 0<n ∧ (p : DiscriminantAlgebra ℚ_[p] D)^n*z ∈
      (1 : Submodule (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D)) := by
  letI := padicOrderAlgebra p D
  obtain ⟨n,u,hu⟩ := exists_pow_mul_padicInt p z.re
  obtain ⟨m,v,hv⟩ := exists_pow_mul_padicInt p z.im
  refine ⟨n+m+1,by omega,Submodule.mem_one.mpr ⟨⟨(p : ℤ_[p])^(m+1)*u,
    (p : ℤ_[p])^(n+1)*v⟩,?_⟩⟩
  change padicOrderMap p D _=_
  rw [show (p : DiscriminantAlgebra ℚ_[p] D)^(n+m+1)=
    algebraMap ℚ_[p] _ ((p : ℚ_[p])^(n+m+1)) by simp]
  apply QuadraticAlgebra.ext
  · rw [QuadraticAlgebra.re_mul,QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im]
    simp only [zero_mul,mul_zero,add_zero]
    change (((p : ℤ_[p])^(m+1)*u : ℤ_[p]) : ℚ_[p])=(p : ℚ_[p])^(n+m+1)*z.re
    push_cast
    rw [hu]
    simp only [pow_add,pow_one]
    ring
  · rw [QuadraticAlgebra.im_mul,QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im]
    simp only [zero_mul,mul_zero,add_zero]
    change (((p : ℤ_[p])^(n+1)*v : ℤ_[p]) : ℚ_[p])=(p : ℚ_[p])^(n+m+1)*z.im
    push_cast
    rw [hv]
    simp only [pow_add,pow_one]
    ring

/-- Multiplication by an integral natural scalar preserves the local order. -/
lemma natCast_mul_mem_padicOrder (p : ℕ) [Fact (Nat.Prime p)] (D : ℤ)
    (z : DiscriminantAlgebra ℚ_[p] D) (n : ℕ)
    (hz : letI := padicOrderAlgebra p D
      z ∈ (1 : Submodule (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D))) :
    letI := padicOrderAlgebra p D
    (n : DiscriminantAlgebra ℚ_[p] D)*z ∈
      (1 : Submodule (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D)) := by
  letI := padicOrderAlgebra p D
  simpa only [Algebra.smul_def,map_natCast] using
    (1 : Submodule (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D)).smul_mem
      (n : DiscriminantAlgebra ℤ_[p] D) hz

/-- One positive p-power clears a local unit and its actual inverse. -/
theorem exists_pos_pow_mul_unit_and_inv_mem_padicOrder
    (p : ℕ) [Fact (Nat.Prime p)] (D : ℤ)
    (y : (DiscriminantAlgebra ℚ_[p] D)ˣ) :
    letI := padicOrderAlgebra p D
    ∃ n : ℕ, 0<n ∧
      (p : DiscriminantAlgebra ℚ_[p] D)^n*y.val ∈
        (1 : Submodule (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D)) ∧
      (p : DiscriminantAlgebra ℚ_[p] D)^n*(y⁻¹).val ∈
        (1 : Submodule (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D)) := by
  letI := padicOrderAlgebra p D
  obtain ⟨n,hn,hy⟩ := exists_pos_pow_mul_mem_padicOrder p D y.val
  obtain ⟨m,hm,hi⟩ := exists_pos_pow_mul_mem_padicOrder p D (y⁻¹).val
  refine ⟨n+m,by omega,?_,?_⟩
  · convert natCast_mul_mem_padicOrder p D _ (p^m) hy using 1
    push_cast
    ring
  · convert natCast_mul_mem_padicOrder p D _ (p^n) hi using 1
    push_cast
    ring

/-- A finite family has one positive integer clearing every local unit
and its reciprocal. All prime divisors of that integer belong to the
specified finite prime set. -/
theorem exists_common_padicOrder_denominator (D : ℤ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (y : ∀ (p : ℕ) [Fact (Nat.Prime p)], (DiscriminantAlgebra ℚ_[p] D)ˣ)
    (hy : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∉ S → y p=1) :
    ∃ M : ℕ, 0<M ∧ (∀ p : ℕ, p.Prime → p ∣ M → p ∈ S) ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        letI := padicOrderAlgebra p D
        (M : DiscriminantAlgebra ℚ_[p] D)*(y p).val ∈
            (1 : Submodule (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D)) ∧
          (M : DiscriminantAlgebra ℚ_[p] D)*((y p)⁻¹).val ∈
            (1 : Submodule (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D)) := by
  classical
  have h (p : ℕ) (hp : p ∈ S) :
      letI : Fact (Nat.Prime p) := ⟨hS p hp⟩
      letI := padicOrderAlgebra p D
      ∃ n : ℕ, 0<n ∧
        (p : DiscriminantAlgebra ℚ_[p] D)^n*(y p).val ∈
            (1 : Submodule (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D)) ∧
          (p : DiscriminantAlgebra ℚ_[p] D)^n*((y p)⁻¹).val ∈
            (1 : Submodule (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D)) := by
    letI : Fact (Nat.Prime p) := ⟨hS p hp⟩
    exact exists_pos_pow_mul_unit_and_inv_mem_padicOrder p D (y p)
  choose n hnpos hn hninv using h
  let e (p : ℕ) : ℕ := if hp : p ∈ S then n p hp else 0
  let M : ℕ := ∏ p ∈ S, p^(e p)
  have hpos : 0<M := Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos _)
  refine ⟨M,hpos,?_,?_⟩
  · intro p hp hpd
    obtain ⟨q,hq,hqp⟩ := (hp.prime.dvd_finsetProd_iff (fun q => q^(e q))).mp hpd
    have heq : p=q := (Nat.prime_dvd_prime_iff_eq hp (hS q hq)).mp
      (hp.dvd_of_dvd_pow hqp)
    exact heq.symm ▸ hq
  · intro p hp
    letI := padicOrderAlgebra p D
    by_cases hmem : p ∈ S
    · have hdiv : p^(n p hmem) ∣ M := by
        simpa only [e,dif_pos hmem] using (Finset.dvd_prod_of_mem (fun q => q^(e q)) hmem)
      obtain ⟨k,hk⟩ := hdiv
      have ha := natCast_mul_mem_padicOrder p D _ k (hn p hmem)
      have hb := natCast_mul_mem_padicOrder p D _ k (hninv p hmem)
      constructor
      · convert ha using 1
        simp [hk,Nat.cast_mul,Nat.cast_pow]
        ring
      · convert hb using 1
        simp [hk,Nat.cast_mul,Nat.cast_pow]
        ring
    · rw [hy p hmem]
      simp only [Units.val_one,inv_one,mul_one]
      exact ⟨Submodule.mem_one.mpr ⟨(M : DiscriminantAlgebra ℤ_[p] D),map_natCast _ _⟩,
        Submodule.mem_one.mpr ⟨(M : DiscriminantAlgebra ℤ_[p] D),map_natCast _ _⟩⟩

/-- An integral M*y inverse puts the original scalar M in the principal
local span of y. No scalar division occurs in the integral order. -/
lemma natCast_mem_padic_unit_span (p : ℕ) [Fact (Nat.Prime p)] (D : ℤ)
    (y : (DiscriminantAlgebra ℚ_[p] D)ˣ) (M : ℕ)
    (h : letI := padicOrderAlgebra p D
      (M : DiscriminantAlgebra ℚ_[p] D)*(y⁻¹).val ∈
        (1 : Submodule (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D))) :
    letI := padicOrderAlgebra p D
    (M : DiscriminantAlgebra ℚ_[p] D) ∈
      Submodule.span (DiscriminantAlgebra ℤ_[p] D) {y.val} := by
  letI := padicOrderAlgebra p D
  obtain ⟨r,hr⟩ := Submodule.mem_one.mp h
  apply Submodule.mem_span_singleton.mpr
  refine ⟨r,?_⟩
  rw [Algebra.smul_def,hr,mul_assoc,← Units.val_mul,inv_mul_cancel,Units.val_one,mul_one]

/-- An integral M*y bounds its whole principal span above, with exact
membership in the actual local order. -/
lemma natCast_mul_padic_unit_span_mem_one (p : ℕ) [Fact (Nat.Prime p)] (D : ℤ)
    (y : (DiscriminantAlgebra ℚ_[p] D)ˣ) (M : ℕ)
    (h : letI := padicOrderAlgebra p D
      (M : DiscriminantAlgebra ℚ_[p] D)*y.val ∈
        (1 : Submodule (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D)))
    (z : DiscriminantAlgebra ℚ_[p] D)
    (hz : letI := padicOrderAlgebra p D
      z ∈ Submodule.span (DiscriminantAlgebra ℤ_[p] D) {y.val}) :
    letI := padicOrderAlgebra p D
    (M : DiscriminantAlgebra ℚ_[p] D)*z ∈
      (1 : Submodule (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D)) := by
  letI := padicOrderAlgebra p D
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hz
  rw [← hr,Algebra.smul_def]
  convert (1 : Submodule (DiscriminantAlgebra ℤ_[p] D)
    (DiscriminantAlgebra ℚ_[p] D)).smul_mem r h using 1
  rw [Algebra.smul_def]
  ring

/-- A finite family of integral local coefficient pairs has one original
order representative modulo the specified prime powers. This is actual
principal-ideal membership, not a metric density assertion. -/
theorem exists_order_simultaneous_padic_residues (D : ℤ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℕ)
    (z : ∀ (p : ℕ) [Fact (Nat.Prime p)], DiscriminantAlgebra ℤ_[p] D) :
    ∃ w : DiscriminantOrder D, ∀ p : ℕ, ∀ hp : p ∈ S,
      letI : Fact (Nat.Prime p) := ⟨hS p hp⟩
      z p-orderScalarMap 1 (D%2) (((D%2)^2-D)/4) ℤ_[p] w ∈
        Ideal.span {(p : DiscriminantAlgebra ℤ_[p] D)^(e p)} := by
  classical
  let ar (p : ℕ) : ℕ := if hp : p ∈ S then
    letI : Fact (Nat.Prime p) := ⟨hS p hp⟩
    (z p).re.appr (e p) else 0
  let ai (p : ℕ) : ℕ := if hp : p ∈ S then
    letI : Fact (Nat.Prime p) := ⟨hS p hp⟩
    (z p).im.appr (e p) else 0
  have hnz (p : ℕ) (hp : p ∈ S) : p^(e p) ≠ 0 := pow_ne_zero _ (hS p hp).ne_zero
  have hcop : Set.Pairwise (S : Set ℕ) (Function.onFun Nat.Coprime (fun p => p^(e p))) := by
    intro p hp q hq hpq
    exact Nat.coprime_pow_primes _ _ (hS p hp) (hS q hq) hpq
  let wr := Nat.chineseRemainderOfFinset ar (fun p => p^(e p)) S hnz hcop
  let wi := Nat.chineseRemainderOfFinset ai (fun p => p^(e p)) S hnz hcop
  refine ⟨⟨(wr.val : ℤ),(wi.val : ℤ)⟩,?_⟩
  intro p hp
  letI : Fact (Nat.Prime p) := ⟨hS p hp⟩
  have hcoord (x : ℤ_[p]) (v : ℕ)
      (hv : v ≡ x.appr (e p) [MOD p^(e p)]) :
      (p : ℤ_[p])^(e p) ∣ x-(v : ℤ_[p]) := by
    have hd := map_dvd (Int.castRingHom ℤ_[p]) hv.dvd
    have hd' : (p : ℤ_[p])^(e p) ∣ (x.appr (e p) : ℤ_[p])-(v : ℤ_[p]) := by
      simpa only [map_sub,map_pow,map_natCast,Nat.cast_pow] using hd
    have ha := Ideal.mem_span_singleton.mp (PadicInt.appr_spec (e p) x)
    convert dvd_add ha hd' using 1
    ring
  have hr := hcoord (z p).re wr.val (by simpa only [ar,dif_pos hp] using wr.property p hp)
  have hi := hcoord (z p).im wi.val (by simpa only [ai,dif_pos hp] using wi.property p hp)
  obtain ⟨r,hr⟩ := hr
  obtain ⟨t,ht⟩ := hi
  apply Ideal.mem_span_singleton.mpr
  refine ⟨⟨r,t⟩,?_⟩
  rw [show (p : DiscriminantAlgebra ℤ_[p] D)^(e p)=
    algebraMap ℤ_[p] _ ((p : ℤ_[p])^(e p)) by simp]
  apply QuadraticAlgebra.ext
  · rw [QuadraticAlgebra.re_mul,QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im]
    simpa [orderScalarMap,coefficientScalarMap] using hr
  · rw [QuadraticAlgebra.im_mul,QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im]
    simpa [orderScalarMap,coefficientScalarMap] using ht

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal
open scoped nonZeroDivisors

/-- The intersection is an actual submodule of the original fraction field.
The local factors are ambient units, not necessarily integral units. -/
noncomputable def binaryIdealPatchSubmodule (K : PositiveDefiniteIntegralLattice 2)
    (y : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ) :
    Submodule (DiscriminantOrder K.binaryPrimitiveDiscriminant)
      (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact {
    carrier := {z | ∀ (p : ℕ) [Fact (Nat.Prime p)],
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      K.binaryPadicFractionMap p z ∈
        Submodule.span (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant) {(y p).val}}
    zero_mem' := by intro p hp; simp only [map_zero]; exact Submodule.zero_mem _
    add_mem' := by
      intro x z hx hz p hp
      rw [map_add]
      exact Submodule.add_mem _ (hx p) (hz p)
    smul_mem' := by
      intro r z hz p hp
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      rw [Algebra.smul_def,map_mul,K.binaryPadicFractionMap_compatible]
      exact (Submodule.span (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
        {(y p).val}).smul_mem
          (orderScalarMap 1 (K.binaryPrimitiveDiscriminant%2)
            (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) ℤ_[p] r) (hz p) }

/-- The common reciprocal bound puts the original integer in the global
intersection. Ideal closure then supplies the full lower lattice M*O. -/
theorem natCast_mem_binaryIdealPatchSubmodule (K : PositiveDefiniteIntegralLattice 2)
    (y : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ) (M : ℕ)
    (h : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      (M : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)*((y p)⁻¹).val ∈
        (1 : Submodule (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
          (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant))) :
    (M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ∈
      K.binaryIdealPatchSubmodule y := by
  letI := K.binaryDiscriminantOrder_isDomain
  intro p hp
  rw [map_natCast]
  exact natCast_mem_padic_unit_span p _ (y p) M (h p)

/-- The common coefficient bound gives an original integral element after
multiplication by M. The all-prime order detector has no inverse premise. -/
theorem natCast_mul_binaryIdealPatchSubmodule_mem_one (K : PositiveDefiniteIntegralLattice 2)
    (y : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ) (M : ℕ)
    (h : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      (M : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)*(y p).val ∈
        (1 : Submodule (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
          (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)))
    (z : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    (hz : z ∈ K.binaryIdealPatchSubmodule y) :
    letI := K.binaryDiscriminantOrder_isDomain
    (M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))*z ∈
      (1 : K.BinaryDiscriminantFractionalIdeals) := by
  letI := K.binaryDiscriminantOrder_isDomain
  apply (K.binaryFraction_mem_one_iff_padic _).mpr
  intro p hp
  rw [map_mul,map_natCast]
  exact natCast_mul_padic_unit_span_mem_one p _ (y p) M (h p) _ (hz p)

/-- The proved upper bound supplies a nonzero original denominator.
Invertibility and finite generation need not precede this carrier. -/
theorem binaryIdealPatchSubmodule_isFractional (K : PositiveDefiniteIntegralLattice 2)
    (y : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ)
    (M : ℕ) (hM : 0<M)
    (h : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      (M : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)*(y p).val ∈
        (1 : Submodule (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
          (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant))) :
    IsFractional (DiscriminantOrder K.binaryPrimitiveDiscriminant)⁰
      (K.binaryIdealPatchSubmodule y) := by
  letI := K.binaryDiscriminantOrder_isDomain
  refine ⟨(M : DiscriminantOrder K.binaryPrimitiveDiscriminant),?_,?_⟩
  · apply mem_nonZeroDivisors_iff_ne_zero.mpr
    exact_mod_cast (ne_of_gt hM)
  · intro z hz
    change ∃ w : DiscriminantOrder K.binaryPrimitiveDiscriminant,
      algebraMap _ _ w=(M : DiscriminantOrder K.binaryPrimitiveDiscriminant) • z
    simpa only [Algebra.smul_def,map_natCast] using
      (FractionalIdeal.mem_one_iff _).mp (K.natCast_mul_binaryIdealPatchSubmodule_mem_one y M h z hz)

/-- Finite support constructs both actual fractional-ideal carriers with
their exact all-prime membership conditions and one common scalar bound.
This does not yet identify their extended local spans. -/
theorem exists_binaryIdealPatch_pair (K : PositiveDefiniteIntegralLattice 2) (S : Finset ℕ)
    (y : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ)
    (hy : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∉ S → y p=1) :
    letI := K.binaryDiscriminantOrder_isDomain
    ∃ M : ℕ, 0<M ∧ (∀ p : ℕ, p.Prime → p ∣ M → p ∈ S) ∧
      (∀ (p : ℕ) [Fact (Nat.Prime p)],
        letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
        (M : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)*(y p).val ∈
          (1 : Submodule (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
            (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)) ∧
        (M : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)*((y p)⁻¹).val ∈
          (1 : Submodule (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
            (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant))) ∧
      ∃ J Jprime : K.BinaryDiscriminantFractionalIdeals,
        (J : Submodule (DiscriminantOrder K.binaryPrimitiveDiscriminant)
          (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))=
            K.binaryIdealPatchSubmodule y ∧
        (Jprime : Submodule (DiscriminantOrder K.binaryPrimitiveDiscriminant)
          (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))=
            K.binaryIdealPatchSubmodule (fun p _ => (y p)⁻¹) ∧
        (M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ∈ J ∧
        (M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ∈ Jprime ∧
        (∀ z ∈ J, (M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))*z ∈
          (1 : K.BinaryDiscriminantFractionalIdeals)) ∧
        (∀ z ∈ Jprime, (M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))*z ∈
          (1 : K.BinaryDiscriminantFractionalIdeals)) ∧
        ((M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))^2 ∈ J*Jprime) := by
  classical
  letI := K.binaryDiscriminantOrder_isDomain
  let T := S.filter Nat.Prime
  have hT (p : ℕ) (hp : p ∈ T) : p.Prime := (Finset.mem_filter.mp hp).2
  have hyT (p : ℕ) [hp : Fact (Nat.Prime p)] (hpT : p ∉ T) : y p=1 := by
    apply hy p
    intro hpS
    exact hpT (Finset.mem_filter.mpr ⟨hpS,hp.out⟩)
  obtain ⟨M,hM,hsupp,hbound⟩ := exists_common_padicOrder_denominator
    K.binaryPrimitiveDiscriminant T hT y hyT
  let J : K.BinaryDiscriminantFractionalIdeals :=
    ⟨K.binaryIdealPatchSubmodule y,
      K.binaryIdealPatchSubmodule_isFractional y M hM (fun p _ => (hbound p).1)⟩
  let Jprime : K.BinaryDiscriminantFractionalIdeals :=
    ⟨K.binaryIdealPatchSubmodule (fun p _ => (y p)⁻¹),
      K.binaryIdealPatchSubmodule_isFractional (fun p _ => (y p)⁻¹) M hM
        (fun p _ => (hbound p).2)⟩
  have hMJ : (M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ∈ J :=
    K.natCast_mem_binaryIdealPatchSubmodule y M (fun p _ => (hbound p).2)
  have hMJprime : (M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ∈ Jprime :=
    K.natCast_mem_binaryIdealPatchSubmodule (fun p _ => (y p)⁻¹) M
      (fun p _ => by simpa only [inv_inv] using (hbound p).1)
  refine ⟨M,hM,(fun p hp hd => (Finset.mem_filter.mp (hsupp p hp hd)).1),
    hbound,J,Jprime,rfl,rfl,hMJ,hMJprime,?_,?_,?_⟩
  · exact fun z hz => K.natCast_mul_binaryIdealPatchSubmodule_mem_one y M
      (fun p _ => (hbound p).1) z hz
  · exact fun z hz => K.natCast_mul_binaryIdealPatchSubmodule_mem_one (fun p _ => (y p)⁻¹) M
      (fun p _ => (hbound p).2) z hz
  · simpa only [pow_two] using FractionalIdeal.mul_mem_mul hMJ hMJprime

/-- Extension of the actual intersection is contained in the prescribed
principal local span. Equality still needs the finite CRT construction. -/
theorem binaryPadicIdealExtension_le_patch_span (K : PositiveDefiniteIntegralLattice 2)
    (y : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ)
    (J : K.BinaryDiscriminantFractionalIdeals)
    (hJ : (J : Submodule (DiscriminantOrder K.binaryPrimitiveDiscriminant)
      (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))=
        K.binaryIdealPatchSubmodule y) (p : ℕ) [Fact (Nat.Prime p)] :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    K.binaryPadicIdealExtension p J ≤
      Submodule.span (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant) {(y p).val} := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  apply Submodule.span_le.mpr
  rintro _ ⟨z,hz,rfl⟩
  change z ∈ (J : Submodule (DiscriminantOrder K.binaryPrimitiveDiscriminant)
    (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) at hz
  rw [hJ] at hz
  exact hz p

/-- The two actual intersection ideals have an integral global product.
This direction uses only inclusion into the known invertible target one. -/
theorem binaryIdealPatch_product_le_one (K : PositiveDefiniteIntegralLattice 2)
    (y : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ)
    (J Jprime : K.BinaryDiscriminantFractionalIdeals)
    (hJ : (J : Submodule (DiscriminantOrder K.binaryPrimitiveDiscriminant)
      (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))=K.binaryIdealPatchSubmodule y)
    (hJprime : (Jprime : Submodule (DiscriminantOrder K.binaryPrimitiveDiscriminant)
      (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))=
        K.binaryIdealPatchSubmodule (fun p _ => (y p)⁻¹)) :
    letI := K.binaryDiscriminantOrder_isDomain
    J*Jprime ≤ (1 : K.BinaryDiscriminantFractionalIdeals) := by
  letI := K.binaryDiscriminantOrder_isDomain
  apply (K.binaryFractionalIdeal_le_unit_iff_padic (J*Jprime) 1).mpr
  intro p hp
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  rw [map_mul,Units.val_one,map_one]
  calc
    K.binaryPadicIdealExtension p J*K.binaryPadicIdealExtension p Jprime ≤
        Submodule.span _ {(y p).val}*Submodule.span _ {((y p)⁻¹).val} :=
      mul_le_mul' (K.binaryPadicIdealExtension_le_patch_span y J hJ p)
        (K.binaryPadicIdealExtension_le_patch_span (fun p _ => (y p)⁻¹) Jprime hJprime p)
    _ = Submodule.span _ {(y p).val*((y p)⁻¹).val} :=
      ((Submodule.spanSingleton _).map_mul _ _).symm
    _ = 1 := by rw [← Units.val_mul,mul_inv_cancel,Units.val_one,← Submodule.one_eq_span]

/-- The local realization is already exact wherever the factor is one
and the common denominator is a local scalar unit. Exceptional primes
still require the finite coefficient CRT argument. -/
theorem binaryPadicIdealExtension_patch_eq_one_of_natCast_mem
    (K : PositiveDefiniteIntegralLattice 2)
    (y : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ)
    (J : K.BinaryDiscriminantFractionalIdeals)
    (hJ : (J : Submodule (DiscriminantOrder K.binaryPrimitiveDiscriminant)
      (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))=K.binaryIdealPatchSubmodule y)
    (M : ℕ) (hMJ : (M : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ∈ J)
    (p : ℕ) [Fact (Nat.Prime p)] (hy : y p=1) (hM : ¬p ∣ M) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    K.binaryPadicIdealExtension p J=1 := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  have hu : IsUnit (M : DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant) := by
    have h := (isUnit_padic_intCast_of_not_dvd (M : ℤ) p (by exact_mod_cast hM)).map
      (algebraMap ℤ_[p] (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant))
    simpa only [Int.cast_natCast,map_natCast] using h
  have hspan : Submodule.span (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
      {(M : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)}=1 := by
    simpa only [map_natCast] using Submodule.span_singleton_algebraMap_of_isUnit hu
  apply le_antisymm
  · have hh := K.binaryPadicIdealExtension_le_patch_span y J hJ p
    simpa only [hy,Units.val_one,← Submodule.one_eq_span] using hh
  · rw [← hspan]
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    simpa only [map_natCast] using K.binaryPadicFractionMap_mem_idealExtension J _ hMJ p

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.exists_pow_mul_padicInt
#assert_standard_axioms BinaryNormIdeal.exists_pos_pow_mul_mem_padicOrder
#assert_standard_axioms BinaryNormIdeal.natCast_mul_mem_padicOrder
#assert_standard_axioms BinaryNormIdeal.exists_pos_pow_mul_unit_and_inv_mem_padicOrder
#assert_standard_axioms BinaryNormIdeal.exists_common_padicOrder_denominator
#assert_standard_axioms BinaryNormIdeal.natCast_mem_padic_unit_span
#assert_standard_axioms BinaryNormIdeal.natCast_mul_padic_unit_span_mem_one
#assert_standard_axioms BinaryNormIdeal.exists_order_simultaneous_padic_residues
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealPatchSubmodule
#assert_standard_axioms PositiveDefiniteIntegralLattice.natCast_mem_binaryIdealPatchSubmodule
#assert_standard_axioms PositiveDefiniteIntegralLattice.natCast_mul_binaryIdealPatchSubmodule_mem_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealPatchSubmodule_isFractional
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryIdealPatch_pair
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicIdealExtension_le_patch_span
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIdealPatch_product_le_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicIdealExtension_patch_eq_one_of_natCast_mem

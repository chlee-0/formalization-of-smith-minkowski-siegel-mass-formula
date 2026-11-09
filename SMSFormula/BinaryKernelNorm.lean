import SMSFormula.BinaryGenusKernel

/-!
# Local norm witnesses and quadratic Hilbert 90 on the actual carriers

A kernel class gives norm witnesses for its positive rational leading
coefficient at every finite place and at infinity. The finite quadratic
algebra may split. Quadratic Hilbert 90 is proved directly on the original
canonical fraction field, without a Galois-cohomology import.
-/

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The local ideal generator has norm exactly A*u. -/
lemma norm_binaryPadicIdealGeneratorUnit (K L : PositiveDefiniteIntegralLattice 2)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (p : ℕ) [Fact (Nat.Prime p)] (v : Fin 2 → ℤ_[p]) (u : ℤ_[p]ˣ)
    (hv : L.binaryPrimitivePolynomialOver ℤ_[p] v=(u : ℤ_[p])) :
    (binaryPadicIdealGeneratorUnit K L hD p v u hv).val.norm=
      ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℚ_[p])*((u : ℤ_[p]) : ℚ_[p]) := by
  rw [binaryPadicIdealGeneratorUnit_val,padicOrderMap,norm_coefficientScalarMap,
    norm_binaryLocalIdealGeneratorAt,hv,map_mul,map_intCast]
  rfl

/-- A class in the actual finite-place kernel gives a norm witness for its
leading coefficient in the genuine quadratic Q_p algebra, including split
cases. The leading coefficient is not inverted in the integral order. -/
theorem exists_binaryKernel_leading_padic_norm (K L : PositiveDefiniteIntegralLattice 2)
    (hg : L.binaryContent=K.binaryContent)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (hk : letI := K.binaryDiscriminantOrder_isDomain
      L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD ∈ K.binaryIdealLocalNormKernel)
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ z : (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ,
      z.val.norm=((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℚ_[p]) := by
  letI := K.binaryDiscriminantOrder_isDomain
  obtain ⟨v,u,hu⟩ := L.binaryPrimitivePolynomialOver_padic_exists_unit p
  have hv := hu.symm
  have hm : orderUnitNormQuotientMap ℤ_[p] K.binaryPrimitiveDiscriminant u=1 :=
    (K.binaryIdealLocalNormHom_apply L hg hD p v u hv).symm.trans (hk p)
  obtain ⟨e,he⟩ := (orderUnitNormQuotientMap_eq_iff ℤ_[p] K.binaryPrimitiveDiscriminant u 1).mp hm
  simp only [Units.val_one,one_mul] at he
  let alpha := binaryPadicIdealGeneratorUnit K L hD p v u hv
  let E := Units.map (padicOrderMap p K.binaryPrimitiveDiscriminant).toMonoidHom e
  let z := alpha*E⁻¹
  refine ⟨z,?_⟩
  have hE : E.val.norm=((u : ℤ_[p]) : ℚ_[p]) := by
    change (padicOrderMap p K.binaryPrimitiveDiscriminant e.val).norm=_
    rw [padicOrderMap,norm_coefficientScalarMap,← he]
    rfl
  have hmul : z.val*E.val=alpha.val := by
    change ((alpha*E⁻¹)*E).val=alpha.val
    simp
  have hn := congrArg QuadraticAlgebra.norm hmul
  rw [map_mul,hE,norm_binaryPadicIdealGeneratorUnit] at hn
  have hnu : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0 := fun h => u.ne_zero (PadicInt.ext h)
  exact mul_right_cancel₀ hnu hn

/-- The same positive leading coefficient is an actual real quadratic norm.
This uses a scalar square root and adds no caller real-place certificate. -/
theorem exists_binary_leading_real_norm (L : PositiveDefiniteIntegralLattice 2) (D : ℤ) :
    ∃ z : (DiscriminantAlgebra ℝ D)ˣ,
      z.val.norm=((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℝ) := by
  let a : ℝ := ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℝ)
  have ha : 0<a := by
    dsimp only [a]
    exact_mod_cast L.binaryPrimitivePolynomial_leading_pos
  let u : ℝˣ := Units.mk0 (Real.sqrt a) (ne_of_gt (Real.sqrt_pos.mpr ha))
  refine ⟨Units.map (algebraMap ℝ (DiscriminantAlgebra ℝ D)) u,?_⟩
  simp [u,QuadraticAlgebra.norm_def,← pow_two,Real.sq_sqrt ha.le,a]

/-- One actual lattice at the original (g,D) realizes a kernel class and
supplies the same positive rational leading coefficient as a norm at every
finite place and infinity. This is not a local-global norm theorem. -/
theorem exists_binaryKernelClass_local_norms (K : PositiveDefiniteIntegralLattice 2)
    (xi : letI := K.binaryDiscriminantOrder_isDomain
      ClassGroup (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    (hxi : letI := K.binaryDiscriminantOrder_isDomain
      xi ∈ K.binaryIdealLocalNormKernel) :
    letI := K.binaryDiscriminantOrder_isDomain
    ∃ L : PositiveDefiniteIntegralLattice 2, L.binaryContent=K.binaryContent ∧
      ∃ hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant,
        L.binaryIdealClassAt K.binaryPrimitiveDiscriminant hD=xi ∧
        (0 : ℚ)<(L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) ∧
        (∀ (p : ℕ) [Fact (Nat.Prime p)],
          ∃ z : (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ,
            z.val.norm=((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℚ_[p])) ∧
        ∃ z : (DiscriminantAlgebra ℝ K.binaryPrimitiveDiscriminant)ˣ,
          z.val.norm=((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℝ) := by
  letI := K.binaryDiscriminantOrder_isDomain
  obtain ⟨L,hg,hD,hclass⟩ := K.exists_lattice_of_binaryIdealClass xi
  refine ⟨L,hg,hD,hclass,?_,?_,L.exists_binary_leading_real_norm _⟩
  · exact_mod_cast L.binaryPrimitivePolynomial_leading_pos
  · intro p hp
    exact K.exists_binaryKernel_leading_padic_norm L hg hD (hclass ▸ hxi) p

end PositiveDefiniteIntegralLattice

namespace BinaryNormIdeal

open scoped nonZeroDivisors QuadraticAlgebra

/-- Every rational coefficient pair comes from the original canonical
fraction field. This is the inverse carrier bridge needed by a conic proof. -/
theorem fractionRationalMap_surjective (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]
    (hD : b^2-4*a*c<0) : Function.Surjective (fractionRationalMap a b c hD) := by
  letI := fractionField_charZero a b c hD
  letI := rationalField a b c hD
  intro w
  refine ⟨(w.re : FractionRing (CoefficientOrder a b c))+
    (w.im : FractionRing (CoefficientOrder a b c))*algebraMap _ _ (QuadraticAlgebra.omega : CoefficientOrder a b c),?_⟩
  rw [map_add,map_mul,map_ratCast,map_ratCast,fractionRationalMap_algebraMap]
  apply QuadraticAlgebra.ext <;> simp [rationalMap]

/-- Exact equivalence with the rational quadratic coefficient field. -/
noncomputable def fractionRationalEquiv (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]
    (hD : b^2-4*a*c<0) :
    FractionRing (CoefficientOrder a b c) ≃+* CoefficientAlgebra (a : ℚ) (b : ℚ) (c : ℚ) := by
  letI := rationalField a b c hD
  exact RingEquiv.ofBijective (fractionRationalMap a b c hD)
    ⟨(fractionRationalMap a b c hD).injective,fractionRationalMap_surjective a b c hD⟩

/-- Rational conic solvability is exactly actual canonical field-norm
solvability. No local-global solvability assertion is introduced. -/
theorem exists_fractionNorm_eq_iff_conic (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]
    (hD : b^2-4*a*c<0) (q : ℚ) :
    (∃ z : FractionRing (CoefficientOrder a b c), fractionNorm a b c hD z=q) ↔
      ∃ s t : ℚ, s^2+(b : ℚ)*s*t+(a : ℚ)*(c : ℚ)*t^2=q := by
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨(fractionRationalMap a b c hD z).re,(fractionRationalMap a b c hD z).im,?_⟩
    change (fractionRationalMap a b c hD z).norm=q at hz
    rw [QuadraticAlgebra.norm_def] at hz
    linear_combination hz
  · rintro ⟨s,t,hst⟩
    obtain ⟨z,hz⟩ := fractionRationalMap_surjective a b c hD ⟨s,t⟩
    refine ⟨z,?_⟩
    change (fractionRationalMap a b c hD z).norm=q
    rw [hz,QuadraticAlgebra.norm_def]
    linear_combination hst

/-- Quadratic Hilbert 90 on the original canonical FractionRing. The two
branches are explicit: 1+x, or the anti-invariant element 2*theta-b at x=-1.
No generic Galois or number-field norm identification is assumed. -/
theorem exists_fraction_div_conjugation_of_norm_eq_one
    (a b c : ℤ) [IsDomain (CoefficientOrder a b c)] (hD : b^2-4*a*c<0)
    (x : FractionRing (CoefficientOrder a b c)) (hx : fractionNorm a b c hD x=1) :
    ∃ y : (FractionRing (CoefficientOrder a b c))ˣ,
      (y : FractionRing (CoefficientOrder a b c))/fractionConjugation a b c y.val=x := by
  letI := fractionField_charZero a b c hD
  by_cases hm : x=-1
  · subst x
    let j : FractionRing (CoefficientOrder a b c) :=
      algebraMap _ _ (⟨-b,2⟩ : CoefficientOrder a b c)
    have hj : j ≠ 0 := by
      intro h
      have hh := congrArg (fun w => (fractionRationalMap a b c hD w).im) h
      dsimp only [j] at hh
      rw [fractionRationalMap_algebraMap,map_zero] at hh
      norm_num [rationalMap] at hh
    have hs : fractionConjugation a b c j=-j := by
      dsimp only [j]
      rw [fractionConjugation_algebraMap,← map_neg]
      congr 1
      apply QuadraticAlgebra.ext
      · simp
        ring
      · simp
    refine ⟨Units.mk0 j hj,?_⟩
    change j/fractionConjugation a b c j=-1
    rw [hs,div_neg_self hj]
  · have hy : 1+x ≠ 0 := by
      intro h
      apply hm
      linear_combination h
    have hmul : x*fractionConjugation a b c x=1 := by
      rw [fraction_mul_conjugation a b c hD,hx]
      simp
    refine ⟨Units.mk0 (1+x) hy,?_⟩
    change (1+x)/fractionConjugation a b c (1+x)=x
    apply (div_eq_iff (by simpa only [map_zero] using (fractionConjugation a b c).injective.ne hy)).mpr
    rw [map_add,map_one,mul_add,mul_one,hmul]
    ring

end BinaryNormIdeal

#assert_standard_axioms PositiveDefiniteIntegralLattice.norm_binaryPadicIdealGeneratorUnit
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryKernel_leading_padic_norm
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binary_leading_real_norm
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryKernelClass_local_norms
#assert_standard_axioms BinaryNormIdeal.fractionRationalMap_surjective
#assert_standard_axioms BinaryNormIdeal.fractionRationalEquiv
#assert_standard_axioms BinaryNormIdeal.exists_fractionNorm_eq_iff_conic
#assert_standard_axioms BinaryNormIdeal.exists_fraction_div_conjugation_of_norm_eq_one

import SMSFormula.BinaryPicardExtension
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Recovering actual conductor residues from the Picard kernel

A finite CRT argument chooses one reciprocal residue pair in an actual
invertible fractional ideal and its actual inverse. No coprime representative
or residue generator is supplied by the caller.
-/

open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F]

omit [IsDomain R] [IsFractionRing R F] in
/-- Products in an actual ideal-unit inverse pair lie in the original ring. -/
theorem unit_pair_mul_mem_one (J : (FractionalIdeal R⁰ F)ˣ)
    (x : J.val) (y : J⁻¹.val) : (x : F)*(y : F) ∈ (1 : FractionalIdeal R⁰ F) := by
  have h := mul_mem_mul x.prop y.prop
  have hJJ : J.val*J⁻¹.val=(1 : FractionalIdeal R⁰ F) := by
    exact J.mul_inv
  rwa [hJJ] at h

omit [IsDomain R] [IsFractionRing R F] in
/-- The original-ring coefficient of the actual product. -/
noncomputable def unitPairCoefficient (J : (FractionalIdeal R⁰ F)ˣ)
    (x : J.val) (y : J⁻¹.val) : R :=
  Classical.choose ((mem_one_iff R⁰).mp (unit_pair_mul_mem_one J x y))

omit [IsDomain R] [IsFractionRing R F] in
theorem unitPairCoefficient_spec (J : (FractionalIdeal R⁰ F)ˣ)
    (x : J.val) (y : J⁻¹.val) :
    algebraMap R F (unitPairCoefficient J x y)=(x : F)*(y : F) :=
  Classical.choose_spec ((mem_one_iff R⁰).mp (unit_pair_mul_mem_one J x y))

omit [IsDomain R] in
/-- At EACH actual maximal ideal some product in the inverse pair avoids it. -/
theorem exists_unit_pair_not_mem_maximal (J : (FractionalIdeal R⁰ F)ˣ)
    (m : MaximalSpectrum R) :
    ∃ (x : J.val) (y : J⁻¹.val), unitPairCoefficient J x y ∉ m.asIdeal := by
  classical
  by_contra h
  push Not at h
  have hle : J.val*J⁻¹.val ≤ (m.asIdeal : FractionalIdeal R⁰ F) := by
    apply FractionalIdeal.mul_le.mpr
    intro x hx y hy
    exact (mem_coeIdeal R⁰).mpr
      ⟨unitPairCoefficient J ⟨x,hx⟩ ⟨y,hy⟩,h ⟨x,hx⟩ ⟨y,hy⟩,
        unitPairCoefficient_spec J ⟨x,hx⟩ ⟨y,hy⟩⟩
  have hJJ : J.val*J⁻¹.val=(1 : FractionalIdeal R⁰ F) := J.mul_inv
  rw [hJJ] at hle
  obtain ⟨r,hr,he⟩ := (mem_coeIdeal R⁰).mp (hle (one_mem_one (S := R⁰) (P := F)))
  have hr1 : r=1 := (IsFractionRing.injective R F) (he.trans (map_one _).symm)
  exact m.isMaximal.isPrime.one_notMem (hr1 ▸ hr)

omit [IsDomain R] in
/-- Finite CRT chooses one actual inverse pair with product one modulo C.
The empty set of maximal ideals is allowed, including C=top. -/
theorem exists_unit_pair_mod_conductor (J : (FractionalIdeal R⁰ F)ˣ) (C : Ideal R)
    [Finite {m : MaximalSpectrum R // C ≤ m.asIdeal}] :
    ∃ (x : J.val) (y : J⁻¹.val), (x : F)*(y : F)-1 ∈ (C : FractionalIdeal R⁰ F) := by
  classical
  let ι := {m : MaximalSpectrum R // C ≤ m.asIdeal}
  letI : Fintype ι := Fintype.ofFinite ι
  choose u v huv using (fun i : ι => exists_unit_pair_not_mem_maximal J i.val)
  have hcop : Pairwise (fun (i j : ι) => IsCoprime i.val.asIdeal j.val.asIdeal) := by
    intro i j hij
    apply MaximalSpectrum.isCoprime_of_ne
    exact fun h => hij (Subtype.ext h)
  have hcrt (i : ι) : ∃ e : R, ∀ j : ι,
      Ideal.Quotient.mk j.val.asIdeal e = if i=j then 1 else 0 :=
    Ideal.pi_quotient_surjective hcop (fun j => if i=j then 1 else 0)
  choose e he using hcrt
  let x : F := ∑ i : ι, algebraMap R F (e i)*(u i : F)
  let y : F := ∑ i : ι, algebraMap R F (e i)*(v i : F)
  have hx : x ∈ J.val := by
    exact (J.val : Submodule R F).sum_mem fun i _ => by
      simpa only [Algebra.smul_def] using (J.val : Submodule R F).smul_mem (e i) (u i).prop
  have hy : y ∈ J⁻¹.val := by
    exact (J⁻¹.val : Submodule R F).sum_mem fun i _ => by
      simpa only [Algebra.smul_def] using (J⁻¹.val : Submodule R F).smul_mem (e i) (v i).prop
  let r : R := ∑ i : ι, ∑ j : ι, e i*e j*unitPairCoefficient J (u i) (v j)
  have hr : algebraMap R F r=x*y := by
    simp only [r,x,y,map_sum,map_mul,unitPairCoefficient_spec,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have havoid (m : ι) : r ∉ m.val.asIdeal := by
    have hres : Ideal.Quotient.mk m.val.asIdeal r =
        Ideal.Quotient.mk m.val.asIdeal (unitPairCoefficient J (u m) (v m)) := by
      let f := Ideal.Quotient.mk m.val.asIdeal
      change f r=f (unitPairCoefficient J (u m) (v m))
      simp only [r,map_sum,map_mul]
      have hi (i : ι) :
          (∑ j : ι, f (e i)*f (e j)*f (unitPairCoefficient J (u i) (v j))) =
            f (e i)*f (unitPairCoefficient J (u i) (v m)) := by
        rw [Finset.sum_eq_single m]
        · rw [show f (e m)=1 from by simpa only [if_pos rfl] using he m m,mul_one]
        · intro j _ hj
          rw [show f (e j)=0 from by simpa only [if_neg hj] using he j m,mul_zero,zero_mul]
        · simp
      simp_rw [hi]
      rw [Finset.sum_eq_single m]
      · rw [show f (e m)=1 from by simpa only [if_pos rfl] using he m m,one_mul]
      · intro i _ hi
        rw [show f (e i)=0 from by simpa only [if_neg hi] using he i m,zero_mul]
      · simp
    intro hm
    have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
    rw [hres] at hz
    exact huv m (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have htop : C ⊔ Ideal.span {r}=⊤ := by
    by_contra h
    obtain ⟨M,hM,hle⟩ := Ideal.exists_le_maximal _ h
    let m : ι := ⟨⟨M,hM⟩,le_sup_left.trans hle⟩
    exact havoid m ((le_sup_right.trans hle) (Ideal.subset_span (Set.mem_singleton r)))
  have hone : (1 : R) ∈ C ⊔ Ideal.span {r} := by rw [htop]; trivial
  obtain ⟨c,hc,z,hz,hsum⟩ := Submodule.mem_sup.mp hone
  obtain ⟨s,hs⟩ := Ideal.mem_span_singleton.mp hz
  have hrs : r*s-1 ∈ C := by
    have hh : r*s-1 = -c := by rw [hs] at hsum; linear_combination hsum
    rw [hh]
    exact C.neg_mem hc
  refine ⟨⟨x,hx⟩,⟨algebraMap R F s*y,?_⟩,?_⟩
  · simpa only [Algebra.smul_def] using (J⁻¹.val : Submodule R F).smul_mem s hy
  · have hmap : algebraMap R F (r*s-1) ∈ (C : FractionalIdeal R⁰ F) :=
      mem_coeIdeal_of_mem R⁰ hrs
    rw [map_sub,map_mul,map_one,hr] at hmap
    convert hmap using 1
    ring


omit [IsDomain R] in
/-- A reciprocal conductor pair recovers the literal line, provided the
actual ideal and inverse lie in the given overorder and contain C. -/
theorem unit_eq_conductorLine_of_pair (J : (FractionalIdeal R⁰ F)ˣ)
    (T C : FractionalIdeal R⁰ F) (hTC : T*C=C)
    (hC : C ≤ J.val) (hJ : J.val ≤ T)
    (x : J.val) (y : J⁻¹.val) (hxy : (x : F)*(y : F)-1 ∈ C) :
    J.val=conductorLine C (x : F) := by
  apply le_antisymm
  · intro z hz
    let r := unitPairCoefficient J ⟨z,hz⟩ y
    have hr : algebraMap R F r=z*(y : F) := unitPairCoefficient_spec J ⟨z,hz⟩ y
    have hm : ((x : F)*(y : F)-1)*z ∈ C := by
      rw [← hTC,mul_comm T C]
      exact mul_mem_mul hxy (hJ hz)
    have hd : z-algebraMap R F r*(x : F) ∈ C := by
      have hh := (C : Submodule R F).neg_mem hm
      convert hh using 1
      rw [hr]
      ring
    change z ∈ spanSingleton R⁰ (x : F)+C
    apply (mem_add _ _ _).mpr
    refine ⟨algebraMap R F r*(x : F),?_,z-algebraMap R F r*(x : F),hd,?_⟩
    · exact (mem_spanSingleton _).mpr ⟨r,Algebra.smul_def ..⟩
    · ring
  · exact sup_le (spanSingleton_le_iff_mem.mpr x.prop) hC

end FractionalIdeal

namespace BinaryNormIdeal

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- The actual positive order index belongs to the original conductor. -/
theorem index_mem_originalConductorIdeal (hD : b^2-4*a*c<0) :
    (orderIndex a b c : CoefficientOrder a b c) ∈ originalConductorIdeal a b c := by
  change orderToRingOfIntegers a b c (orderIndex a b c : CoefficientOrder a b c) ∈
    orderConductor a b c
  rw [map_natCast,orderConductor_eq_span_index a b c hD]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Only finitely many actual maximal ideals contain the conductor. Its
positive integer index supplies finiteness, including index one. -/
theorem finite_maximalSpectrum_above_originalConductor (hD : b^2-4*a*c<0) :
    Finite {m : MaximalSpectrum (CoefficientOrder a b c) //
      originalConductorIdeal a b c ≤ m.asIdeal} := by
  classical
  let d : CoefficientOrder a b c := orderIndex a b c
  have hd0 : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast (ne_of_gt (orderIndex_pos a b c hD))
  letI : Ring.HasFiniteQuotients (CoefficientOrder a b c) :=
    Ring.HasFiniteQuotients.of_module_finite ℤ (CoefficientOrder a b c)
  letI : Fintype {P : Ideal (CoefficientOrder a b c) // d ∈ P} :=
    (Ring.HasFiniteQuotients.finite_setOf_mem d hd0).fintype
  apply Finite.of_injective (fun m =>
    (⟨m.val.asIdeal,m.prop (index_mem_originalConductorIdeal a b c hD)⟩ :
      {P : Ideal (CoefficientOrder a b c) // d ∈ P}))
  intro m n h
  apply Subtype.ext
  apply MaximalSpectrum.ext
  exact congrArg Subtype.val h

/-- A normalized actual ideal is a literal connecting ideal of an actual
maximal-order residue unit. This supplies the missing generator natively. -/
theorem exists_residueConnectingIdealUnit_of_extension_one (hD : b^2-4*a*c<0)
    (J : (FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))ˣ)
    (hJ : orderIdealExtension a b c hD J=1) :
    ∃ q : ConductorResidueUnits a b c,
      (residueConnectingIdealUnit a b c hD q :
        FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))=J.val := by
  letI := finite_maximalSpectrum_above_originalConductor a b c hD
  obtain ⟨x,y,hxy⟩ := FractionalIdeal.exists_unit_pair_mod_conductor J (originalConductorIdeal a b c)
  obtain ⟨hC,hJT,hprod⟩ := conductor_bounds_of_extension_one a b c hD J.val hJ
  obtain ⟨_,hJinvT,_⟩ := conductor_bounds_of_extension_one a b c hD J⁻¹.val
    (orderIdealExtension_inv_eq_one a b c hD J hJ)
  obtain ⟨u,hu⟩ := (mem_maximalOrderFractionalIdeal a b c hD (x : FractionRing _)).mp (hJT x.prop)
  obtain ⟨v,hv⟩ := (mem_maximalOrderFractionalIdeal a b c hD (y : FractionRing _)).mp (hJinvT y.prop)
  have hxyC : (x : FractionRing (CoefficientOrder a b c))*(y : FractionRing _)-1 ∈
      conductorFractionalIdeal a b c hD := by
    obtain ⟨r,hr,he⟩ := (FractionalIdeal.mem_coeIdeal _).mp hxy
    change orderToRingOfIntegers a b c r ∈ orderConductor a b c at hr
    have hh := (mem_conductorFractionalIdeal_iff a b c hD (orderToRingOfIntegers a b c r)).mpr hr
    simpa only [orderToRingOfIntegers_coe,he] using hh
  have huv : u*v-1 ∈ orderConductor a b c := by
    apply (mem_conductorFractionalIdeal_iff a b c hD (u*v-1)).mp
    simpa only [map_sub,map_mul,map_one,hu,hv] using hxyC
  let q : ConductorResidueUnits a b c :=
    ⟨Ideal.Quotient.mk (orderConductor a b c) u,
      Ideal.Quotient.mk (orderConductor a b c) v,
      by rw [← map_mul]; exact (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr huv,
      by rw [← map_mul,mul_comm v u]; exact (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr huv⟩
  refine ⟨q,?_⟩
  change conductorConnectingIdeal a b c hD (conductorResidueLift a b c q)=J.val
  have heq : conductorConnectingIdeal a b c hD (conductorResidueLift a b c q)=
      conductorConnectingIdeal a b c hD u := by
    apply conductorConnectingIdeal_eq_of_sub_mem
    apply Ideal.Quotient.eq.mp
    rw [mk_conductorResidueLift]
  rw [heq]
  have hline := FractionalIdeal.unit_eq_conductorLine_of_pair J
    (maximalOrderFractionalIdeal a b c hD) (conductorFractionalIdeal a b c hD)
    (maximalOrderFractionalIdeal_mul_conductor a b c hD) hC hJT x y hxyC
  change FractionalIdeal.conductorLine (conductorFractionalIdeal a b c hD) (algebraMap _ _ u)=J.val
  rw [hu]
  exact hline.symm

/-- The Picard extension kernel is exactly the image of the connecting map.
Both directions use the `ClassGroup` of the original arbitrary order. -/
theorem orderPicardExtension_ker (hD : b^2-4*a*c<0) :
    (orderPicardExtension a b c hD).ker=
      (conductorResidueQuotientClassHom a b c hD).range := by
  apply le_antisymm _ (conductorResidueQuotientClassHom_range_le_extension_ker a b c hD)
  intro d hd
  obtain ⟨J,hclass,hJ⟩ := exists_unit_representative_extension_one a b c hD d hd
  obtain ⟨q,hq⟩ := exists_residueConnectingIdealUnit_of_extension_one a b c hD J hJ
  refine ⟨QuotientGroup.mk q,?_⟩
  rw [conductorResidueQuotientClassHom_mk]
  change ClassGroup.mk _ (residueConnectingIdealUnit a b c hD q)=d
  rw [show residueConnectingIdealUnit a b c hD q=J from Units.ext hq]
  exact hclass


/-- The exact quotient is the actual extension image. Surjectivity onto
the whole maximal-order class group is not used. -/
noncomputable def conductorPicardQuotientEquivExtensionRange (hD : b^2-4*a*c<0) :
    ClassGroup (CoefficientOrder a b c) ⧸ (conductorResidueQuotientClassHom a b c hD).range ≃*
      (orderPicardExtension a b c hD).range := by
  rw [← orderPicardExtension_ker a b c hD]
  exact QuotientGroup.quotientKerEquivRange (orderPicardExtension a b c hD)

/-- Class-number correction in terms of the extension image.
Replacing that image by the whole maximal class group requires surjectivity. -/
theorem card_classGroup_mul_unitIndex_eq_extensionImage_mul_residueQuotient (hD : b^2-4*a*c<0) :
    Nat.card (ClassGroup (CoefficientOrder a b c))*orderUnitIndex a b c =
      Nat.card (orderPicardExtension a b c hD).range *
        Nat.card (ConductorResidueUnitQuotient a b c) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (orderPicardExtension a b c hD).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
    (orderPicardExtension a b c hD )).toEquiv,orderPicardExtension_ker a b c hD] at h
  rw [h,card_conductorResidueQuotient_eq_image_mul_unitIndex a b c hD]
  ring

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

/-- Complete exactness at the original order class group. -/
theorem binaryOrderPicardExtension_ker (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryOrderPicardExtension.ker=K.binaryConductorResidueQuotientClassHom.range := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact BinaryNormIdeal.orderPicardExtension_ker _ _ _ K.binaryDiscriminantOrder_discriminant_neg

/-- The exact count in terms of the maximal-order extension image. -/
theorem card_binaryClassGroup_mul_unitIndex_eq_extensionImage_mul_residueQuotient (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    Nat.card (ClassGroup (BinaryNormIdeal.DiscriminantOrder K.binaryPrimitiveDiscriminant))*
      K.binaryOrderUnitIndex = Nat.card K.binaryOrderPicardExtension.range *
        Nat.card (BinaryNormIdeal.ConductorResidueUnitQuotient 1 (K.binaryPrimitiveDiscriminant%2)
          (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact BinaryNormIdeal.card_classGroup_mul_unitIndex_eq_extensionImage_mul_residueQuotient _ _ _
    K.binaryDiscriminantOrder_discriminant_neg

end PositiveDefiniteIntegralLattice

#assert_standard_axioms FractionalIdeal.unit_pair_mul_mem_one
#assert_standard_axioms FractionalIdeal.unitPairCoefficient
#assert_standard_axioms FractionalIdeal.unitPairCoefficient_spec
#assert_standard_axioms FractionalIdeal.exists_unit_pair_not_mem_maximal
#assert_standard_axioms FractionalIdeal.exists_unit_pair_mod_conductor
#assert_standard_axioms FractionalIdeal.unit_eq_conductorLine_of_pair
#assert_standard_axioms BinaryNormIdeal.index_mem_originalConductorIdeal
#assert_standard_axioms BinaryNormIdeal.finite_maximalSpectrum_above_originalConductor
#assert_standard_axioms BinaryNormIdeal.exists_residueConnectingIdealUnit_of_extension_one
#assert_standard_axioms BinaryNormIdeal.orderPicardExtension_ker
#assert_standard_axioms BinaryNormIdeal.conductorPicardQuotientEquivExtensionRange
#assert_standard_axioms BinaryNormIdeal.card_classGroup_mul_unitIndex_eq_extensionImage_mul_residueQuotient
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryOrderPicardExtension_ker
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_binaryClassGroup_mul_unitIndex_eq_extensionImage_mul_residueQuotient

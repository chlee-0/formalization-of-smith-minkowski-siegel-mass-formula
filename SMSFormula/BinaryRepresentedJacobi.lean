import SMSFormula.BinaryNormCharacterPrimeSign

/-!
# Jacobi signs of literal represented binary values

Inert odd primes divide both coordinates. Strong descent on a positive
odd represented value handles nonprimitive vectors without assuming a
prime value or dividing by two in a residue ring.
-/

noncomputable section
namespace BinaryNormIdeal

/-- A negative prime sign forces divisibility of both original integer
coordinates of a represented value. -/
theorem inert_prime_dvd_binary_coordinates (a b c x y : ℤ)
    (p : ℕ) [Fact p.Prime] (hp : p≠2)
    (hj : jacobiSym (b^2-4*a*c) p=-1)
    (hQ : (p : ℤ)∣a*x^2+b*x*y+c*y^2) : (p : ℤ)∣x ∧ (p : ℤ)∣y := by
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hnotA : ¬(p : ℤ)∣a := by
    intro ha
    have he : b^2-(b^2-4*a*c)*(1 : ℤ)^2=4*a*c := by ring
    have hdiv : (p : ℤ)∣b^2-(b^2-4*a*c)*(1 : ℤ)^2 := by
      rw [he]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ha 4) c
    have hone := (jacobiSym.prime_dvd_of_eq_neg_one hj hdiv).2
    exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp (by exact_mod_cast hone))
  have hnorm : (2*a*x+b*y)^2-(b^2-4*a*c)*y^2=4*a*(a*x^2+b*x*y+c*y^2) := by ring
  have hd : (p : ℤ)∣(2*a*x+b*y)^2-(b^2-4*a*c)*y^2 := by
    rw [hnorm]
    exact dvd_mul_of_dvd_right hQ (4*a)
  obtain ⟨hu,hy⟩ := jacobiSym.prime_dvd_of_eq_neg_one hj hd
  have hx2 : (p : ℤ)∣2*a*x := by
    have h := dvd_sub hu (dvd_mul_of_dvd_right hy b)
    simpa only [add_sub_cancel_right] using h
  have hnot2 : ¬(p : ℤ)∣2 := by
    intro hd2
    have hn : p∣2 := by exact_mod_cast hd2
    rcases (Nat.dvd_prime Nat.prime_two).mp hn with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · exact hp h
  have hx : (p : ℤ)∣x := (hprime.dvd_mul.mp hx2).resolve_left (by
    intro h
    exact ((hprime.dvd_mul.mp h).resolve_left hnot2) |> hnotA)
  exact ⟨hx,hy⟩

/-- A positive odd value of any integral binary polynomial never has
negative Jacobi sign at its discriminant. No primitive-vector hypothesis. -/
theorem jacobi_discriminant_represented_ne_neg_one (a b c : ℤ) (N : ℕ)
    (hN : 0<N) (hodd : Odd N) (x y : ℤ)
    (hQ : a*x^2+b*x*y+c*y^2=(N : ℤ)) : jacobiSym (b^2-4*a*c) N≠-1 := by
  induction N using Nat.strong_induction_on generalizing x y with
  | h N ih =>
    intro hneg
    obtain ⟨p,hp,hpN,hpneg⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one hneg
    letI : Fact p.Prime := ⟨hp⟩
    have hp2 : p≠2 := by
      intro he
      subst p
      obtain ⟨t,ht⟩ := hodd
      obtain ⟨s,hs⟩ := hpN
      omega
    have hd : (p : ℤ)∣a*x^2+b*x*y+c*y^2 := by
      rw [hQ]
      exact_mod_cast hpN
    obtain ⟨hx,hy⟩ := inert_prime_dvd_binary_coordinates a b c x y p hp2 hpneg hd
    obtain ⟨u,rfl⟩ := hx
    obtain ⟨v,rfl⟩ := hy
    let q : ℤ := a*u^2+b*u*v+c*v^2
    have he : (N : ℤ)=(p : ℤ)^2*q := by dsimp [q]; nlinarith [hQ]
    have hppos : 0<(p : ℤ) := by exact_mod_cast hp.pos
    have hqpos : 0<q := by nlinarith [sq_pos_of_pos hppos]
    let m := q.toNat
    have hmcast : (m : ℤ)=q := Int.toNat_of_nonneg hqpos.le
    have hmpos : 0<m := by exact_mod_cast (hmcast ▸ hqpos)
    have hn : N=p^2*m := by
      have hz : (N : ℤ)=(p : ℤ)^2*(m : ℤ) := by rw [he,hmcast]
      exact_mod_cast hz
    have hmlt : m<N := by
      have hpge : (2 : ℤ)≤p := by exact_mod_cast hp.two_le
      have hm : (0 : ℤ)<m := by exact_mod_cast hmpos
      exact_mod_cast (show (m : ℤ)<N by rw [hn]; push_cast; nlinarith [sq_nonneg ((p : ℤ)-2)])
    have hmodd : Odd m := by
      obtain ⟨t,ht⟩ := hodd
      by_contra h
      have heven : Even m := Nat.not_odd_iff_even.mp h
      obtain ⟨s,hs⟩ := heven
      have hn2 : N=2*(p^2*s) := by rw [hn,hs]; ring
      omega
    have hj : jacobiSym (b^2-4*a*c) m=-1 := by
      rw [hn,jacobiSym.mul_right' _ (pow_ne_zero _ hp.ne_zero) hmpos.ne',
        jacobiSym.pow_right,hpneg] at hneg
      norm_num at hneg
      exact hneg
    exact ih m hmlt hmpos hmodd u v (by change q=_; exact hmcast.symm) hj

/-- Coprimality removes the remaining zero sign for a positive odd
represented value. No primality or primitive-vector certificate occurs. -/
theorem jacobi_discriminant_represented_eq_one (a b c : ℤ) (N : ℕ)
    (hN : 0<N) (hodd : Odd N) (x y : ℤ)
    (hQ : a*x^2+b*x*y+c*y^2=(N : ℤ)) (hcop : (b^2-4*a*c).gcd N=1) :
    jacobiSym (b^2-4*a*c) N=1 := by
  rcases jacobiSym.trichotomy (b^2-4*a*c) N with h | h | h
  · exact False.elim ((jacobiSym.ne_zero hcop) h)
  · exact h
  · exact False.elim ((jacobi_discriminant_represented_ne_neg_one a b c N hN hodd x y hQ) h)

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

/-- One positive global primitive-polynomial value avoids any finite set
of primes. The vector need not be primitive and the value need not be prime. -/
theorem exists_pos_binaryPrimitivePolynomial_avoiding (L : PositiveDefiniteIntegralLattice 2)
    (S : Finset {p : ℕ // p.Prime}) :
    ∃ v : Fin 2 → ℤ, 0<L.binaryPrimitivePolynomial v ∧
      ∀ p∈S, ¬(p.val : ℤ)∣L.binaryPrimitivePolynomial v := by
  classical
  let w (p : ↥S) : Fin 2 → ℤ :=
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    Classical.choose (L.exists_prime_not_dvd_binaryPrimitivePolynomial p.val.val)
  have hw (p : ↥S) : ¬(p.val.val : ℤ)∣L.binaryPrimitivePolynomial (w p) := by
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    exact Classical.choose_spec (L.exists_prime_not_dvd_binaryPrimitivePolynomial p.val.val)
  let m (p : ↥S) := p.val.val
  let r (i : Fin 2) (p : ↥S) : ℕ :=
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    ((w p i : ℤ) : ZMod p.val.val).val
  have hnz (p : ↥S) (_ : p∈Finset.univ) : m p≠0 := p.val.prop.ne_zero
  have hcop : Set.Pairwise (↑(Finset.univ : Finset ↥S)) (Function.onFun Nat.Coprime m) := by
    intro p _ q _ hpq
    have hne : p.val.val≠q.val.val := by
      intro h
      exact hpq (Subtype.ext (Subtype.ext h))
    simpa only [pow_one] using Nat.coprime_pow_primes 1 1 p.val.prop q.val.prop hne
  let z (i : Fin 2) := Nat.chineseRemainderOfFinset (r i) m Finset.univ hnz hcop
  let M : ℕ := ∏ p∈S, p.val
  have hM : 0<M := Finset.prod_pos (by intro p _; exact p.prop.pos)
  let v : Fin 2 → ℤ := fun i => (z i).val + if i=0 then (M : ℤ) else 0
  have hvres (i : Fin 2) (p : ↥S) :
      letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
      (v i : ZMod p.val.val)=(w p i : ZMod p.val.val) := by
    letI : Fact p.val.val.Prime := ⟨p.val.prop⟩
    have hd : p.val.val∣M := Finset.dvd_prod_of_mem _ p.prop
    have hz : ((z i).val : ZMod p.val.val)=(r i p : ZMod p.val.val) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((z i).prop p (Finset.mem_univ p))
    have he : (v i : ZMod p.val.val)=((z i).val : ZMod p.val.val) := by
      dsimp [v]
      by_cases hi : i=0 <;> simp [hi,(ZMod.natCast_eq_zero_iff M p.val.val).mpr hd]
    exact he.trans (hz.trans (ZMod.natCast_zmod_val _))
  have hv : v≠0 := by
    intro h
    have hz := congrFun h 0
    have hp : (0 : ℤ)<M := by exact_mod_cast hM
    dsimp [v] at hz
    omega
  refine ⟨v,L.binaryPrimitivePolynomial_posDef v hv,?_⟩
  intro p hp hd
  letI : Fact p.val.Prime := ⟨p.prop⟩
  have he : (L.binaryPrimitivePolynomial v : ZMod p.val)=
      (L.binaryPrimitivePolynomial (w ⟨p,hp⟩) : ZMod p.val) := by
    rw [← L.binaryPrimitivePolynomialOver_intCast,← L.binaryPrimitivePolynomialOver_intCast]
    congr 1
    funext i
    exact hvres i ⟨p,hp⟩
  apply hw ⟨p,hp⟩
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    (he.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd))

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.inert_prime_dvd_binary_coordinates
#assert_standard_axioms BinaryNormIdeal.jacobi_discriminant_represented_ne_neg_one
#assert_standard_axioms BinaryNormIdeal.jacobi_discriminant_represented_eq_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_pos_binaryPrimitivePolynomial_avoiding

import SMSFormula.RationalCliffordSpinCandidateLatticeProperDomainSelectorSourceMap
import SMSFormula.RationalCliffordGeneralSpinVerticalSpecialOrthogonalProjection

/-!
# The finite proper double coset of a full-adelic `SO` quotient point

The proper-piece label can be read before choosing the proper-domain
normalization: take the finite component of the full adelic point and pass to
the rational-left, integral-right double quotient.  Rational left
translation does not change this class, so the map descends to the
`SO(Q)\SO(A)` carrier.

The descended class is exactly the piece label selected after proper-domain
normalization.  Consequently right multiplication by an element of the
finite lattice stabilizer preserves the proper-piece coordinate.  So the
remaining normalization calculation concerns the refined selector
orbit alone.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

/-- The finite proper double coset of a concrete full-adelic `SO` point. -/
noncomputable def concreteFullAdelicSpecialOrthogonalToProperDoubleCoset
    (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteFullAdelicSpecialOrthogonalGroup →
      L.ConcreteProperRationalDoubleCosetSet := fun g =>
  Quot.mk (leftRightDoubleCosetSetoid
      L.rationalSpecialOrthogonalDiagonalSubgroup
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup)
    (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2

/-- Rational left translation does not change the finite proper double
coset. -/
theorem concreteFullAdelicSpecialOrthogonalToProperDoubleCoset_gamma_mul
    (L : PositiveDefiniteIntegralLattice n)
    (gamma : L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.concreteFullAdelicSpecialOrthogonalToProperDoubleCoset
        ((gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup) * g) =
      L.concreteFullAdelicSpecialOrthogonalToProperDoubleCoset g := by
  rcases gamma.2 with ⟨q, hq⟩
  apply (leftRightDoubleCoset_mk_eq_iff
    L.rationalSpecialOrthogonalDiagonalSubgroup
    L.finiteSpecialOrthogonalLatticeStabilizerSubgroup _ _).mpr
  let gammaFinite : L.rationalSpecialOrthogonalDiagonalSubgroup :=
    ⟨L.rationalSpecialOrthogonalDiagonalHom q, ⟨q, rfl⟩⟩
  refine ⟨gammaFinite⁻¹, 1, ?_⟩
  have hsplit :=
    L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.map_mul
      (gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup) g
  have hfinite := congrArg Prod.snd hsplit
  change
    (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
      ((gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup) * g)).2 =
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
          (gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup)).2 *
        (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2 at hfinite
  have hgamma :
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
        (gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup)).2 =
          L.rationalSpecialOrthogonalDiagonalHom q := by
    rw [← hq]
    exact
      L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv_rationalDiagonal_finite q
  change
    (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2 =
      (gammaFinite⁻¹ : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) *
        (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv
          ((gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup) * g)).2 * 1
  rw [mul_one, hfinite, hgamma]
  change _ = (L.rationalSpecialOrthogonalDiagonalHom q)⁻¹ *
    (L.rationalSpecialOrthogonalDiagonalHom q * _)
  simp

/-- The finite proper double-coset map descends to the literal rational
full-adelic left quotient. -/
noncomputable def concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDoubleCoset
    (L : PositiveDefiniteIntegralLattice n) :
    L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient →
      L.ConcreteProperRationalDoubleCosetSet :=
  Quot.lift L.concreteFullAdelicSpecialOrthogonalToProperDoubleCoset (by
    intro x y hxy
    rcases hxy with ⟨gamma, rfl⟩
    exact
      (L.concreteFullAdelicSpecialOrthogonalToProperDoubleCoset_gamma_mul gamma x).symm)

@[simp]
theorem concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDoubleCoset_mk
    (L : PositiveDefiniteIntegralLattice n)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDoubleCoset
        (L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap g) =
      L.concreteFullAdelicSpecialOrthogonalToProperDoubleCoset g :=
  rfl

/-- The intrinsic finite double coset is exactly the proper-domain piece
label chosen after normalization. -/
theorem concreteFullAdelicProperDomainPieceLabel_normalization
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.concreteFullAdelicProperDomainPieceLabel
        (L.concreteFullAdelicProperNormalization g) =
      L.concreteFullAdelicSpecialOrthogonalToProperDoubleCoset g := by
  let z := L.concreteFullAdelicProperNormalization g
  let C := L.concreteFullAdelicProperDomainPieceLabel z
  have hnorm :
      L.concreteFullAdelicSpecialOrthogonalToProperDoubleCoset z.1 =
        L.concreteFullAdelicSpecialOrthogonalToProperDoubleCoset g := by
    exact L.concreteFullAdelicSpecialOrthogonalToProperDoubleCoset_gamma_mul
      (L.concreteFullAdelicProperNormalizerDiagonal g) g
  rw [← hnorm]
  change C = L.concreteFullAdelicSpecialOrthogonalToProperDoubleCoset z.1
  rw [← Quot.out_eq C]
  apply Quotient.sound
  refine ⟨1, L.concreteFullAdelicProperDomainSelectorElement z, ?_⟩
  change
    (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv z.1).2 =
      (1 : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) * Quot.out C *
        (L.concreteFullAdelicProperDomainSelectorElement z).1
  simpa using congrArg
    (fun x => (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv x).2)
    (L.concreteFullAdelicProperDomainSelectorElement_factor z)

/-- On the actual rational quotient, the intrinsic finite double coset is
the piece label of its proper-domain representative. -/
theorem concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDoubleCoset_eq_pieceLabel
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (q : L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient) :
    L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDoubleCoset q =
      L.concreteFullAdelicProperDomainPieceLabel
        (L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDomain q) := by
  induction q using Quot.inductionOn with
  | _ g =>
    exact (L.concreteFullAdelicProperDomainPieceLabel_normalization g).symm

/-- Right multiplication on the concrete lattice realization of the
rational full-adelic left quotient. -/
noncomputable def concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul
    (L : PositiveDefiniteIntegralLattice n)
    (x : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient →
      L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient :=
  Quot.lift
    (fun g => L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap (g * x)) (by
      intro g h hgh
      rcases hgh with ⟨gamma, rfl⟩
      change L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap (g * x) =
        L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap
          (((gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup) * g) * x)
      rw [mul_assoc]
      exact (leftCosetMap_gamma_mul
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup gamma (g * x)).symm)

@[simp]
theorem concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul_mk
    (L : PositiveDefiniteIntegralLattice n)
    (x g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul x
        (L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap g) =
      L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap (g * x) :=
  rfl

/-- Right multiplication by a full-adelic point with integral finite
component preserves the intrinsic proper-piece label. -/
theorem concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDoubleCoset_rightMul_stabilizer
    (L : PositiveDefiniteIntegralLattice n)
    (q : L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient)
    (x : L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (hx :
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv x).2 ∈
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
    L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDoubleCoset
        (L.concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul x q) =
      L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDoubleCoset q := by
  induction q using Quot.inductionOn with
  | _ g =>
    apply (leftRightDoubleCoset_mk_eq_iff
      L.rationalSpecialOrthogonalDiagonalSubgroup
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup _ _).mpr
    let h : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup :=
      ⟨(L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv x).2, hx⟩
    refine ⟨1, h⁻¹, ?_⟩
    have hfinite :
        (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv (g * x)).2 =
          (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2 *
            (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv x).2 := by
      exact congrArg Prod.snd
        (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv.map_mul g x)
    change
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2 =
        (1 : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) *
          (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv (g * x)).2 *
            (h⁻¹ : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    rw [one_mul, hfinite]
    change _ = (_ * (h : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)) *
      (h : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)⁻¹
    simp

/-- Proper-domain normalization therefore preserves the proper-piece label
under every compact-open right translation. -/
theorem concreteFullAdelicProperDomainPieceLabel_rightMul_stabilizer
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (q : L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient)
    (x : L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (hx :
      (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv x).2 ∈
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
    L.concreteFullAdelicProperDomainPieceLabel
        (L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDomain
          (L.concreteFullAdelicSpecialOrthogonalLeftQuotientRightMul x q)) =
      L.concreteFullAdelicProperDomainPieceLabel
        (L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDomain q) := by
  rw [← L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDoubleCoset_eq_pieceLabel,
    ← L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDoubleCoset_eq_pieceLabel]
  exact
    L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDoubleCoset_rightMul_stabilizer
      q x hx

end PositiveDefiniteIntegralLattice

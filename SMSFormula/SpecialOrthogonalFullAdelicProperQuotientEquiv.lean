import SMSFormula.SpecialOrthogonalFullAdelicProperFundamentalDomain
import SMSFormula.SpecialOrthogonalConcreteRationalQuotientCarrier

/-!
# The proper fundamental domain as the concrete `SO` quotient carrier

The unique rational diagonal translate into the completed proper fundamental
domain defines a normalization map.  It is invariant under rational left
translation and therefore identifies the concrete rational adelic
`SO` quotient with the subtype of the proper domain.  This is a carrier
equivalence only; measurability of the normalization is treated
separately.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

/-- The unique rational diagonal element moving an adelic `SO` point into
the proper fundamental domain. -/
noncomputable def concreteFullAdelicProperNormalizerDiagonal
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup :=
  Classical.choose
    (L.concreteFullAdelicProperTransversal_existsUnique_diagonal g)

/-- The chosen normalizing diagonal has the required proper-domain
membership. -/
theorem concreteFullAdelicProperNormalizerDiagonal_spec
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    ((L.concreteFullAdelicProperNormalizerDiagonal g :
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup) :
      L.ConcreteFullAdelicSpecialOrthogonalGroup) * g ∈
        L.concreteFullAdelicProperTransversal :=
  (Classical.choose_spec
    (L.concreteFullAdelicProperTransversal_existsUnique_diagonal g)).1

/-- The normalized proper-domain representative of an adelic `SO` point. -/
noncomputable def concreteFullAdelicProperNormalization
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    {z : L.ConcreteFullAdelicSpecialOrthogonalGroup //
      z ∈ L.concreteFullAdelicProperTransversal} :=
  ⟨(L.concreteFullAdelicProperNormalizerDiagonal g :
      L.ConcreteFullAdelicSpecialOrthogonalGroup) * g,
    L.concreteFullAdelicProperNormalizerDiagonal_spec g⟩

/-- Proper normalization is unchanged by rational left translation. -/
theorem concreteFullAdelicProperNormalization_gamma_mul
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (gamma : L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup)
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.concreteFullAdelicProperNormalization
        ((gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup) * g) =
      L.concreteFullAdelicProperNormalization g := by
  let delta := L.concreteFullAdelicProperNormalizerDiagonal
    ((gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup) * g)
  let epsilon := L.concreteFullAdelicProperNormalizerDiagonal g
  have hdelta :
      (((delta * gamma :
          L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup) :
        L.ConcreteFullAdelicSpecialOrthogonalGroup) * g) ∈
          L.concreteFullAdelicProperTransversal := by
    simpa [delta, mul_assoc] using
      L.concreteFullAdelicProperNormalizerDiagonal_spec
        ((gamma : L.ConcreteFullAdelicSpecialOrthogonalGroup) * g)
  have hepsilon :
      ((epsilon : L.ConcreteFullAdelicSpecialOrthogonalGroup) * g) ∈
        L.concreteFullAdelicProperTransversal :=
    L.concreteFullAdelicProperNormalizerDiagonal_spec g
  have heq : delta * gamma = epsilon :=
    (Classical.choose_spec
      (L.concreteFullAdelicProperTransversal_existsUnique_diagonal g)).2
      (delta * gamma) hdelta
  dsimp only [delta, epsilon] at heq
  apply Subtype.ext
  simp only [concreteFullAdelicProperNormalization]
  rw [← mul_assoc, ← Subgroup.coe_mul, heq]

/-- A point already in the proper domain normalizes to itself. -/
theorem concreteFullAdelicProperNormalization_eq_self
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (hg : g ∈ L.concreteFullAdelicProperTransversal) :
    L.concreteFullAdelicProperNormalization g = ⟨g, hg⟩ := by
  have heq : L.concreteFullAdelicProperNormalizerDiagonal g = 1 :=
    ((Classical.choose_spec
      (L.concreteFullAdelicProperTransversal_existsUnique_diagonal g)).2
      1 (by simpa using hg)).symm
  apply Subtype.ext
  change (L.concreteFullAdelicProperNormalizerDiagonal g :
      L.ConcreteFullAdelicSpecialOrthogonalGroup) * g = g
  rw [heq]
  simp

/-- Normalize a concrete rational adelic `SO` left coset into its unique
proper-domain representative. -/
noncomputable def concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDomain
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient →
      {z : L.ConcreteFullAdelicSpecialOrthogonalGroup //
        z ∈ L.concreteFullAdelicProperTransversal} :=
  Quot.lift L.concreteFullAdelicProperNormalization (by
    intro x y hxy
    rcases hxy with ⟨gamma, rfl⟩
    exact (L.concreteFullAdelicProperNormalization_gamma_mul gamma x).symm)

@[simp]
theorem concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDomain_mk
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup) :
    L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDomain
        (L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap g) =
      L.concreteFullAdelicProperNormalization g :=
  rfl

/-- The concrete rational adelic `SO` quotient is exactly the proper
fundamental-domain subtype. -/
noncomputable def concreteFullAdelicSpecialOrthogonalLeftQuotientProperDomainEquiv
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] :
    L.ConcreteFullAdelicSpecialOrthogonalLeftQuotient ≃
      {z : L.ConcreteFullAdelicSpecialOrthogonalGroup //
        z ∈ L.concreteFullAdelicProperTransversal} where
  toFun := L.concreteFullAdelicSpecialOrthogonalLeftQuotientToProperDomain
  invFun := fun z => L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap z.1
  left_inv := by
    intro C
    induction C using Quot.inductionOn with
    | _ g =>
      change L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap
          (L.concreteFullAdelicProperNormalization g).1 =
        L.concreteFullAdelicSpecialOrthogonalLeftQuotientMap g
      exact leftCosetMap_gamma_mul
        L.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
        (L.concreteFullAdelicProperNormalizerDiagonal g) g
  right_inv := by
    intro z
    exact L.concreteFullAdelicProperNormalization_eq_self z.1 z.2

end PositiveDefiniteIntegralLattice

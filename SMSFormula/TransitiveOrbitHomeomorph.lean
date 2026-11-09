import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Homeomorph.Defs

/-!
# The homeomorphism upgrade

The route's first binding qualification on the native comparison is that a continuous bijection
onto the homogeneous space is not enough -- a homeomorphism is needed, and the recorded way to get
one is the open-orbit-map Baire argument for a sigma-compact locally compact group.

That argument is already in Mathlib.  `isOpenMap_smul_of_sigmaCompact` states exactly it: for a
sigma-compact topological group acting continuously and pretransitively on a Baire `T2` space, the
orbit map `g |-> g . x` is an open map, proved by the Baire argument the route describes.  So this
qualification is not an item to build; it is an item to use.

What is added here is the upgrade in the form the comparison needs.  If a continuous bijection
factors the orbit map -- `e (q g) = g . x` for a continuous surjection `q` onto its source -- then
`e` is open, hence a homeomorphism.  The factorisation is exactly how the identification of the
shell with `G/H_a` arises, so the continuous bijection the route already has becomes a
homeomorphism as soon as the four hypotheses are supplied.

Negative scope: the hypotheses are real and are not verified here for the adelic situation --
sigma-compactness of the acting group, the Baire and `T2` properties of the shell, continuity of the
action, and pretransitivity.  Transitivity in particular is a separate closed input of the route and
is not reproved.  Nothing here constructs the shell, the stabilizer, or any measure, and a
homeomorphism is still not a measure comparison: the route's remaining qualifications on the native
comparison -- the nonabelian homogeneous-space uniqueness lemma, the positivity witness, and the
value-independence of the scalar -- are untouched.
-/

namespace SMSFormula.OrbitTopology

open MulAction

variable {G X : Type*} [TopologicalSpace G] [TopologicalSpace X] [Group G] [IsTopologicalGroup G]
  [MulAction G X] [SigmaCompactSpace G] [BaireSpace X] [T2Space X] [ContinuousSMul G X]
  [IsPretransitive G X]

/-- A map that factors the orbit map through a continuous surjection is open.  The orbit map itself
is open by mathlib's Baire argument, and a surjection lets the image of an open set be rewritten as
the orbit-map image of its preimage. -/
theorem isOpenMap_of_comp_orbit {Y : Type*} [TopologicalSpace Y] (x : X) {q : G → Y}
    (hq : Continuous q) (hqs : Function.Surjective q) {e : Y → X} (he : ∀ g, e (q g) = g • x) :
    IsOpenMap e := by
  intro U hU
  have hfun : (fun g : G ↦ g • x) = e ∘ q := funext fun g ↦ (he g).symm
  have himg : e '' U = (fun g ↦ g • x) '' (q ⁻¹' U) := by
    rw [hfun, Set.image_comp, Set.image_preimage_eq U hqs]
  rw [himg]
  exact isOpenMap_smul_of_sigmaCompact x _ (hU.preimage hq)

/-- The upgrade: a continuous bijection factoring the orbit map is a homeomorphism.  This is the
route's first qualification on the native comparison, discharged. -/
def homeomorphOfFactorsOrbit {Y : Type*} [TopologicalSpace Y] (x : X) {q : G → Y}
    (hq : Continuous q) (hqs : Function.Surjective q) (e : Y ≃ X) (hc : Continuous e)
    (he : ∀ g, e (q g) = g • x) : Y ≃ₜ X :=
  e.toHomeomorphOfContinuousOpen hc (isOpenMap_of_comp_orbit x hq hqs he)

@[simp]
theorem homeomorphOfFactorsOrbit_apply {Y : Type*} [TopologicalSpace Y] (x : X) {q : G → Y}
    (hq : Continuous q) (hqs : Function.Surjective q) (e : Y ≃ X) (hc : Continuous e)
    (he : ∀ g, e (q g) = g • x) (y : Y) :
    homeomorphOfFactorsOrbit x hq hqs e hc he y = e y := rfl

end SMSFormula.OrbitTopology

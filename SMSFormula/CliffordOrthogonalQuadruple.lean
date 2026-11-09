import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

/-!
# Clifford normal forms for four pairwise orthogonal vectors

For pairwise orthogonal vectors `v₀, v₁, v₂, v₃` of a quadratic form `Q` over a commutative ring, write
`eᵢ = ι(vᵢ)`, `fᵢ = Q(vᵢ)`.  The generators anticommute and square to `fᵢ`; the volume element
`w = e₀e₁e₂e₃` satisfies
* `w² = f₀f₁f₂f₃` (`volume_mul_volume`),
* `eᵢ w = −w eᵢ` (`gen_mul_volume`),
* `reverse w = w`, `involute w = w`.
When `f₀f₁f₂f₃ = d²` with `d` a unit, `z = w/d` squares to `1`, so `p± = (1 ± z)/2` are orthogonal idempotents
(`idempotent_*`), exchanged by the generators (`gen_mul_idempotent`).  These identities hold in every base change,
so they apply verbatim to the commutative scalar-extension model of the Spin candidate points.
Nothing is chosen.
-/

noncomputable section

-- the Clifford normalizer uses one rewrite set for every monomial computation
set_option linter.unusedSimpArgs false

namespace CliffordAlgebra.OrthogonalQuadruple

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (Q : QuadraticForm R M)
variable (v : Fin 4 → M) (hv : ∀ i j, i ≠ j → Q.IsOrtho (v i) (v j))

/-- The Clifford generator `eᵢ = ι(vᵢ)`. -/
abbrev gen (i : Fin 4) : CliffordAlgebra Q := ι Q (v i)

local notation "𝔢" => gen Q v

include hv

theorem gen_swap {i j : Fin 4} (hij : i ≠ j) : 𝔢 j * 𝔢 i = -(𝔢 i * 𝔢 j) :=
  ι_mul_ι_comm_of_isOrtho (hv j i hij.symm)

theorem gen_swap_assoc {i j : Fin 4} (hij : i ≠ j) (y : CliffordAlgebra Q) :
    𝔢 j * (𝔢 i * y) = -(𝔢 i * (𝔢 j * y)) := by
  rw [← mul_assoc, gen_swap Q v hv hij, neg_mul, mul_assoc]

omit hv in
theorem gen_sq (i : Fin 4) : 𝔢 i * 𝔢 i = algebraMap R _ (Q (v i)) := ι_sq_scalar Q (v i)

omit hv in
theorem gen_sq_assoc (i : Fin 4) (y : CliffordAlgebra Q) : 𝔢 i * (𝔢 i * y) = Q (v i) • y := by
  rw [← mul_assoc, gen_sq, Algebra.smul_def]

/-- The normalizing rewrite set: adjacent inversions and squares. -/
theorem e10 : 𝔢 1 * 𝔢 0 = -(𝔢 0 * 𝔢 1) := gen_swap Q v hv (by decide)
theorem e20 : 𝔢 2 * 𝔢 0 = -(𝔢 0 * 𝔢 2) := gen_swap Q v hv (by decide)
theorem e30 : 𝔢 3 * 𝔢 0 = -(𝔢 0 * 𝔢 3) := gen_swap Q v hv (by decide)
theorem e21 : 𝔢 2 * 𝔢 1 = -(𝔢 1 * 𝔢 2) := gen_swap Q v hv (by decide)
theorem e31 : 𝔢 3 * 𝔢 1 = -(𝔢 1 * 𝔢 3) := gen_swap Q v hv (by decide)
theorem e32 : 𝔢 3 * 𝔢 2 = -(𝔢 2 * 𝔢 3) := gen_swap Q v hv (by decide)
theorem e10a (y : CliffordAlgebra Q) : 𝔢 1 * (𝔢 0 * y) = -(𝔢 0 * (𝔢 1 * y)) :=
  gen_swap_assoc Q v hv (by decide) y
theorem e20a (y : CliffordAlgebra Q) : 𝔢 2 * (𝔢 0 * y) = -(𝔢 0 * (𝔢 2 * y)) :=
  gen_swap_assoc Q v hv (by decide) y
theorem e30a (y : CliffordAlgebra Q) : 𝔢 3 * (𝔢 0 * y) = -(𝔢 0 * (𝔢 3 * y)) :=
  gen_swap_assoc Q v hv (by decide) y
theorem e21a (y : CliffordAlgebra Q) : 𝔢 2 * (𝔢 1 * y) = -(𝔢 1 * (𝔢 2 * y)) :=
  gen_swap_assoc Q v hv (by decide) y
theorem e31a (y : CliffordAlgebra Q) : 𝔢 3 * (𝔢 1 * y) = -(𝔢 1 * (𝔢 3 * y)) :=
  gen_swap_assoc Q v hv (by decide) y
theorem e32a (y : CliffordAlgebra Q) : 𝔢 3 * (𝔢 2 * y) = -(𝔢 2 * (𝔢 3 * y)) :=
  gen_swap_assoc Q v hv (by decide) y

omit hv in
/-- The volume element `w = e₀e₁e₂e₃`. -/
def volume : CliffordAlgebra Q := 𝔢 0 * (𝔢 1 * (𝔢 2 * 𝔢 3))

local notation "𝔴" => volume Q v

/-- `w² = f₀f₁f₂f₃`. -/
theorem volume_mul_volume :
    𝔴 * 𝔴 = algebraMap R _ (Q (v 0) * Q (v 1) * Q (v 2) * Q (v 3)) := by
  unfold volume
  simp only [mul_assoc, e10a Q v hv, e20a Q v hv, e30a Q v hv, e21a Q v hv, e31a Q v hv, e32a Q v hv,
    e10 Q v hv, e20 Q v hv, e21 Q v hv, e31 Q v hv, e32 Q v hv, neg_mul, mul_neg, neg_neg, gen_sq_assoc,
    gen_sq, mul_smul_comm, smul_neg, smul_smul]
  rw [Algebra.smul_def, ← map_mul]
  congr 1
  ring

/-- Every generator anticommutes with the volume element. -/
theorem gen_mul_volume (i : Fin 4) : 𝔢 i * 𝔴 = -(𝔴 * 𝔢 i) := by
  unfold volume
  fin_cases i <;>
  · simp only [mul_assoc, e10a Q v hv, e20a Q v hv, e30a Q v hv, e21a Q v hv, e31a Q v hv, e32a Q v hv,
      e10 Q v hv, e20 Q v hv, e30 Q v hv, e21 Q v hv, e31 Q v hv, e32 Q v hv, neg_mul, mul_neg, neg_neg,
      gen_sq_assoc, gen_sq, mul_smul_comm, smul_neg, smul_smul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    try simp only [mul_comm, Algebra.smul_def]

omit hv in
theorem involute_volume : involute 𝔴 = 𝔴 := by
  unfold volume
  simp only [map_mul, involute_ι, neg_mul, mul_neg, neg_neg]

theorem reverse_volume : reverse 𝔴 = 𝔴 := by
  unfold volume
  simp only [reverse.map_mul, reverse_ι]
  simp only [mul_assoc, e10a Q v hv, e20a Q v hv, e30a Q v hv, e21a Q v hv, e31a Q v hv, e32a Q v hv,
    e10 Q v hv, e20 Q v hv, e30 Q v hv, e21 Q v hv, e31 Q v hv, e32 Q v hv, neg_mul, mul_neg, neg_neg]

/-- Every vector of the span of the `vᵢ` anticommutes with the volume element. -/
theorem ι_mul_volume_of_mem_span {m : M} (hm : m ∈ Submodule.span R (Set.range v)) :
    ι Q m * 𝔴 = -(𝔴 * ι Q m) := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact gen_mul_volume Q v hv i
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, add_mul, mul_add, hx, hy, neg_add]
  | smul r x _ hx => simp only [map_smul, smul_mul_assoc, mul_smul_comm, hx, smul_neg]

/-- Every even element commutes with the volume element (when the `vᵢ` span `M`). -/
theorem even_mul_volume (hspan : ∀ m : M, m ∈ Submodule.span R (Set.range v)) {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 0) : x * 𝔴 = 𝔴 * x := by
  induction x, hx using even_induction with
  | algebraMap r => rw [Algebra.commutes]
  | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
  | ι_mul_ι_mul m₁ m₂ x _ hx =>
    have h1 := ι_mul_volume_of_mem_span Q v hv (hspan m₁)
    have h2 := ι_mul_volume_of_mem_span Q v hv (hspan m₂)
    calc ι Q m₁ * ι Q m₂ * x * 𝔴 = ι Q m₁ * (ι Q m₂ * 𝔴) * x := by
          rw [mul_assoc (ι Q m₁ * ι Q m₂), hx, ← mul_assoc, mul_assoc (ι Q m₁)]
      _ = -((ι Q m₁ * 𝔴) * ι Q m₂ * x) := by rw [h2]; simp only [mul_neg, neg_mul, mul_assoc]
      _ = 𝔴 * (ι Q m₁ * ι Q m₂ * x) := by rw [h1]; simp only [mul_neg, neg_mul, neg_neg, mul_assoc]

/-! ## The normalized volume element and the central idempotents -/

variable {d : R} (hd : Q (v 0) * Q (v 1) * Q (v 2) * Q (v 3) * (d * d) = 1)

omit hv in
/-- The normalized volume element `z = d · w` (with `d² f₀f₁f₂f₃ = 1`). -/
def normVolume (d : R) : CliffordAlgebra Q := d • 𝔴

local notation "𝔷" => normVolume Q v d

include hd in
theorem normVolume_mul_self : 𝔷 * 𝔷 = 1 := by
  unfold normVolume
  rw [smul_mul_smul_comm, volume_mul_volume Q v hv, Algebra.smul_def, ← map_mul, mul_comm, hd, map_one]

theorem gen_mul_normVolume (i : Fin 4) : 𝔢 i * 𝔷 = -(𝔷 * 𝔢 i) := by
  unfold normVolume
  rw [mul_smul_comm, gen_mul_volume Q v hv, smul_mul_assoc, smul_neg]

omit hv in
theorem involute_normVolume : involute 𝔷 = 𝔷 := by
  unfold normVolume
  rw [map_smul, involute_volume]

theorem reverse_normVolume : reverse 𝔷 = 𝔷 := by
  unfold normVolume
  rw [map_smul, reverse_volume Q v hv]

theorem even_mul_normVolume (hspan : ∀ m : M, m ∈ Submodule.span R (Set.range v)) {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 0) : x * 𝔷 = 𝔷 * x := by
  unfold normVolume
  rw [mul_smul_comm, even_mul_volume Q v hv hspan hx, smul_mul_assoc]

variable [Invertible (2 : R)]

omit hv in
/-- The idempotents `p± = (1 ± z)/2`. -/
def idemPlus (d : R) : CliffordAlgebra Q := ⅟(2 : R) • (1 + normVolume Q v d)

omit hv in
def idemMinus (d : R) : CliffordAlgebra Q := ⅟(2 : R) • (1 - normVolume Q v d)

local notation "𝔭₊" => idemPlus Q v d
local notation "𝔭₋" => idemMinus Q v d

omit hv in
theorem idemPlus_add_idemMinus : 𝔭₊ + 𝔭₋ = 1 := by
  unfold idemPlus idemMinus
  rw [← smul_add, add_add_sub_cancel, ← two_smul R (1 : CliffordAlgebra Q), smul_smul, invOf_mul_self,
    one_smul]

include hd in
theorem idemPlus_mul_self : 𝔭₊ * 𝔭₊ = 𝔭₊ := by
  unfold idemPlus
  rw [smul_mul_smul_comm, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul,
    normVolume_mul_self Q v hv hd]
  rw [show (1 : CliffordAlgebra Q) + 𝔷 + (𝔷 + 1) = (2 : R) • (1 + 𝔷) by
    rw [two_smul]; abel, smul_smul, mul_assoc, invOf_mul_self, mul_one]

include hd in
theorem idemMinus_mul_self : 𝔭₋ * 𝔭₋ = 𝔭₋ := by
  unfold idemMinus
  rw [smul_mul_smul_comm, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul,
    normVolume_mul_self Q v hv hd]
  rw [show (1 : CliffordAlgebra Q) - 𝔷 - (𝔷 - 1) = (2 : R) • (1 - 𝔷) by
    rw [two_smul]; abel, smul_smul, mul_assoc, invOf_mul_self, mul_one]

include hd in
theorem idemPlus_mul_idemMinus : 𝔭₊ * 𝔭₋ = 0 := by
  unfold idemPlus idemMinus
  rw [smul_mul_smul_comm, add_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul,
    normVolume_mul_self Q v hv hd, show (1 : CliffordAlgebra Q) - 𝔷 + (𝔷 - 1) = 0 by abel, smul_zero]

include hd in
theorem idemMinus_mul_idemPlus : 𝔭₋ * 𝔭₊ = 0 := by
  unfold idemPlus idemMinus
  rw [smul_mul_smul_comm, sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul,
    normVolume_mul_self Q v hv hd, show (1 : CliffordAlgebra Q) + 𝔷 - (𝔷 + 1) = 0 by abel, smul_zero]

/-- The generators exchange the idempotents: `eᵢ p₊ = p₋ eᵢ`. -/
theorem gen_mul_idemPlus (i : Fin 4) : 𝔢 i * 𝔭₊ = 𝔭₋ * 𝔢 i := by
  unfold idemPlus idemMinus
  rw [mul_smul_comm, smul_mul_assoc, mul_add, sub_mul, mul_one, one_mul, gen_mul_normVolume Q v hv,
    sub_eq_add_neg]

theorem gen_mul_idemMinus (i : Fin 4) : 𝔢 i * 𝔭₋ = 𝔭₊ * 𝔢 i := by
  unfold idemPlus idemMinus
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, add_mul, mul_one, one_mul, gen_mul_normVolume Q v hv,
    sub_neg_eq_add]

omit hv in
theorem involute_idemPlus : involute 𝔭₊ = 𝔭₊ := by
  unfold idemPlus
  rw [map_smul, map_add, map_one, involute_normVolume]

omit hv in
theorem involute_idemMinus : involute 𝔭₋ = 𝔭₋ := by
  unfold idemMinus
  rw [map_smul, map_sub, map_one, involute_normVolume]

theorem reverse_idemPlus : reverse 𝔭₊ = 𝔭₊ := by
  unfold idemPlus
  rw [map_smul, map_add, reverse.map_one, reverse_normVolume Q v hv]

theorem reverse_idemMinus : reverse 𝔭₋ = 𝔭₋ := by
  unfold idemMinus
  rw [map_smul, map_sub, reverse.map_one, reverse_normVolume Q v hv]

theorem even_mul_idemPlus (hspan : ∀ m : M, m ∈ Submodule.span R (Set.range v)) {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 0) : x * 𝔭₊ = 𝔭₊ * x := by
  unfold idemPlus
  rw [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
    even_mul_normVolume Q v hv hspan hx]

theorem even_mul_idemMinus (hspan : ∀ m : M, m ∈ Submodule.span R (Set.range v)) {x : CliffordAlgebra Q}
    (hx : x ∈ evenOdd Q 0) : x * 𝔭₋ = 𝔭₋ * x := by
  unfold idemMinus
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul,
    even_mul_normVolume Q v hv hspan hx]

end CliffordAlgebra.OrthogonalQuadruple

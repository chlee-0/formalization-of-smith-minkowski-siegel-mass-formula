import SMSFormula.SpecialOrthogonalRealIdentitySphereVolume

/-!
# Last-column geometry for the identity-model real special orthogonal group

This module defines the last-column map from the project identity-form group
in rank `n + 1` to the Euclidean unit sphere. It proves sphere membership,
continuity, multiplication compatibility, and an exact characterization of
the identity-vector fiber. No orbit-surjectivity or measure disintegration is
asserted.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

/-- The project identity-form real special orthogonal group in rank `n + 1`. -/
abbrev identitySpecialOrthogonalGroup (n : ℕ) :=
  specialFormPreservingMatrixSubgroup
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)

/-- The Euclidean unit sphere carrying the last column in rank `n + 1`. -/
abbrev identitySpecialOrthogonalLastColumnSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The last matrix column, regarded as a vector in Euclidean space. -/
def identitySpecialOrthogonalLastColumnVector
    (n : ℕ) (g : identitySpecialOrthogonalGroup n) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => g.1.1.1 i (Fin.last n))

@[simp]
theorem identitySpecialOrthogonalLastColumnVector_apply
    (n : ℕ) (g : identitySpecialOrthogonalGroup n)
    (i : Fin (n + 1)) :
    identitySpecialOrthogonalLastColumnVector n g i =
      g.1.1.1 i (Fin.last n) :=
  rfl

/-- Form preservation makes the last column a unit vector. -/
theorem norm_identitySpecialOrthogonalLastColumnVector
    (n : ℕ) (g : identitySpecialOrthogonalGroup n) :
    ‖identitySpecialOrthogonalLastColumnVector n g‖ = 1 := by
  have hpres := g.1.2
  have hentry :
      (∑ i, g.1.1.1 i (Fin.last n) *
        g.1.1.1 i (Fin.last n)) = 1 := by
    simpa [Matrix.mul_apply] using congrArg
      (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
        A (Fin.last n) (Fin.last n)) hpres
  have hsq :
      ‖identitySpecialOrthogonalLastColumnVector n g‖ ^ 2 =
        (1 : ℝ) ^ 2 := by
    calc
      ‖identitySpecialOrthogonalLastColumnVector n g‖ ^ 2 =
          RCLike.re (inner ℝ
            (identitySpecialOrthogonalLastColumnVector n g)
            (identitySpecialOrthogonalLastColumnVector n g)) :=
        norm_sq_eq_re_inner (𝕜 := ℝ) _
      _ = 1 := by
        change
          (∑ i, g.1.1.1 i (Fin.last n) *
            g.1.1.1 i (Fin.last n)) = 1
        exact hentry
      _ = (1 : ℝ) ^ 2 := by norm_num
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hsq

/-- The last-column map into the Euclidean unit sphere. -/
def identitySpecialOrthogonalLastColumn
    (n : ℕ) (g : identitySpecialOrthogonalGroup n) :
    identitySpecialOrthogonalLastColumnSphere n :=
  ⟨identitySpecialOrthogonalLastColumnVector n g, by
    rw [Metric.mem_sphere, dist_zero_right,
      norm_identitySpecialOrthogonalLastColumnVector]⟩

@[simp]
theorem coe_identitySpecialOrthogonalLastColumn
    (n : ℕ) (g : identitySpecialOrthogonalGroup n) :
    (identitySpecialOrthogonalLastColumn n g :
      EuclideanSpace ℝ (Fin (n + 1))) =
        identitySpecialOrthogonalLastColumnVector n g :=
  rfl

/-- The last-column vector depends continuously on the group element. -/
theorem continuous_identitySpecialOrthogonalLastColumnVector (n : ℕ) :
    Continuous (identitySpecialOrthogonalLastColumnVector n) := by
  have hmatrix :
      Continuous
        (fun g : identitySpecialOrthogonalGroup n => g.1.1.1) :=
    Units.continuous_val.comp
      (continuous_subtype_val.comp continuous_subtype_val)
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
  apply continuous_pi
  intro i
  exact
    (continuous_apply (Fin.last n)).comp
      ((continuous_apply i).comp hmatrix)

/-- The last-column sphere map is continuous. -/
theorem continuous_identitySpecialOrthogonalLastColumn (n : ℕ) :
    Continuous (identitySpecialOrthogonalLastColumn n) :=
  (continuous_identitySpecialOrthogonalLastColumnVector n).subtype_mk _

/-- Ambient matrix action on a Euclidean vector. -/
def identitySpecialOrthogonalMatrixActionVector
    (n : ℕ) (g : identitySpecialOrthogonalGroup n)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (g.1.1.1 *ᵥ fun i => v i)

/-- Taking the last column converts group multiplication into the ambient
matrix action. -/
theorem identitySpecialOrthogonalLastColumnVector_mul
    (n : ℕ) (g h : identitySpecialOrthogonalGroup n) :
    identitySpecialOrthogonalLastColumnVector n (g * h) =
      identitySpecialOrthogonalMatrixActionVector n g
        (identitySpecialOrthogonalLastColumnVector n h) := by
  ext i
  simp [identitySpecialOrthogonalLastColumnVector,
    identitySpecialOrthogonalMatrixActionVector, Matrix.mulVec,
    Matrix.mul_apply, dotProduct]

/-- The distinguished identity vector on the last-column sphere. -/
def identitySpecialOrthogonalNorthPole (n : ℕ) :
    identitySpecialOrthogonalLastColumnSphere n :=
  identitySpecialOrthogonalLastColumn n 1

@[simp]
theorem coe_identitySpecialOrthogonalNorthPole_apply
    (n : ℕ) (i : Fin (n + 1)) :
    (identitySpecialOrthogonalNorthPole n :
      EuclideanSpace ℝ (Fin (n + 1))) i =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          i (Fin.last n) :=
  rfl

/-- The fiber of the identity vector under the last-column map. -/
def identitySpecialOrthogonalLastColumnFiber (n : ℕ) :
    Set (identitySpecialOrthogonalGroup n) :=
  {g | identitySpecialOrthogonalLastColumn n g =
    identitySpecialOrthogonalNorthPole n}

/-- Membership in the identity-vector fiber is exactly equality of the last
matrix column with the last standard basis vector. -/
theorem mem_identitySpecialOrthogonalLastColumnFiber_iff
    (n : ℕ) (g : identitySpecialOrthogonalGroup n) :
    g ∈ identitySpecialOrthogonalLastColumnFiber n ↔
      ∀ i, g.1.1.1 i (Fin.last n) =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          i (Fin.last n) := by
  constructor
  · intro hg i
    have hv := congrArg
      (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v i)
      (congrArg Subtype.val hg)
    exact hv
  · intro hg
    apply Subtype.ext
    ext i
    exact hg i

/-- Entrywise, the identity-vector fiber fixes the last standard basis
vector. -/
theorem mem_identitySpecialOrthogonalLastColumnFiber_iff_apply
    (n : ℕ) (g : identitySpecialOrthogonalGroup n) :
    g ∈ identitySpecialOrthogonalLastColumnFiber n ↔
      ∀ i, g.1.1.1 i (Fin.last n) =
        if i = Fin.last n then 1 else 0 := by
  rw [mem_identitySpecialOrthogonalLastColumnFiber_iff]
  simp only [Matrix.one_apply]

/-- The identity belongs to the identity-vector fiber. -/
theorem one_mem_identitySpecialOrthogonalLastColumnFiber (n : ℕ) :
    (1 : identitySpecialOrthogonalGroup n) ∈
      identitySpecialOrthogonalLastColumnFiber n := by
  rw [mem_identitySpecialOrthogonalLastColumnFiber_iff]
  intro i
  rfl

/-- The identity-vector fiber is closed. -/
theorem isClosed_identitySpecialOrthogonalLastColumnFiber (n : ℕ) :
    IsClosed (identitySpecialOrthogonalLastColumnFiber n) :=
  isClosed_eq
    (continuous_identitySpecialOrthogonalLastColumn n)
    continuous_const

end PositiveDefiniteIntegralLattice

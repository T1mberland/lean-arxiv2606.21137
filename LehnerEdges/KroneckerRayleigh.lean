import LehnerEdges.MatrixRayleigh
import LehnerEdges.PurificationBound

/-! The vectorization identity has a transpose on the second Kronecker
factor. This is kept explicit throughout the matrix-model identification. -/

noncomputable section
open Matrix
open scoped InnerProductSpace Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace LehnerEdges

theorem kronecker_transpose_mulVec {N M : ℕ} (A : Mat N) (B : Mat M)
    (S : Matrix (Fin N) (Fin M) ℂ) :
    (EuclideanSpace.equiv (Fin N × Fin M) ℂ).symm ((A ⊗ₖ B.transpose) *ᵥ matrixVector S) =
      matrixVector (A * S * B) := by
  ext p
  rcases p with ⟨a, b⟩
  change (∑ p : Fin N × Fin M, (A ⊗ₖ B.transpose) (a, b) p * S p.1 p.2) = (A * S * B) a b
  simp only [Fintype.sum_prod_type, kronecker_apply, transpose_apply,
    Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem matrixRayleigh_kronecker_transpose {N M : ℕ} (A : Mat N) (B : Mat M)
    (u : UnitPurification N M) :
    matrixRayleigh (A ⊗ₖ B.transpose) u =
      ((purificationMatrix u).conjTranspose * A * purificationMatrix u * B).trace.re := by
  unfold matrixRayleigh
  change (inner ℂ (matrixVector (purificationMatrix u))
    ((EuclideanSpace.equiv (Fin N × Fin M) ℂ).symm
      ((A ⊗ₖ B.transpose) *ᵥ matrixVector (purificationMatrix u)))).re = _
  rw [kronecker_transpose_mulVec, matrixVector_inner]
  simp only [Matrix.mul_assoc]

theorem matrixRayleigh_kronecker_one {N M : ℕ} (A : Mat N) (u : UnitPurification N M) :
    matrixRayleigh (A ⊗ₖ (1 : Mat M)) u = purificationDrift A u := by
  have h := matrixRayleigh_kronecker_transpose A (1 : Mat M) u
  simp only [transpose_one, Matrix.mul_one] at h
  rw [h, trace_mul_cycle]
  exact congrArg Complex.re (Matrix.trace_mul_comm _ A)

theorem matrixRayleigh_add {κ : Type*} [Fintype κ]
    (B C : Matrix κ κ ℂ) (u : ComplexUnitSphere κ) :
    matrixRayleigh (B + C) u = matrixRayleigh B u + matrixRayleigh C u := by
  simp only [matrixRayleigh, Matrix.add_mulVec, map_add, inner_add_right, Complex.add_re]

theorem matrixRayleigh_sum {κ ι : Type*} [Fintype κ] [Fintype ι]
    (B : ι → Matrix κ κ ℂ) (u : ComplexUnitSphere κ) :
    matrixRayleigh (∑ i, B i) u = ∑ i, matrixRayleigh (B i) u := by
  simp only [matrixRayleigh, Matrix.sum_mulVec, map_sum, inner_sum, Complex.re_sum]

theorem matrixRayleigh_real_smul {κ : Type*} [Fintype κ]
    (B : Matrix κ κ ℂ) (u : ComplexUnitSphere κ) (r : ℝ) :
    matrixRayleigh (r • B) u = r * matrixRayleigh B u := by
  simp only [matrixRayleigh, Matrix.smul_mulVec, ← Complex.coe_smul,
    map_smul, inner_smul_right, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

theorem kronecker_hermitian {N M : ℕ} {A : Mat N} {B : Mat M}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  show (A ⊗ₖ B).conjTranspose = A ⊗ₖ B
  rw [conjTranspose_kronecker, hA.eq, hB.eq]

/-- The paper's random Kronecker matrix, on the product index set. Each input
complex coordinate supplies two real variance-one Gaussian coordinates. -/
def gueMatrixModel {n N M : ℕ} (A₀ : Mat N) (A : Fin n → Mat N)
    (g : GaussianCoordinates n M M) : Matrix (Fin N × Fin M) (Fin N × Fin M) ℂ :=
  A₀ ⊗ₖ (1 : Mat M) + (1 / Real.sqrt M : ℝ) •
    ∑ i, A i ⊗ₖ gueProjection (familyMatrices g i)

/-- The same construction with each GUE factor transposed. Gaussian
transpose invariance will identify its expectation with `gueMatrixModel`. -/
def transposedGueMatrixModel {n N M : ℕ} (A₀ : Mat N) (A : Fin n → Mat N)
    (g : GaussianCoordinates n M M) : Matrix (Fin N × Fin M) (Fin N × Fin M) ℂ :=
  A₀ ⊗ₖ (1 : Mat M) + (1 / Real.sqrt M : ℝ) •
    ∑ i, A i ⊗ₖ (gueProjection (familyMatrices g i)).transpose

theorem gueMatrixModel_hermitian {n N M : ℕ} (A₀ : Mat N) (A : Fin n → Mat N)
    (h₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (g : GaussianCoordinates n M M) :
    (gueMatrixModel A₀ A g).IsHermitian := by
  apply (kronecker_hermitian h₀ isHermitian_one).add
  apply Matrix.IsHermitian.smul _ (isSelfAdjoint_iff.mpr rfl)
  exact isSelfAdjoint_sum _ (fun i _ => kronecker_hermitian (hA i) (gueProjection_hermitian _))

theorem transposedGueMatrixModel_hermitian {n N M : ℕ} (A₀ : Mat N) (A : Fin n → Mat N)
    (h₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (g : GaussianCoordinates n M M) :
    (transposedGueMatrixModel A₀ A g).IsHermitian := by
  apply (kronecker_hermitian h₀ isHermitian_one).add
  apply Matrix.IsHermitian.smul _ (isSelfAdjoint_iff.mpr rfl)
  exact isSelfAdjoint_sum _ (fun i _ =>
    kronecker_hermitian (hA i) (gueProjection_hermitian _).transpose)

end LehnerEdges

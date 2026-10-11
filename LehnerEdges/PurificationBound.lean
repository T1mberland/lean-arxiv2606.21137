import LehnerEdges.PurificationComparison
import LehnerEdges.FiniteBlockBound

/-! Identifying the rectangular purification process with the trace pairing
used in the deterministic block estimate. -/

noncomputable section
open Matrix
open scoped NNReal InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace LehnerEdges

def familyMatrices {n N M : ℕ} (g : GaussianCoordinates n N M) :
    Fin n → Matrix (Fin N) (Fin M) ℂ := fun i a b => g (i, a, b)

@[simp] theorem familyMatrices_familyVector {n N M : ℕ}
    (B : Fin n → Matrix (Fin N) (Fin M) ℂ) : familyMatrices (familyVector B) = B := rfl

theorem familyVector_real_inner {n N M : ℕ}
    (B D : Fin n → Matrix (Fin N) (Fin M) ℂ) :
    inner ℝ (familyVector B) (familyVector D) = ∑ i, frobeniusPair (B i) (D i) := by
  rw [euclidean_real_inner_eq_re]
  have h : inner ℂ (familyVector B) (familyVector D) =
      ∑ i, ((B i).conjTranspose * D i).trace := by
    simp only [familyVector, PiLp.inner_apply, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [matrixVector, PiLp.inner_apply, Fintype.sum_prod_type] using matrixVector_inner (B i) (D i)
  rw [h, Complex.re_sum]
  rfl

theorem frobeniusPair_smul_right {N M : ℕ} (W T : Matrix (Fin N) (Fin M) ℂ) (c : ℝ) :
    frobeniusPair W (c • T) = c * frobeniusPair W T := by
  simp only [frobeniusPair, Matrix.mul_smul, trace_smul, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem frobeniusPair_sum {n N M : ℕ} (W : Matrix (Fin N) (Fin M) ℂ)
    (T : Fin n → Matrix (Fin N) (Fin M) ℂ) :
    frobeniusPair W (∑ i, T i) = ∑ i, frobeniusPair W (T i) := by
  simp only [frobeniusPair, Matrix.mul_sum, trace_sum, Complex.re_sum]

theorem frobeniusPair_mul_left {N M : ℕ} (B : Mat N) (hB : B.IsHermitian)
    (W T : Matrix (Fin N) (Fin M) ℂ) :
    frobeniusPair (B * W) T = frobeniusPair W (B * T) := by
  simp only [frobeniusPair, conjTranspose_mul, hB.eq, Matrix.mul_assoc]

theorem purification_complex_pair {n N M : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) (S : Matrix (Fin N) (Fin M) ℂ)
    (g : GaussianCoordinates n N M) :
    inner ℝ (purificationComplexCoefficient A S) g =
      (2 / Real.sqrt M) * frobeniusPair (polarContraction S)
        (∑ i, compressed (S * S.conjTranspose) (A i) *
          ((1 / Real.sqrt 2 : ℝ) • familyMatrices g i)) := by
  have hg : familyVector (familyMatrices g) = g := rfl
  rw [purificationComplexCoefficient, real_inner_smul_left, ← hg,
    familyVector_real_inner, frobeniusPair_sum]
  simp only [← compressed_mul_polar S,
    frobeniusPair_mul_left _ (purification_compressed_hermitian S (hA _)),
    Matrix.mul_smul, frobeniusPair_smul_right, ← Finset.mul_sum]
  simp only [familyMatrices_familyVector]
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem purification_pair_le_traceNorm {N M : ℕ} (S T : Matrix (Fin N) (Fin M) ℂ) :
    frobeniusPair (polarContraction S) T ≤ traceNorm T := by
  calc
    _ ≤ |frobeniusPair (polarContraction S) T| := le_abs_self _
    _ ≤ ‖polarContraction S‖ * traceNorm T := abs_frobeniusPair_le_traceNorm _ _
    _ ≤ 1 * traceNorm T := mul_le_mul_of_nonneg_right (polarContraction_norm_le S) (traceNorm_nonneg T)
    _ = _ := one_mul _

theorem purification_comparison_pointwise {n N M : ℕ} [NeZero N]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (u : UnitPurification N M)
    (g : GaussianCoordinates n N M) :
    purificationDrift A₀ u + inner ℝ (purificationComplexCoefficient A (purificationMatrix u)) g ≤
      rhoPlus A₀ A + 2 * max
        (‖blockColumn (fun i => (1 / Real.sqrt 2 : ℝ) • familyMatrices g i)‖ / Real.sqrt M - 1) 0 *
          Real.sqrt ‖squareFunction A‖ := by
  rw [purification_complex_pair A hA]
  apply le_trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (purification_pair_le_traceNorm _ _)
      (div_nonneg (by norm_num) (Real.sqrt_nonneg _))))
  exact pointwise_comparison_bound A₀ A h₀ hA
    (purificationDensity (purificationMatrix u) (purificationMatrix_frobeniusSq u)) _

end LehnerEdges

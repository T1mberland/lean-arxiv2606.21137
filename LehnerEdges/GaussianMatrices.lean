import LehnerEdges.TraceNorm
import LehnerEdges.GaussianConcentration
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! Explicit real-coordinate constructions with the normalization in Section 2.
The standard Gaussian on complex Euclidean space is taken over `ℝ`, hence its
real and imaginary coordinates have variance one before the displayed scaling. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace LehnerEdges

theorem euclidean_real_inner_eq_re {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℂ ι) : inner ℝ x y = (inner ℂ x y).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_eq_re_inner ℂ (x i) (y i)

def matrixOfVector {N M : ℕ} (g : EuclideanSpace ℂ (Fin N × Fin M)) :
    Matrix (Fin N) (Fin M) ℂ := fun a b => g (a, b)

@[simp] theorem matrixVector_matrixOfVector {N M : ℕ}
    (g : EuclideanSpace ℂ (Fin N × Fin M)) : matrixVector (matrixOfVector g) = g := rfl

/-- Orthogonal projection onto Hermitian matrices. Applied to a real isotropic
Gaussian complex matrix this produces GUE with diagonal variance `1` and
off-diagonal real/imaginary variance `1/2`. -/
def gueProjection {N : ℕ} (Z : Mat N) : Mat N := (1 / 2 : ℝ) • (Z + Z.conjTranspose)

theorem gueProjection_hermitian {N : ℕ} (Z : Mat N) : (gueProjection Z).IsHermitian := by
  show (gueProjection Z).conjTranspose = gueProjection Z
  simp [gueProjection, conjTranspose_smul, conjTranspose_add, add_comm]

theorem gueProjection_pair {N : ℕ} (Z K : Mat N) (hK : K.IsHermitian) :
    frobeniusPair (gueProjection Z) K = frobeniusPair Z K := by
  have h : (Z * K).trace.re = (Z.conjTranspose * K).trace.re := by
    rw [← re_trace_conjTranspose (Z * K), conjTranspose_mul, hK.eq, trace_mul_comm]
  simp only [frobeniusPair, gueProjection, conjTranspose_smul, conjTranspose_add,
    conjTranspose_conjTranspose, star_trivial, Matrix.smul_mul, add_mul, trace_smul,
    trace_add, Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, h]
  ring

/-- Every Hermitian linear test of the constructed matrix is a real Gaussian
linear functional, with precisely the Frobenius coefficient. -/
theorem gue_pair_eq_innerSL {N : ℕ} (K : Mat N) (hK : K.IsHermitian) :
    (fun g : EuclideanSpace ℂ (Fin N × Fin N) =>
      frobeniusPair (gueProjection (matrixOfVector g)) K) = innerSL ℝ (matrixVector K) := by
  ext g
  rw [gueProjection_pair _ _ hK, frobeniusPair,
    ← matrixVector_inner, matrixVector_matrixOfVector]
  calc (inner ℂ g (matrixVector K)).re = inner ℝ g (matrixVector K) :=
         (euclidean_real_inner_eq_re g (matrixVector K)).symm
       _ = inner ℝ (matrixVector K) g := real_inner_comm _ _
       _ = _ := rfl

/-- Section 2's GUE normalization, verified under an actual Gaussian law. -/
theorem gue_variance_pair {N : ℕ} (K : Mat N) (hK : K.IsHermitian) :
    variance (fun g : EuclideanSpace ℂ (Fin N × Fin N) =>
      frobeniusPair (gueProjection (matrixOfVector g)) K)
      (stdGaussian (EuclideanSpace ℂ (Fin N × Fin N))) = frobeniusSq K := by
  rw [gue_pair_eq_innerSL K hK, variance_dual_stdGaussian,
    innerSL_apply_norm, matrixVector_norm_sq]

theorem gue_mean_pair {N : ℕ} (K : Mat N) (hK : K.IsHermitian) :
    (∫ g : EuclideanSpace ℂ (Fin N × Fin N),
      frobeniusPair (gueProjection (matrixOfVector g)) K
      ∂stdGaussian (EuclideanSpace ℂ (Fin N × Fin N))) = 0 := by
  rw [gue_pair_eq_innerSL K hK, integral_strongDual_stdGaussian]

/-- The complete scalar law for every Hermitian linear test of the GUE
construction. This certifies Gaussianity in addition to mean and variance. -/
theorem gue_pair_law {N : ℕ} (K : Mat N) (hK : K.IsHermitian) :
    (stdGaussian (EuclideanSpace ℂ (Fin N × Fin N))).map
      (fun g => frobeniusPair (gueProjection (matrixOfVector g)) K) =
      gaussianReal 0 (frobeniusSq K).toNNReal := by
  have hg : HasGaussianLaw
      (fun g : EuclideanSpace ℂ (Fin N × Fin N) =>
        frobeniusPair (gueProjection (matrixOfVector g)) K)
      (stdGaussian (EuclideanSpace ℂ (Fin N × Fin N))) := by
    rw [gue_pair_eq_innerSL K hK]
    simpa only [Function.comp_id] using
      (IsGaussian.hasGaussianLaw_id (μ := stdGaussian (EuclideanSpace ℂ (Fin N × Fin N)))).map
        (innerSL ℝ (matrixVector K))
  have h := hg.map_eq_gaussianReal
  rw [gue_mean_pair K hK, gue_variance_pair K hK] at h
  exact h

/-- Standard complex Gaussian scaling: each real coordinate has variance `1/2`. -/
def complexGaussianMatrix {N M : ℕ} (g : EuclideanSpace ℂ (Fin N × Fin M)) :
    Matrix (Fin N) (Fin M) ℂ := (1 / Real.sqrt 2 : ℝ) • matrixOfVector g

set_option maxHeartbeats 800000 in
theorem matrixOfVector_norm_lipschitz {N M : ℕ} :
    LipschitzWith 1 (fun g : EuclideanSpace ℂ (Fin N × Fin M) => ‖matrixOfVector g‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  calc dist ‖matrixOfVector x‖ ‖matrixOfVector y‖ ≤ dist (matrixOfVector x) (matrixOfVector y) :=
         by simpa only [dist_eq_norm] using (dist_norm_norm_le (matrixOfVector x) (matrixOfVector y))
       _ = ‖matrixOfVector (x - y)‖ := by rw [dist_eq_norm]; rfl
       _ ≤ Real.sqrt (frobeniusSq (matrixOfVector (x - y))) := opNorm_le_frobenius _
       _ = dist x y := by
         rw [← matrixVector_norm_sq, matrixVector_matrixOfVector,
           Real.sqrt_sq (norm_nonneg _), dist_eq_norm]

/-- Concentration for a rectangular Gaussian matrix norm, centered at its
actual mean. The separate `sqrt M + sqrt d` mean estimate is not assumed. -/
theorem gaussian_matrix_norm_concentration {N M : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian (EuclideanSpace ℂ (Fin N × Fin M))).real
      {g | t ≤ ‖matrixOfVector g‖ - ∫ h, ‖matrixOfVector h‖
        ∂stdGaussian (EuclideanSpace ℂ (Fin N × Fin M))} ≤ Real.exp (-t ^ 2 / 2) := by
  simpa using stdGaussian_measure_ge_le (matrixOfVector_norm_lipschitz (N := N) (M := M)) ht

end LehnerEdges

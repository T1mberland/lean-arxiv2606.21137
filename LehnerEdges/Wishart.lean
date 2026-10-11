import LehnerEdges.GaussianMatrices

/-! Normalized complex Gaussian and Wishart norm identities and concentration.
The dimension-dependent mean estimate in Lemma 5.1 remains open. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace LehnerEdges

theorem complexGaussianMatrix_norm_lipschitz {N M : ℕ} :
    LipschitzWith ⟨1 / Real.sqrt 2, div_nonneg zero_le_one (Real.sqrt_nonneg _)⟩
      (fun g : EuclideanSpace ℂ (Fin N × Fin M) => ‖complexGaussianMatrix g‖) := by
  let c : ℝ := 1 / Real.sqrt 2
  have hc : 0 ≤ c := div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have heq : (fun g : EuclideanSpace ℂ (Fin N × Fin M) => ‖complexGaussianMatrix g‖) =
      fun g => c * ‖matrixOfVector g‖ := by
    ext g
    simp only [complexGaussianMatrix, norm_smul, Real.norm_eq_abs]
    change |c| * ‖matrixOfVector g‖ = c * ‖matrixOfVector g‖
    rw [abs_of_nonneg hc]
  rw [heq]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (c * ‖matrixOfVector x‖) (c * ‖matrixOfVector y‖) ≤ c * dist x y
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    (matrixOfVector_norm_lipschitz (N := N) (M := M)).dist_le_mul x y

/-- Concentration for Section 2's standard complex Gaussian normalization:
real and imaginary coordinates have variance `1/2`, giving exponent `-t²`. -/
theorem complex_gaussian_matrix_norm_concentration {N M : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian (EuclideanSpace ℂ (Fin N × Fin M))).real
      {g | t ≤ ‖complexGaussianMatrix g‖ - ∫ h, ‖complexGaussianMatrix h‖
        ∂stdGaussian (EuclideanSpace ℂ (Fin N × Fin M))} ≤ Real.exp (-t ^ 2) := by
  have h := stdGaussian_measure_ge_le (complexGaussianMatrix_norm_lipschitz (N := N) (M := M)) ht
  have hc : 2 * (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  change _ ≤ Real.exp (-t ^ 2 / (2 * (1 / Real.sqrt 2) ^ 2)) at h
  rw [hc, div_one] at h
  exact h

def wishartMatrix {N M : ℕ} (Γ : Matrix (Fin N) (Fin M) ℂ) : Mat N :=
  (1 / (M : ℝ)) • (Γ * Γ.conjTranspose)

theorem wishartMatrix_posSemidef {N M : ℕ} (Γ : Matrix (Fin N) (Fin M) ℂ) :
    (wishartMatrix Γ).PosSemidef := by
  exact (Matrix.posSemidef_self_mul_conjTranspose Γ).smul
    (div_nonneg zero_le_one (Nat.cast_nonneg M) : 0 ≤ 1 / (M : ℝ))

/-- The exact singular-value identity used to express Lemma 5.1 as a Gaussian
matrix norm estimate. It is also valid when `M = 0` by total division. -/
theorem wishart_sqrt_norm {N M : ℕ} (Γ : Matrix (Fin N) (Fin M) ℂ) :
    Real.sqrt ‖wishartMatrix Γ‖ = ‖Γ‖ / Real.sqrt M := by
  have hn : ‖Γ * Γ.conjTranspose‖ = ‖Γ‖ ^ 2 := by
    simpa only [conjTranspose_conjTranspose, l2_opNorm_conjTranspose, pow_two] using
      l2_opNorm_conjTranspose_mul_self Γ.conjTranspose
  rw [wishartMatrix, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg M)), hn]
  rw [one_div_mul_eq_div, Real.sqrt_div (sq_nonneg _) _, Real.sqrt_sq (norm_nonneg _)]

end LehnerEdges

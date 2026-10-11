import LehnerEdges.QuadraticEdges
import LehnerEdges.GaussianMaximum
import LehnerEdges.LeftVariational

/-! The finite-dimensional operator-norm theorem, for the explicit normalized
GUE Kronecker model. No identification with free operator edges is assumed. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace LehnerEdges

theorem spectralScale_le_error_scale {n N M : ℕ} [NeZero n] [NeZero N]
    (A : Fin n → Mat N) :
    (spectralScale A M : ℝ) ≤ Real.sqrt ((n : ℝ) * N / M) * Real.sqrt ‖squareFunction A‖ := by
  have hd : 1 ≤ (n : ℝ) * N := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne N))
  have hroot : 1 ≤ Real.sqrt ((n : ℝ) * N) := Real.one_le_sqrt.mpr hd
  change Real.sqrt ‖squareFunction A‖ / Real.sqrt M ≤ _
  calc
    _ ≤ (Real.sqrt ((n : ℝ) * N) * Real.sqrt ‖squareFunction A‖) / Real.sqrt M :=
      div_le_div_of_nonneg_right (by nlinarith [Real.sqrt_nonneg ‖squareFunction A‖]) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_div (by positivity : 0 ≤ (n : ℝ) * N) M]; ring

/-- A stronger constant-eight estimate for positive dimensions and at least
one coefficient. The dimension condition `M ≥ N` is unnecessary for the
direct purification proof. -/
theorem expected_gueMatrixModel_norm_le_eight_pos {n N M : ℕ} [NeZero n] [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).PosSemidef) :
    (∫ g, ‖gueMatrixModel A₀ A g‖ ∂stdGaussian (GaussianCoordinates n M M)) ≤
      rhoStar A₀ A + 8 * Real.sqrt ((n : ℝ) * N / M) * Real.sqrt ‖squareFunction A‖ := by
  let b := rhoStar A₀ A + 6 * Real.sqrt ((n : ℝ) * N / M) * Real.sqrt ‖squareFunction A‖
  have hHerm : ∀ i, (A i).IsHermitian := fun i => (hA i).isHermitian
  have hplus : rhoPlus A₀ A ≤ rhoStar A₀ A := le_max_left _ _
  have hminus : rhoPlus (-A₀) A ≤ rhoStar A₀ A := by
    rw [rhoStar_eq_max_rhoPlus A₀ A h₀ hHerm]
    exact le_max_right _ _
  have hfb : (∫ g : GaussianCoordinates n M M, quadraticGueSup A₀ A g ∂stdGaussian _) ≤ b := by
    have h := gaussian_purification_edge_bound_six (M := M) A₀ A h₀ hA
    dsimp [b]
    exact h.trans (add_le_add_left hplus _)
  have hgb : (∫ g : GaussianCoordinates n M M, quadraticGueSup (-A₀) A (-g) ∂stdGaussian _) ≤ b := by
    rw [integral_quadraticGueSup_neg (-A₀) A h₀.neg hHerm]
    exact (gaussian_purification_edge_bound_six (-A₀) A h₀.neg hA).trans (add_le_add_left hminus _)
  calc
    _ = ∫ g, ‖transposedGueMatrixModel A₀ A g‖ ∂stdGaussian (GaussianCoordinates n M M) :=
      integral_gueMatrixModel_transpose A₀ A
    _ = ∫ g, max (quadraticGueSup A₀ A g) (quadraticGueSup (-A₀) A (-g))
        ∂stdGaussian (GaussianCoordinates n M M) := by
      simp_rw [transposedGueMatrixModel_norm_eq_max A₀ A h₀ hHerm]
    _ ≤ b + 2 * (spectralScale A M : ℝ) :=
      stdGaussian_integral_max_le (quadraticGueSup_lipschitz A₀ A h₀ hHerm)
        (quadraticGueSup_neg_lipschitz (-A₀) A h₀.neg hHerm) b hfb hgb
    _ ≤ _ := by
      have h := spectralScale_le_error_scale (M := M) A
      dsimp [b]
      nlinarith

/-- The same estimate includes the empty coefficient family. Its proof pads
that family by one zero coefficient; the Gaussian error then vanishes. -/
theorem expected_gueMatrixModel_norm_le_eight {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).PosSemidef) :
    (∫ g, ‖gueMatrixModel A₀ A g‖ ∂stdGaussian (GaussianCoordinates n M M)) ≤
      rhoStar A₀ A + 8 * Real.sqrt ((n : ℝ) * N / M) * Real.sqrt ‖squareFunction A‖ := by
  by_cases hn : n = 0
  · subst n
    have h := expected_gueMatrixModel_norm_le_eight_pos (M := M) A₀
      (fun _ : Fin 1 => (0 : Mat N)) h₀ (fun _ => Matrix.PosSemidef.zero)
    have hρ : rhoStar A₀ (fun _ : Fin 1 => (0 : Mat N)) = rhoStar A₀ A := by
      simp only [rhoStar, rhoPlus, rhoMinus, lehnerMatrix, covariance,
        Finset.univ_unique, Finset.sum_singleton, Matrix.zero_mul, Matrix.mul_zero,
        Finset.univ_eq_empty, Finset.sum_empty]
    rw [hρ] at h
    simpa [gueMatrixModel, squareFunction] using h
  · letI : NeZero n := ⟨hn⟩
    exact expected_gueMatrixModel_norm_le_eight_pos A₀ A h₀ hA

/-- Theorem 7.2 of Collins–Yamagishi, arXiv:2606.21137v2, with its precise
constant nine. The proof above actually works for every positive `M`, and
proves constant eight. `rhoStar` is the finite variational quantity defined
over positive and negative definite matrices, not an assumed free edge. -/
theorem theorem_7_2 {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).PosSemidef) (_hMN : N ≤ M) :
    (∫ g, ‖gueMatrixModel A₀ A g‖ ∂stdGaussian (GaussianCoordinates n M M)) ≤
      rhoStar A₀ A + 9 * Real.sqrt ((n : ℝ) * N / M) * Real.sqrt ‖squareFunction A‖ := by
  apply (expected_gueMatrixModel_norm_le_eight A₀ A h₀ hA).trans
  have hnonneg : 0 ≤ Real.sqrt ((n : ℝ) * N / M) * Real.sqrt ‖squareFunction A‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

end LehnerEdges

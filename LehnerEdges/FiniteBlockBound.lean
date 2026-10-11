import LehnerEdges.BlockComparison
import LehnerEdges.TraceDuality
import LehnerEdges.GaussianComparison

/-! The deterministic finite-maximum bound for the rectangular comparison
process. No Wishart expectation estimate is built into the statement. -/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace LehnerEdges

theorem stiefel_norm_le_one {N M : ℕ} [NeZero N] (W : Stiefel N M) : ‖W.val‖ ≤ 1 := by
  have hn : ‖W.val‖ ^ 2 = 1 := by
    have h := l2_opNorm_conjTranspose_mul_self W.val.conjTranspose
    rw [conjTranspose_conjTranspose, W.property, norm_one, l2_opNorm_conjTranspose] at h
    nlinarith
  nlinarith [norm_nonneg W.val]

theorem stiefel_pair_le_traceNorm {N M : ℕ} [NeZero N]
    (W : Stiefel N M) (T : Matrix (Fin N) (Fin M) ℂ) :
    frobeniusPair W.val T ≤ traceNorm T := by
  calc _ ≤ |frobeniusPair W.val T| := le_abs_self _
       _ ≤ ‖W.val‖ * traceNorm T := abs_frobeniusPair_le_traceNorm _ _
       _ ≤ 1 * traceNorm T :=
         mul_le_mul_of_nonneg_right (stiefel_norm_le_one W) (traceNorm_nonneg T)
       _ = _ := one_mul _

/-- Uniform control of every finite restriction of the rectangular process,
including its deterministic density drift, by the single stacked Gaussian
norm used in Proposition 5.2. The matrices `Γ` may be arbitrary here. -/
theorem finite_block_process_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    {n N M : ℕ} [NeZero N]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (C : ι → Density N) (W : ι → Stiefel N M)
    (Γ : Fin n → Matrix (Fin N) (Fin M) ℂ) :
    vecMax (fun t => (A₀ * (C t).val).trace.re + (2 / Real.sqrt M) *
      frobeniusPair (W t).val (∑ i, compressed (C t).val (A i) * Γ i)) ≤
      rhoPlus A₀ A + 2 * max (‖blockColumn Γ‖ / Real.sqrt M - 1) 0 *
        Real.sqrt ‖squareFunction A‖ := by
  apply Finset.sup'_le
  intro t _
  calc _ ≤ (A₀ * (C t).val).trace.re + (2 / Real.sqrt M) *
          traceNorm (∑ i, compressed (C t).val (A i) * Γ i) := by
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (stiefel_pair_le_traceNorm (W t) _)
              (div_nonneg (by norm_num) (Real.sqrt_nonneg _)))
       _ ≤ _ := pointwise_comparison_bound A₀ A h₀ hA (C t) Γ

end LehnerEdges

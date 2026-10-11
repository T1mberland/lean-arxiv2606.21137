import LehnerEdges.SpectralResults
import Mathlib.Topology.Order.LiminfLimsup

/-! The asymptotic upper bound of Corollary 1.2 for the finite variational
quantities. Identification of these quantities with free edges is separate. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace LehnerEdges

def gueNormExpectation {n N : ℕ} (A₀ : Mat N) (A : Fin n → Mat N) (M : ℕ) : ℝ :=
  ∫ g, ‖gueMatrixModel A₀ A g‖ ∂stdGaussian (GaussianCoordinates n M M)

theorem squareFunction_norm_le_of_uniform_bound {n N : ℕ}
    (A : Fin n → Mat N) (K : ℝ) (hK : ∀ i, ‖A i‖ ≤ K) :
    ‖squareFunction A‖ ≤ (n : ℝ) * K ^ 2 := by
  calc
    _ ≤ ∑ i, ‖A i ^ 2‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, K ^ 2 := Finset.sum_le_sum (fun i _ =>
      (show ‖A i ^ 2‖ ≤ ‖A i‖ ^ 2 by simpa only [pow_two] using norm_mul_le (A i) (A i)).trans
        (pow_le_pow_left₀ (norm_nonneg _) (hK i) 2))
    _ = _ := by simp

section
variable {n : ℕ} (N : ℕ → ℕ) [∀ k, NeZero (N k)]
  (A₀ : ∀ k, Mat (N k)) (A : ∀ k, Fin n → Mat (N k))
  (h₀ : ∀ k, (A₀ k).IsHermitian) (hA : ∀ k i, (A k i).PosSemidef)
  (K : ℝ) (hK : ∀ k i, ‖A k i‖ ≤ K)
  (hRatio : Tendsto (fun k : ℕ => (N k : ℝ) / (k + 1 : ℕ)) atTop (𝓝 0))

include h₀ hA K hK hRatio

/-- The nonnegative excess above the finite variational edge tends to zero.
The index `k` represents the paper's positive matrix size `M = k + 1`. -/
theorem expected_norm_excess_tendsto_zero :
    Tendsto (fun k => max (gueNormExpectation (A₀ k) (A k) (k + 1) - rhoStar (A₀ k) (A k)) 0)
      atTop (𝓝 0) := by
  have hlimit : Tendsto (fun k : ℕ =>
      8 * Real.sqrt ((n : ℝ) * N k / (k + 1 : ℕ)) * Real.sqrt ((n : ℝ) * K ^ 2))
      atTop (𝓝 0) := by
    have h := ((hRatio.const_mul (n : ℝ)).sqrt.const_mul 8).mul_const
      (Real.sqrt ((n : ℝ) * K ^ 2))
    simpa only [mul_div_assoc, mul_zero, Real.sqrt_zero, zero_mul] using h
  apply squeeze_zero (fun _ => le_max_right _ _) _ hlimit
  intro k
  have hb := expected_gueMatrixModel_norm_le_eight (M := k + 1) (A₀ k) (A k) (h₀ k) (hA k)
  have hs := Real.sqrt_le_sqrt (squareFunction_norm_le_of_uniform_bound (A k) K (hK k))
  have he := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 8 * Real.sqrt ((n : ℝ) * N k / (k + 1 : ℕ)) by positivity)
  change gueNormExpectation (A₀ k) (A k) (k + 1) ≤ _ at hb
  apply max_le
  · linarith
  · positivity

/-- Corollary 1.2 in epsilon form, for finite variational edges. No
boundedness assumption on the deterministic matrices `A₀ k` is required. -/
theorem expected_norm_eventually_le_of_edge_tendsto {ρ : ℝ}
    (hρ : Tendsto (fun k => rhoStar (A₀ k) (A k)) atTop (𝓝 ρ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, gueNormExpectation (A₀ k) (A k) (k + 1) ≤ ρ + ε := by
  have h := hρ.add (expected_norm_excess_tendsto_zero N A₀ A h₀ hA K hK hRatio)
  have he : ∀ᶠ k in atTop,
      rhoStar (A₀ k) (A k) +
        max (gueNormExpectation (A₀ k) (A k) (k + 1) - rhoStar (A₀ k) (A k)) 0 < ρ + ε :=
    (tendsto_order.mp (by simpa only [add_zero] using h)).2 _ (by linarith)
  filter_upwards [he] with k hk
  have hm := le_max_left
    (gueNormExpectation (A₀ k) (A k) (k + 1) - rhoStar (A₀ k) (A k)) 0
  linarith

/-- The limsup conclusion of Corollary 1.2 for the same finite variational
quantities. Nonnegativity of the actual norm expectation supplies the lower
boundedness needed for a real-valued limsup. -/
theorem expected_norm_limsup_le_of_edge_tendsto {ρ : ℝ}
    (hρ : Tendsto (fun k => rhoStar (A₀ k) (A k)) atTop (𝓝 ρ)) :
    limsup (fun k => gueNormExpectation (A₀ k) (A k) (k + 1)) atTop ≤ ρ := by
  have hco : IsCoboundedUnder (· ≤ ·) atTop
      (fun k => gueNormExpectation (A₀ k) (A k) (k + 1)) :=
    isCoboundedUnder_le_of_le atTop (fun _ => integral_nonneg (fun _ => norm_nonneg _))
  have hb : IsBoundedUnder (· ≤ ·) atTop
      (fun k => gueNormExpectation (A₀ k) (A k) (k + 1)) :=
    ⟨ρ + 1, expected_norm_eventually_le_of_edge_tendsto N A₀ A h₀ hA K hK hRatio hρ (by norm_num)⟩
  apply (limsup_le_iff' hco hb).mpr
  intro y hy
  simpa only [add_sub_cancel] using
    expected_norm_eventually_le_of_edge_tendsto N A₀ A h₀ hA K hK hRatio hρ
      (show 0 < y - ρ by linarith)

end
end LehnerEdges

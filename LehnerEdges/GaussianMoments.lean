import LehnerEdges.GaussianConcentration
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! First and second radial moments of the actual standard Gaussian measure.
The bound on the first moment retains the real Hilbert space dimension. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace LehnerEdges

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_integral_norm_sq :
    (∫ x : E, ‖x‖ ^ 2 ∂stdGaussian E) = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hm (i : Fin (Module.finrank ℝ E)) :
      MemLp (innerSL ℝ (b i)) 2 (stdGaussian E) := by
    exact ((IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map (innerSL ℝ (b i))).memLp_two
  have hi (i : Fin (Module.finrank ℝ E)) :
      (∫ x : E, (inner ℝ (b i) x) ^ 2 ∂stdGaussian E) = 1 := by
    have h := variance_eq_sub (hm i)
    rw [variance_dual_stdGaussian, integral_strongDual_stdGaussian,
      innerSL_apply_norm, b.norm_eq_one, one_pow, zero_pow (by decide), sub_zero] at h
    exact h.symm
  simp_rw [← b.sum_sq_inner_right]
  rw [integral_finsetSum]
  · simp [hi]
  · intro i _
    exact (hm i).integrable_sq

theorem stdGaussian_integral_norm_le_sqrt_finrank :
    (∫ x : E, ‖x‖ ∂stdGaussian E) ≤ Real.sqrt (Module.finrank ℝ E) := by
  have hm : MemLp (fun x : E => ‖x‖) 2 (stdGaussian E) := IsGaussian.memLp_two_id.norm
  have hv := variance_nonneg (X := fun x : E => ‖x‖) (μ := stdGaussian E)
  rw [variance_eq_sub hm] at hv
  change 0 ≤ (∫ x : E, ‖x‖ ^ 2 ∂stdGaussian E) - (∫ x : E, ‖x‖ ∂stdGaussian E) ^ 2 at hv
  rw [stdGaussian_integral_norm_sq] at hv
  exact (Real.le_sqrt (integral_nonneg (fun _ => norm_nonneg _)) (Nat.cast_nonneg _)).2
    (by linarith)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem stdGaussian_integral_norm_sq_linearImage (L : E →L[ℝ] F) :
    (∫ x : E, ‖L x‖ ^ 2 ∂stdGaussian E) =
      ∑ i, ‖(innerSL ℝ (stdOrthonormalBasis ℝ F i)).comp L‖ ^ 2 := by
  let b := stdOrthonormalBasis ℝ F
  have hm (i : Fin (Module.finrank ℝ F)) :
      MemLp ((innerSL ℝ (b i)).comp L) 2 (stdGaussian E) :=
    ((IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map
      ((innerSL ℝ (b i)).comp L)).memLp_two
  have hi (i : Fin (Module.finrank ℝ F)) :
      (∫ x : E, (inner ℝ (b i) (L x)) ^ 2 ∂stdGaussian E) =
        ‖(innerSL ℝ (b i)).comp L‖ ^ 2 := by
    have h := variance_eq_sub (hm i)
    rw [variance_dual_stdGaussian, integral_strongDual_stdGaussian,
      zero_pow (by decide), sub_zero] at h
    exact h.symm
  simp_rw [← b.sum_sq_inner_right]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => hi i)
  · exact fun i _ => (hm i).integrable_sq

/-- A Gaussian contraction into a `d` dimensional real Hilbert space has mean
norm at most `sqrt d`; no independence assumptions are left to the caller. -/
theorem stdGaussian_integral_norm_contraction_le (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) :
    (∫ x : E, ‖L x‖ ∂stdGaussian E) ≤ Real.sqrt (Module.finrank ℝ F) := by
  have hm : MemLp (fun x : E => ‖L x‖) 2 (stdGaussian E) :=
    ((IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map L).memLp_two.norm
  have hsq : (∫ x : E, ‖L x‖ ^ 2 ∂stdGaussian E) ≤ Module.finrank ℝ F := by
    rw [stdGaussian_integral_norm_sq_linearImage]
    calc
      _ ≤ ∑ _ : Fin (Module.finrank ℝ F), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have h := ContinuousLinearMap.opNorm_comp_le (innerSL ℝ (stdOrthonormalBasis ℝ F i)) L
        rw [innerSL_apply_norm, (stdOrthonormalBasis ℝ F).norm_eq_one, one_mul] at h
        nlinarith [norm_nonneg ((innerSL ℝ (stdOrthonormalBasis ℝ F i)).comp L)]
      _ = _ := by simp
  have hv := variance_nonneg (X := fun x : E => ‖L x‖) (μ := stdGaussian E)
  rw [variance_eq_sub hm] at hv
  change 0 ≤ (∫ x : E, ‖L x‖ ^ 2 ∂stdGaussian E) -
    (∫ x : E, ‖L x‖ ∂stdGaussian E) ^ 2 at hv
  exact (Real.le_sqrt (integral_nonneg (fun _ => norm_nonneg _)) (Nat.cast_nonneg _)).2
    (by linarith)

end LehnerEdges

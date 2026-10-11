import LehnerEdges.GaussianConcentration

/-! An elementary consequence of the verified Gaussian exponential moment
bound. This avoids a separate layer-cake calculation when only a numerical
bound on a positive deviation is needed. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace LehnerEdges

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A one-Lipschitz Gaussian observable has expected positive centered
deviation at most one. All integrability conclusions follow from Lipschitzness. -/
theorem stdGaussian_integral_positive_centered_le_one {f : E → ℝ}
    (hf : LipschitzWith 1 f) :
    (∫ x, max (f x - ∫ y, f y ∂stdGaussian E) 0 ∂stdGaussian E) ≤ 1 := by
  let m := ∫ y, f y ∂stdGaussian E
  have hmgf := stdGaussian_hasSubgaussianMGF hf
  have hi := (stdGaussian_integrable_of_lipschitz hf).sub (integrable_const m)
  have he : Integrable (fun x => Real.exp (f x - m)) (stdGaussian E) := by
    simpa only [one_mul] using hmgf.integrable_exp_mul 1
  have hb : (∫ x, Real.exp (f x - m) ∂stdGaussian E) ≤ Real.exp (1 / 2 : ℝ) := by
    simpa only [mgf, NNReal.coe_pow, NNReal.coe_one, one_pow, one_mul] using hmgf.mgf_le 1
  calc
    _ ≤ ∫ x, Real.exp (-1 : ℝ) * Real.exp (f x - m) ∂stdGaussian E := by
      apply integral_mono hi.pos_part (he.const_mul _)
      intro x
      change max (f x - m) 0 ≤ Real.exp (-1) * Real.exp (f x - m)
      rw [← Real.exp_add]
      apply max_le
      · have h := Real.add_one_le_exp (-1 + (f x - m))
        linarith
      · exact (Real.exp_pos _).le
    _ = Real.exp (-1 : ℝ) * ∫ x, Real.exp (f x - m) ∂stdGaussian E := integral_const_mul _ _
    _ ≤ Real.exp (-1 : ℝ) * Real.exp (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ ≤ 1 := by rw [← Real.exp_add]; apply Real.exp_le_one_iff.mpr; norm_num

/-- A deterministic upper bound `b + a` on the mean gives a positive excess
above `b` of at most `a + 1`. -/
theorem stdGaussian_integral_positive_excess_le {f : E → ℝ}
    (hf : LipschitzWith 1 f) (a b : ℝ) (ha : 0 ≤ a)
    (hm : (∫ x, f x ∂stdGaussian E) ≤ b + a) :
    (∫ x, max (f x - b) 0 ∂stdGaussian E) ≤ a + 1 := by
  have hi := stdGaussian_integrable_of_lipschitz hf
  have hcenter := (hi.sub (integrable_const (∫ x, f x ∂stdGaussian E))).pos_part
  change Integrable (fun x => max (f x - ∫ y, f y ∂stdGaussian E) 0) (stdGaussian E) at hcenter
  calc
    _ ≤ ∫ x, a + max (f x - ∫ y, f y ∂stdGaussian E) 0 ∂stdGaussian E := by
      apply integral_mono (hi.sub (integrable_const b)).pos_part
        ((integrable_const a).add hcenter)
      intro x
      change max (f x - b) 0 ≤ a + max (f x - ∫ y, f y ∂stdGaussian E) 0
      apply max_le
      · have h := le_max_left (f x - ∫ y, f y ∂stdGaussian E) 0
        linarith
      · exact add_nonneg ha (le_max_right _ _)
    _ = a + ∫ x, max (f x - ∫ y, f y ∂stdGaussian E) 0 ∂stdGaussian E := by
      rw [integral_add (integrable_const a) hcenter, integral_const, probReal_univ, one_smul]
    _ ≤ a + 1 := add_le_add le_rfl (stdGaussian_integral_positive_centered_le_one hf)

end LehnerEdges

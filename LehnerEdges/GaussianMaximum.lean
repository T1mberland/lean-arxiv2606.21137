import LehnerEdges.GaussianPositivePart

/-! The numerical cost of taking the larger of two Gaussian observables.
Neither observable is required to be independent of the other. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace LehnerEdges

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_integral_positive_centered_le {K : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith K f) :
    (∫ x, max (f x - ∫ y, f y ∂stdGaussian E) 0 ∂stdGaussian E) ≤ K := by
  by_cases hK : K = 0
  · have heq : f = fun _ => f 0 := by
      funext x
      apply dist_le_zero.mp
      simpa only [hK, NNReal.coe_zero, zero_mul] using hf.dist_le_mul x 0
    rw [heq]
    simp [hK]
  · have hpos : 0 < (K : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hK)
    have hs : LipschitzWith 1 (fun x => f x / (K : ℝ)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hpos]
      change |f x - f y| / (K : ℝ) ≤ 1 * dist x y
      rw [one_mul, div_le_iff₀ hpos]
      simpa only [Real.dist_eq, mul_comm] using hf.dist_le_mul x y
    have h := stdGaussian_integral_positive_centered_le_one hs
    have heq (x : E) :
        max (f x / (K : ℝ) - ∫ y, f y / (K : ℝ) ∂stdGaussian E) 0 =
          max (f x - ∫ y, f y ∂stdGaussian E) 0 / (K : ℝ) := by
      rw [integral_div, ← sub_div]
      simpa only [zero_div] using max_div_div_right hpos.le
        (f x - ∫ y, f y ∂stdGaussian E) 0
    simp_rw [heq] at h
    rw [integral_div, div_le_iff₀ hpos, one_mul] at h
    exact h

/-- Two `K`-Lipschitz observables whose means are at most `b` have expected
maximum at most `b + 2K`, under the same standard Gaussian measure. -/
theorem stdGaussian_integral_max_le {K : ℝ≥0} {f g : E → ℝ}
    (hf : LipschitzWith K f) (hg : LipschitzWith K g) (b : ℝ)
    (hfb : (∫ x, f x ∂stdGaussian E) ≤ b)
    (hgb : (∫ x, g x ∂stdGaussian E) ≤ b) :
    (∫ x, max (f x) (g x) ∂stdGaussian E) ≤ b + 2 * K := by
  let mf := ∫ x, f x ∂stdGaussian E
  let mg := ∫ x, g x ∂stdGaussian E
  have hi := stdGaussian_integrable_of_lipschitz hf
  have hj := stdGaussian_integrable_of_lipschitz hg
  have hp : Integrable (fun x => max (f x - mf) 0) (stdGaussian E) :=
    (hi.sub (integrable_const mf)).pos_part
  have hq : Integrable (fun x => max (g x - mg) 0) (stdGaussian E) :=
    (hj.sub (integrable_const mg)).pos_part
  have hbp : Integrable (fun x => b + max (f x - mf) 0) (stdGaussian E) :=
    (integrable_const b).add hp
  calc
    _ ≤ ∫ x, b + max (f x - mf) 0 + max (g x - mg) 0 ∂stdGaussian E := by
      apply integral_mono (hi.sup hj) (((integrable_const b).add hp).add hq)
      intro x
      have hpf := le_max_left (f x - mf) 0
      have hpg := le_max_left (g x - mg) 0
      have hpf0 := le_max_right (f x - mf) 0
      have hpg0 := le_max_right (g x - mg) 0
      change mf ≤ b at hfb
      change mg ≤ b at hgb
      change max (f x) (g x) ≤ b + max (f x - mf) 0 + max (g x - mg) 0
      apply max_le <;> linarith
    _ = b + (∫ x, max (f x - mf) 0 ∂stdGaussian E) +
        (∫ x, max (g x - mg) 0 ∂stdGaussian E) := by
      rw [integral_add hbp hq,
        integral_add (integrable_const b) hp, integral_const, probReal_univ, one_smul]
    _ ≤ _ := by
      have h1 := stdGaussian_integral_positive_centered_le hf
      have h2 := stdGaussian_integral_positive_centered_le hg
      change (∫ x, max (f x - mf) 0 ∂stdGaussian E) ≤ K at h1
      change (∫ x, max (g x - mg) 0 ∂stdGaussian E) ≤ K at h2
      linarith

end LehnerEdges

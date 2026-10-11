import LogSobolev.Concentration.Gaussian
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Transport the existing all-Lipschitz Gaussian concentration theorem to
Mathlib's standard Gaussian on any finite-dimensional real Hilbert space.
This includes complex matrix coordinates viewed as a real Hilbert space. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LehnerEdges

theorem standardGaussian_eq_stdGaussian (d : ℕ) :
    LogSobolev.standardGaussian d = stdGaussian (EuclideanSpace ℝ (Fin d)) :=
  map_pi_eq_stdGaussian

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Gaussian integrability for every globally Lipschitz observable on a finite
real Hilbert space, with no caller-supplied moment conditions. -/
theorem stdGaussian_integrable_of_lipschitz {K : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith K f) : Integrable f (stdGaussian E) := by
  let e := (stdOrthonormalBasis ℝ E).repr
  have hg := LogSobolev.gaussian_integrable_of_lipschitz (hf.comp e.symm.lipschitz)
  rw [standardGaussian_eq_stdGaussian, ← stdGaussian_map e] at hg
  have h := (integrable_map_measure hg.aestronglyMeasurable e.continuous.measurable.aemeasurable).mp hg
  simpa only [Function.comp_def, e.symm_apply_apply] using h

/-- Dimension-free Gaussian concentration in any finite-dimensional real
Hilbert space, including zero dimension and zero Lipschitz constant. -/
theorem stdGaussian_hasSubgaussianMGF {K : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith K f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂stdGaussian E) (K ^ 2) (stdGaussian E) := by
  let e := (stdOrthonormalBasis ℝ E).repr
  have hg := LogSobolev.gaussian_hasSubgaussianMGF (hf.comp e.symm.lipschitz)
  rw [standardGaussian_eq_stdGaussian] at hg
  simp only [Function.comp_def, mul_one] at hg
  have hm : (∫ z, f (e.symm z) ∂stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) =
      ∫ y, f y ∂stdGaussian E := by
    rw [← stdGaussian_map e]
    have hi := integral_map (μ := stdGaussian E) (φ := e)
      (f := fun z => f (e.symm z)) e.continuous.measurable.aemeasurable
      (hf.continuous.comp e.symm.continuous).aestronglyMeasurable
    simpa only [e.symm_apply_apply] using hi
  rw [hm] at hg
  have hmap : HasSubgaussianMGF
      (fun z => f (e.symm z) - ∫ y, f y ∂stdGaussian E) (K ^ 2) ((stdGaussian E).map e) := by
    rw [stdGaussian_map e]
    simpa only [Function.comp_def, mul_one] using hg
  have h := HasSubgaussianMGF.of_map e.continuous.measurable.aemeasurable hmap
  simpa only [Function.comp_def, e.symm_apply_apply] using h

theorem stdGaussian_measure_ge_le {K : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith K f) {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian E).real {x | t ≤ f x - ∫ y, f y ∂stdGaussian E} ≤
      Real.exp (-t ^ 2 / (2 * (K : ℝ) ^ 2)) := by
  simpa only [NNReal.coe_pow] using (stdGaussian_hasSubgaussianMGF hf).measure_ge_le ht

end
end LehnerEdges

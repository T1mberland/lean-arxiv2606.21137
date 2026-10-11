import LehnerEdges.Stiefel
import LeanSudakov.SudakovFerniqueDrift
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Linear Gaussian processes and the finite restrictions of the full-process
comparison. The Gaussian laws and their increment variances are constructed,
not assumed. The external drift theorem is used without copying its source. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace LehnerEdges

section ProcessMap
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite Gaussian process realized as linear functionals of one standard
Gaussian vector. No independence is imposed on its coordinates. -/
def processMap (v : ι → E) : E →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => innerSL ℝ (v i))

@[simp] theorem processMap_apply (v : ι → E) (x : E) (i : ι) :
    processMap v x i = ⟪v i, x⟫_ℝ := rfl

end ProcessMap

section LinearGaussian

variable {E F ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem linear_gaussian_comparison (v : ι → E) (w : ι → F)
    (hinc : ∀ i j, ‖v i - v j‖ ^ 2 ≤ ‖w i - w j‖ ^ 2) (a : ι → ℝ) :
    (∫ x, vecMax (a + processMap v x) ∂stdGaussian E) ≤
      ∫ y, vecMax (a + processMap w y) ∂stdGaussian F := by
  let μ := (stdGaussian E).map (processMap v)
  let ν := (stdGaussian F).map (processMap w)
  have hcenterE (i : ι) : ∫ x, x i ∂μ = 0 := by
    rw [integral_map (processMap v).measurable.aemeasurable
      ((measurable_pi_apply i).aestronglyMeasurable)]
    exact integral_strongDual_stdGaussian (innerSL ℝ (v i))
  have hcenterF (i : ι) : ∫ x, x i ∂ν = 0 := by
    rw [integral_map (processMap w).measurable.aemeasurable
      ((measurable_pi_apply i).aestronglyMeasurable)]
    exact integral_strongDual_stdGaussian (innerSL ℝ (w i))
  have hvar (i j : ι) : variance (fun x : ι → ℝ => x i - x j) μ ≤
      variance (fun x : ι → ℝ => x i - x j) ν := by
    rw [variance_map (by fun_prop) (by fun_prop),
      variance_map (by fun_prop) (by fun_prop)]
    have he : (fun x => processMap v x i - processMap v x j) = innerSL ℝ (v i - v j) := by
      ext x; simp
    have hf : (fun x => processMap w x i - processMap w x j) = innerSL ℝ (w i - w j) := by
      ext x; simp
    change variance (fun x => processMap v x i - processMap v x j) _ ≤
      variance (fun x => processMap w x i - processMap w x j) _
    rw [he, hf, variance_dual_stdGaussian, variance_dual_stdGaussian,
      innerSL_apply_norm, innerSL_apply_norm]
    exact hinc i j
  have h := sudakov_fernique_drift μ ν hcenterE hcenterF hvar a
  have hm : AEStronglyMeasurable (fun x : ι → ℝ => vecMax (a + x)) μ :=
    (gaussian_integrable_vecMax_drift μ a).aestronglyMeasurable
  have hn : AEStronglyMeasurable (fun x : ι → ℝ => vecMax (a + x)) ν :=
    (gaussian_integrable_vecMax_drift ν a).aestronglyMeasurable
  rw [integral_map (processMap v).measurable.aemeasurable hm,
    integral_map (processMap w).measurable.aemeasurable hn] at h
  exact h

end LinearGaussian

/-- The real Hilbert space of a family of rectangular complex matrices. Each
complex entry has two real standard Gaussian coordinates under `stdGaussian`. -/
abbrev GaussianCoordinates (n N M : ℕ) :=
  EuclideanSpace ℂ (Fin n × Fin N × Fin M)

def familyVector {n N M : ℕ} (B : Fin n → Matrix (Fin N) (Fin M) ℂ) :
    GaussianCoordinates n N M := WithLp.toLp 2 (fun p => B p.1 p.2.1 p.2.2)

theorem familyVector_norm_sq {n N M : ℕ} (B : Fin n → Matrix (Fin N) (Fin M) ℂ) :
    ‖familyVector B‖ ^ 2 = ∑ i, frobeniusSq (B i) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [familyVector, WithLp.ofLp_toLp, Fintype.sum_prod_type, frobeniusSq_eq_sum]

theorem familyVector_sub {n N M : ℕ} (B D : Fin n → Matrix (Fin N) (Fin M) ℂ) :
    familyVector B - familyVector D = familyVector (fun i => B i - D i) := by
  rfl

/-- Coefficients for the process (6). Isotropic real Gaussian noise paired with
a Hermitian matrix has exactly the paper's GUE variance. -/
def gueCoefficient {n N M : ℕ} (A : Fin n → Mat N) (C : Density N) (W : Stiefel N M) :
    GaussianCoordinates n M M :=
  (1 / Real.sqrt M) • familyVector
    (fun i => W.val.conjTranspose * compressed C.val (A i) * W.val)

/-- Coefficients for process (7). The factor `sqrt 2` combines amplitude `2`
with the `1/sqrt 2` of standard complex Gaussian entries. -/
def complexCoefficient {n N M : ℕ} (A : Fin n → Mat N) (C : Density N) (W : Stiefel N M) :
    GaussianCoordinates n N M :=
  (Real.sqrt 2 / Real.sqrt M) • familyVector (fun i => compressed C.val (A i) * W.val)

theorem coefficient_increment {n N M : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).PosSemidef) (C D : Density N) (W V : Stiefel N M) :
    ‖gueCoefficient A C W - gueCoefficient A D V‖ ^ 2 ≤
      ‖complexCoefficient A C W - complexCoefficient A D V‖ ^ 2 := by
  have h := compressed_increment A hA C D W V
  simp only [gueCoefficient, complexCoefficient, ← smul_sub, familyVector_sub,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, familyVector_norm_sq, div_pow,
    one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  convert mul_le_mul_of_nonneg_left h (sq_nonneg (1 / Real.sqrt M)) using 1 <;>
    simp only [div_pow, one_pow] <;> ring

/-- Every finite restriction of the density–Stiefel comparison, with arbitrary
common deterministic drift. Gaussianity, centering, and increment domination
are all proved for the explicitly constructed laws. -/
theorem finite_density_stiefel_comparison {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {n N M : ℕ}
    (A : Fin n → Mat N) (hA : ∀ i, (A i).PosSemidef)
    (C : ι → Density N) (W : ι → Stiefel N M) (a : ι → ℝ) :
    (∫ x, vecMax (a + processMap (fun t => gueCoefficient A (C t) (W t)) x)
      ∂stdGaussian (GaussianCoordinates n M M)) ≤
    ∫ y, vecMax (a + processMap (fun t => complexCoefficient A (C t) (W t)) y)
      ∂stdGaussian (GaussianCoordinates n N M) := by
  apply linear_gaussian_comparison
  exact fun s t => coefficient_increment A hA (C s) (C t) (W s) (W t)

end LehnerEdges

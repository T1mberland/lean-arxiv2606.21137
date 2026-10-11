import LehnerEdges.ProcessLipschitz
import LeanSudakov.CountableSudakov
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.DenseEmbedding

/-! Extending the verified finite Gaussian comparison to separable continuous
index spaces. Uniform coefficient bounds prove integrability, rather than
leaving moment assumptions to callers. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped NNReal InnerProductSpace Topology
namespace LehnerEdges

section Supremum
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def linearSup (v : ι → E) (a : ι → ℝ) (x : E) : ℝ :=
  sSup (Set.range (fun i => a i + inner ℝ (v i) x))

theorem linearSup_bddAbove (v : ι → E) (a : ι → ℝ) (K : ℝ≥0)
    (hv : ∀ i, ‖v i‖ ≤ K) (ha : BddAbove (Set.range a)) (x : E) :
    BddAbove (Set.range (fun i => a i + inner ℝ (v i) x)) := by
  obtain ⟨B, hB⟩ := ha
  refine ⟨B + K * ‖x‖, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact add_le_add (hB ⟨i, rfl⟩) ((real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hv i) (norm_nonneg x)))

theorem le_linearSup (v : ι → E) (a : ι → ℝ) (K : ℝ≥0)
    (hv : ∀ i, ‖v i‖ ≤ K) (ha : BddAbove (Set.range a)) (x : E) (i : ι) :
    a i + inner ℝ (v i) x ≤ linearSup v a x :=
  le_csSup (linearSup_bddAbove v a K hv ha x) ⟨i, rfl⟩

theorem linearSup_lipschitz [Nonempty ι] (v : ι → E) (a : ι → ℝ) (K : ℝ≥0)
    (hv : ∀ i, ‖v i‖ ≤ K) (ha : BddAbove (Set.range a)) :
    LipschitzWith K (linearSup v a) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨i, rfl⟩
  have hi : LipschitzWith K (innerSL ℝ (v i)) :=
    (innerSL ℝ (v i)).lipschitzWith_of_opNorm_le (by simpa using hv i)
  have h := hi.le_add_mul x y
  have hy := le_linearSup v a K hv ha y i
  change inner ℝ (v i) x ≤ inner ℝ (v i) y + _ at h
  linarith

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem linearSup_integrable [Nonempty ι] (v : ι → E) (a : ι → ℝ) (K : ℝ≥0)
    (hv : ∀ i, ‖v i‖ ≤ K) (ha : BddAbove (Set.range a)) :
    Integrable (linearSup v a) (stdGaussian E) :=
  stdGaussian_integrable_of_lipschitz (linearSup_lipschitz v a K hv ha)

end Supremum

section Approximation
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Countable ι] [DecidableEq ι]

def linearApprox (v : ι → E) (a : ι → ℝ) (i₀ : ι) (n : ℕ) (x : E) : ℝ :=
  countableApproxMax i₀ n (fun i => a i + inner ℝ (v i) x)

theorem linearApprox_eq_vecMax (v : ι → E) (a : ι → ℝ) (i₀ : ι) (n : ℕ) (x : E) :
    linearApprox v a i₀ n x =
      @vecMax {i // i ∈ countableApproxFinset i₀ n} _
        (countableApproxFinset_nonempty i₀ n).to_subtype
        (fun i => a i.val + inner ℝ (v i.val) x) := by
  exact (vecMax_finset_restrict (countableApproxFinset i₀ n)
    (countableApproxFinset_nonempty i₀ n) (fun i => a i + inner ℝ (v i) x)).symm

theorem linearApprox_lipschitz (v : ι → E) (a : ι → ℝ) (K : ℝ≥0)
    (hv : ∀ i, ‖v i‖ ≤ K) (i₀ : ι) (n : ℕ) :
    LipschitzWith K (linearApprox v a i₀ n) := by
  let s := countableApproxFinset i₀ n
  letI : Nonempty {i // i ∈ s} := (countableApproxFinset_nonempty i₀ n).to_subtype
  have h := finite_process_lipschitz (fun i : s => v i.val) (fun i : s => a i.val) K
    (fun i => hv i.val)
  have heq : linearApprox v a i₀ n =
      fun x => vecMax ((fun i : s => a i.val) + processMap (fun i : s => v i.val) x) := by
    funext x
    exact linearApprox_eq_vecMax v a i₀ n x
  rw [heq]
  exact h

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem tendsto_integral_linearApprox [Nonempty ι]
    (v : ι → E) (a : ι → ℝ) (K : ℝ≥0)
    (hv : ∀ i, ‖v i‖ ≤ K) (ha : BddAbove (Set.range a)) (i₀ : ι) :
    Tendsto (fun n => ∫ x, linearApprox v a i₀ n x ∂stdGaussian E)
      atTop (𝓝 (∫ x, linearSup v a x ∂stdGaussian E)) := by
  have hsup := linearSup_integrable v a K hv ha
  have hcoord : Integrable (fun x => a i₀ + inner ℝ (v i₀) x) (stdGaussian E) := by
    exact (integrable_const (a i₀)).add
      (stdGaussian_integrable_of_lipschitz (innerSL ℝ (v i₀)).lipschitzWith)
  refine tendsto_integral_of_dominated_convergence
    (fun x => ‖a i₀ + inner ℝ (v i₀) x‖ + ‖linearSup v a x‖)
    (fun n => (linearApprox_lipschitz v a K hv i₀ n).continuous.aestronglyMeasurable)
    (hcoord.norm.add hsup.norm) ?_ ?_
  · intro n
    exact ae_of_all _ fun x => norm_countableApproxMax_le i₀ n
      (fun i => a i + inner ℝ (v i) x) (linearSup_bddAbove v a K hv ha x)
  · exact ae_of_all _ fun x => countableApproxMax_tendsto_countableSup i₀
      (fun i => a i + inner ℝ (v i) x) (linearSup_bddAbove v a K hv ha x)

end Approximation

section Comparison
variable {E F ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem countable_linear_gaussian_comparison [Countable ι] [Nonempty ι]
    (v : ι → E) (w : ι → F) (a : ι → ℝ) (K L : ℝ≥0)
    (hv : ∀ i, ‖v i‖ ≤ K) (hw : ∀ i, ‖w i‖ ≤ L)
    (ha : BddAbove (Set.range a))
    (hinc : ∀ i j, ‖v i - v j‖ ^ 2 ≤ ‖w i - w j‖ ^ 2) :
    (∫ x, linearSup v a x ∂stdGaussian E) ≤ ∫ y, linearSup w a y ∂stdGaussian F := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  have hx := tendsto_integral_linearApprox v a K hv ha i₀
  have hy := tendsto_integral_linearApprox w a L hw ha i₀
  apply le_of_tendsto_of_tendsto hx hy
  apply Eventually.of_forall
  intro n
  let s := countableApproxFinset i₀ n
  letI : Nonempty {i // i ∈ s} := (countableApproxFinset_nonempty i₀ n).to_subtype
  have h := linear_gaussian_comparison (fun i : s => v i.val) (fun i : s => w i.val)
    (fun i j => hinc i.val j.val) (fun i : s => a i.val)
  change (∫ x, vecMax (fun i : s => a i.val + inner ℝ (v i.val) x) ∂stdGaussian E) ≤
    ∫ y, vecMax (fun i : s => a i.val + inner ℝ (w i.val) y) ∂stdGaussian F at h
  simpa only [linearApprox_eq_vecMax] using h

end Comparison

section DenseRestriction
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace ι] [Nonempty ι]

theorem linearSup_dense_eq (v : ι → E) (a : ι → ℝ) (K : ℝ≥0)
    (hv : ∀ i, ‖v i‖ ≤ K) (ha : BddAbove (Set.range a))
    (cv : Continuous v) (ca : Continuous a) (e : ℕ → ι) (he : DenseRange e) (x : E) :
    linearSup (v ∘ e) (a ∘ e) x = linearSup v a x := by
  have hb := linearSup_bddAbove v a K hv ha x
  have hbe : BddAbove (Set.range (fun n => a (e n) + inner ℝ (v (e n)) x)) :=
    hb.mono (Set.range_comp_subset_range e (fun i => a i + inner ℝ (v i) x))
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n, rfl⟩
    exact le_csSup hb ⟨e n, rfl⟩
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨i, rfl⟩
    refine he.induction_on (p := fun j => a j + inner ℝ (v j) x ≤
      linearSup (v ∘ e) (a ∘ e) x) i ?_ ?_
    · exact isClosed_le (ca.add (cv.inner continuous_const)) continuous_const
    · intro n
      exact le_csSup hbe ⟨n, rfl⟩

end DenseRestriction

section SeparableComparison
variable {E F ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [TopologicalSpace ι] [TopologicalSpace.SeparableSpace ι] [Nonempty ι]

/-- Continuous-index Sudakov–Fernique with drift. The only boundedness
hypotheses are on deterministic coefficients; all Gaussian moment and
measurability properties are proved. Compact continuous families satisfy these
hypotheses automatically. -/
theorem separable_linear_gaussian_comparison
    (v : ι → E) (w : ι → F) (a : ι → ℝ) (K L : ℝ≥0)
    (hv : ∀ i, ‖v i‖ ≤ K) (hw : ∀ i, ‖w i‖ ≤ L)
    (ha : BddAbove (Set.range a))
    (cv : Continuous v) (cw : Continuous w) (ca : Continuous a)
    (hinc : ∀ i j, ‖v i - v j‖ ^ 2 ≤ ‖w i - w j‖ ^ 2) :
    (∫ x, linearSup v a x ∂stdGaussian E) ≤ ∫ y, linearSup w a y ∂stdGaussian F := by
  let e := TopologicalSpace.denseSeq ι
  have he := TopologicalSpace.denseRange_denseSeq ι
  have h := countable_linear_gaussian_comparison (v ∘ e) (w ∘ e) (a ∘ e) K L
    (fun n => hv (e n)) (fun n => hw (e n)) (ha.mono (Set.range_comp_subset_range _ _))
    (fun i j => hinc (e i) (e j))
  simpa only [linearSup_dense_eq v a K hv ha cv ca e he,
    linearSup_dense_eq w a L hw ha cw ca e he] using h

end SeparableComparison
end LehnerEdges

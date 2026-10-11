import LehnerEdges.GaussianComparison
import LehnerEdges.DensityBounds
import LehnerEdges.GaussianConcentration

/-! The exact square-function Lipschitz estimate for finite restrictions of
the spectral process. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace LehnerEdges

theorem sum_frobeniusSq_mul {n N M : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) (S : Matrix (Fin N) (Fin M) ℂ) :
    (∑ i, frobeniusSq (A i * S)) = (S.conjTranspose * squareFunction A * S).trace.re := by
  simp only [frobeniusSq, squareFunction, Matrix.mul_sum, Matrix.sum_mul,
    trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [conjTranspose_mul, (hA i).eq, pow_two, Matrix.mul_assoc]

theorem sum_compressed_frobeniusSq_le {n N : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) (C : Density N) :
    (∑ i, frobeniusSq (compressed C.val (A i))) ≤ ‖squareFunction A‖ := by
  have hC1 : frobeniusSq (CFC.sqrt C.val) = 1 := by
    rw [frobeniusSq_sqrt C.val C.property.1, C.property.2, Complex.one_re]
  have hCop : ‖CFC.sqrt C.val‖ ^ 2 ≤ 1 := by
    simpa only [hC1] using opNorm_sq_le_frobeniusSq (CFC.sqrt C.val)
  have hi (i : Fin n) : frobeniusSq (compressed C.val (A i)) ≤
      frobeniusSq (A i * CFC.sqrt C.val) := by
    calc _ = frobeniusSq (CFC.sqrt C.val * (A i * CFC.sqrt C.val)) := by
           simp only [compressed, Matrix.mul_assoc]
         _ ≤ ‖CFC.sqrt C.val‖ ^ 2 * frobeniusSq (A i * CFC.sqrt C.val) := frobeniusSq_mul_le _ _
         _ ≤ 1 * frobeniusSq (A i * CFC.sqrt C.val) :=
           mul_le_mul_of_nonneg_right hCop (frobeniusSq_nonneg _)
         _ = _ := one_mul _
  calc _ ≤ ∑ i, frobeniusSq (A i * CFC.sqrt C.val) := Finset.sum_le_sum fun i _ => hi i
       _ = (C.val * squareFunction A).trace.re := by
         rw [sum_frobeniusSq_mul A hA, (CFC.sqrt_nonneg C.val).posSemidef.isHermitian.eq,
           trace_mul_cycle, CFC.sqrt_mul_sqrt_self C.val C.property.1.nonneg]
       _ ≤ ‖squareFunction A‖ := density_trace_le_norm C _ (squareFunction_posSemidef A hA).isHermitian

theorem gueCoefficient_norm_le {n N M : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) (C : Density N) (W : Stiefel N M) :
    ‖gueCoefficient A C W‖ ≤ Real.sqrt ‖squareFunction A‖ / Real.sqrt M := by
  have h := sum_compressed_frobeniusSq_le A hA C
  have hs : ‖familyVector (fun i => W.val.conjTranspose * compressed C.val (A i) * W.val)‖ ^ 2 ≤
      ‖squareFunction A‖ := by
    rw [familyVector_norm_sq]
    simpa only [frobeniusSq_mul_coisometry, frobeniusSq_coisometry_adjoint_mul] using h
  have hn := Real.le_sqrt_of_sq_le hs
  simp only [gueCoefficient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg zero_le_one (Real.sqrt_nonneg _))]
  calc _ ≤ (1 / Real.sqrt M) * Real.sqrt ‖squareFunction A‖ :=
         mul_le_mul_of_nonneg_left hn (div_nonneg zero_le_one (Real.sqrt_nonneg _))
       _ = _ := by ring

section FiniteMaximum
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Nonempty ι]

/-- Taking a finite maximum preserves a uniform Lipschitz constant, regardless
of the deterministic drift. -/
theorem finite_process_lipschitz (v : ι → E) (a : ι → ℝ) (K : ℝ≥0)
    (hv : ∀ i, ‖v i‖ ≤ K) :
    LipschitzWith K (fun x => vecMax (a + processMap v x)) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  apply Finset.sup'_le
  intro i _
  have hi : LipschitzWith K (innerSL ℝ (v i)) :=
    (innerSL ℝ (v i)).lipschitzWith_of_opNorm_le (by simpa using hv i)
  have hm : a i + processMap v y i ≤ vecMax (a + processMap v y) :=
    Finset.le_sup' (f := a + processMap v y) (Finset.mem_univ i)
  change a i + processMap v x i ≤ _
  have h := hi.le_add_mul x y
  change processMap v x i ≤ processMap v y i + _ at h
  linarith

end FiniteMaximum

/-- The exact spectral-process Lipschitz constant in Lemma 7.1, for every
finite restriction. Positivity of the coefficients is unnecessary here. -/
theorem finite_spectral_process_lipschitz {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {n N M : ℕ}
    (A : Fin n → Mat N) (hA : ∀ i, (A i).IsHermitian)
    (C : ι → Density N) (W : ι → Stiefel N M) (a : ι → ℝ) :
    LipschitzWith
      ⟨Real.sqrt ‖squareFunction A‖ / Real.sqrt M,
        div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)⟩
      (fun x => vecMax (a + processMap (fun t => gueCoefficient A (C t) (W t)) x)) := by
  apply finite_process_lipschitz
  exact fun t => gueCoefficient_norm_le A hA (C t) (W t)

/-- One-sided Gaussian concentration with the paper's dimension dependence.
For `M > 0` the exponent is `-M*t²/(2*‖∑ Aᵢ²‖)`. The displayed quotient
also handles zero variance using Mathlib's total division convention. -/
theorem finite_spectral_process_concentration {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {n N M : ℕ}
    (A : Fin n → Mat N) (hA : ∀ i, (A i).IsHermitian)
    (C : ι → Density N) (W : ι → Stiefel N M) (a : ι → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    let f := fun x => vecMax (a + processMap (fun j => gueCoefficient A (C j) (W j)) x)
    (stdGaussian (GaussianCoordinates n M M)).real
      {x | t ≤ f x - ∫ y, f y ∂stdGaussian (GaussianCoordinates n M M)} ≤
      Real.exp (-t ^ 2 / (2 * (Real.sqrt ‖squareFunction A‖ / Real.sqrt M) ^ 2)) := by
  exact stdGaussian_measure_ge_le (finite_spectral_process_lipschitz A hA C W a) ht

end LehnerEdges

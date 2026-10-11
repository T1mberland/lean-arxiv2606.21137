import LehnerEdges.RealGaussianComparison
import LehnerEdges.GaussianPositivePart
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Expected operator norm and positive excess of an actual rectangular real
Gaussian matrix. The matrix norm is the Euclidean operator norm throughout. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace Matrix.Norms.L2Operator
namespace LehnerEdges

def realMatrixOfVector {N M : ℕ} (x : EuclideanSpace ℝ (Fin N × Fin M)) :
    Matrix (Fin N) (Fin M) ℝ := fun i j => x (i, j)

theorem exists_realUnit_inner_eq_norm {N : ℕ} [NeZero N]
    (x : EuclideanSpace ℝ (Fin N)) :
    ∃ u : RealUnitSphere N, inner ℝ u.val x = ‖x‖ := by
  classical
  by_cases hx : x = 0
  · exact ⟨Classical.arbitrary _, by simp [hx]⟩
  · refine ⟨⟨‖x‖⁻¹ • x, norm_smul_inv_norm hx⟩, ?_⟩
    rw [inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [conj_trivial]
    field_simp

theorem realOuterVector_inner_mulVec {N M : ℕ}
    (u : EuclideanSpace ℝ (Fin N)) (v : EuclideanSpace ℝ (Fin M))
    (x : EuclideanSpace ℝ (Fin N × Fin M)) :
    inner ℝ (realOuterVector u v) x =
      inner ℝ u ((EuclideanSpace.equiv (Fin N) ℝ).symm (realMatrixOfVector x *ᵥ v)) := by
  simp only [PiLp.inner_apply, Real.inner_apply]
  change (∑ ij : Fin N × Fin M, (u ij.1 * v ij.2) * x ij) =
    ∑ i : Fin N, u i * ∑ j : Fin M, x (i, j) * v j
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realOuterVector_unit_norm {N M : ℕ} (p : RealUnitSphere N × RealUnitSphere M) :
    ‖realOuterVector p.1.val p.2.val‖ ≤ 1 := by
  have h := realOuterVector_norm_sq p.1.val p.2.val
  simp only [p.1.property, p.2.property, one_pow, mul_one] at h
  nlinarith [norm_nonneg (realOuterVector p.1.val p.2.val)]

theorem real_matrix_process_eq_norm {N M : ℕ} [NeZero N] [NeZero M]
    (x : EuclideanSpace ℝ (Fin N × Fin M)) :
    linearSup (fun p : RealUnitSphere N × RealUnitSphere M =>
      realOuterVector p.1.val p.2.val) (fun _ => 0) x = ‖realMatrixOfVector x‖ := by
  let L := (Matrix.toEuclideanLin (realMatrixOfVector x)).toContinuousLinearMap
  have hb : BddAbove (Set.range (fun _ : RealUnitSphere N × RealUnitSphere M => (0 : ℝ))) :=
    ⟨0, by rintro _ ⟨p, rfl⟩; exact le_rfl⟩
  have hv (v : RealUnitSphere M) : ‖L v.val‖ ≤
      linearSup (fun p : RealUnitSphere N × RealUnitSphere M =>
        realOuterVector p.1.val p.2.val) (fun _ => 0) x := by
    obtain ⟨u, hu⟩ := exists_realUnit_inner_eq_norm (L v.val)
    have h := le_linearSup
      (fun p : RealUnitSphere N × RealUnitSphere M => realOuterVector p.1.val p.2.val)
      (fun _ => 0) 1 realOuterVector_unit_norm hb x (u, v)
    change 0 + inner ℝ (realOuterVector u.val v.val) x ≤ _ at h
    rw [zero_add, realOuterVector_inner_mulVec] at h
    exact hu ▸ h
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨p, rfl⟩
    change 0 + inner ℝ (realOuterVector p.1.val p.2.val) x ≤ _
    rw [zero_add, realOuterVector_inner_mulVec]
    calc
      _ ≤ ‖p.1.val‖ * ‖L p.2.val‖ := real_inner_le_norm _ _
      _ ≤ ‖realMatrixOfVector x‖ := by
        rw [p.1.property, one_mul]
        change ‖L p.2.val‖ ≤ ‖L‖
        simpa only [p.2.property, mul_one] using L.le_opNorm p.2.val
  · change ‖L‖ ≤ _
    apply ContinuousLinearMap.opNorm_le_of_unit_norm
    · exact (norm_nonneg (L (Classical.arbitrary (RealUnitSphere M)).val)).trans
        (hv (Classical.arbitrary _))
    · intro v hv'
      exact hv ⟨v, hv'⟩

theorem real_gaussian_matrix_norm_mean_le {N M : ℕ} [NeZero N] [NeZero M] :
    (∫ x, ‖realMatrixOfVector x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin N × Fin M))) ≤
      Real.sqrt N + Real.sqrt M := by
  simpa only [real_matrix_process_eq_norm] using real_matrix_process_mean_le (N := N) (M := M)

theorem realMatrixOfVector_norm_lipschitz {N M : ℕ} [NeZero N] [NeZero M] :
    LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin N × Fin M) => ‖realMatrixOfVector x‖) := by
  have h := linearSup_lipschitz
    (fun p : RealUnitSphere N × RealUnitSphere M => realOuterVector p.1.val p.2.val)
    (fun _ => 0) 1 realOuterVector_unit_norm
    ⟨0, by rintro _ ⟨p, rfl⟩; exact le_rfl⟩
  have heq : (linearSup (fun p : RealUnitSphere N × RealUnitSphere M =>
      realOuterVector p.1.val p.2.val) (fun _ => 0)) =
      (fun x => ‖realMatrixOfVector x‖) := funext real_matrix_process_eq_norm
  rw [heq] at h
  exact h

/-- Positive excess above `sqrt M`, with explicit dimension dependence. -/
theorem real_gaussian_matrix_positive_excess_le {N M : ℕ} [NeZero N] [NeZero M] :
    (∫ x, max (‖realMatrixOfVector x‖ - Real.sqrt M) 0
      ∂stdGaussian (EuclideanSpace ℝ (Fin N × Fin M))) ≤ Real.sqrt N + 1 := by
  apply stdGaussian_integral_positive_excess_le realMatrixOfVector_norm_lipschitz
    (Real.sqrt N) (Real.sqrt M) (Real.sqrt_nonneg _)
  simpa only [add_comm] using real_gaussian_matrix_norm_mean_le (N := N) (M := M)

end LehnerEdges

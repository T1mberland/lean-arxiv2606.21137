import LehnerEdges.ComplexGaussianNorm
import LehnerEdges.PurificationBound

/-! Stacking an independent rectangular Gaussian family is a coordinate
isometry of the underlying real standard Gaussian spaces. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Matrix.Norms.L2Operator
namespace LehnerEdges

def gaussianBlockEquiv (n N M : ℕ) :
    (Fin n × Fin N × Fin M) ≃ (Fin (n * N) × Fin M) where
  toFun := fun p => (finProdFinEquiv (p.1, p.2.1), p.2.2)
  invFun := fun p => ((finProdFinEquiv.symm p.1).1, (finProdFinEquiv.symm p.1).2, p.2)
  left_inv := by intro p; simp
  right_inv := by
    intro p
    apply Prod.ext
    · change finProdFinEquiv (finProdFinEquiv.symm p.1) = p.1
      exact Equiv.apply_symm_apply _ _
    · rfl

def gaussianBlockIsometry (n N M : ℕ) :
    GaussianCoordinates n N M ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (n * N) × Fin M) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℂ (gaussianBlockEquiv n N M)

theorem gaussianBlock_matrix {n N M : ℕ} (g : GaussianCoordinates n N M) :
    blockColumn (fun i => (1 / Real.sqrt 2 : ℝ) • familyMatrices g i) =
      complexGaussianMatrix (gaussianBlockIsometry n N M g) := rfl

theorem gaussianBlock_normalized_excess_le {n N M : ℕ} [NeZero n] [NeZero N] [NeZero M] :
    (∫ g, max (‖blockColumn (fun i => (1 / Real.sqrt 2 : ℝ) • familyMatrices g i)‖ /
        Real.sqrt M - 1) 0 ∂stdGaussian (GaussianCoordinates n N M)) ≤
      (Real.sqrt ((n * N : ℕ) * 2) + 1) / Real.sqrt M := by
  haveI : NeZero (n * N) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne N)⟩
  rw [show (fun g : GaussianCoordinates n N M =>
      max (‖blockColumn (fun i => (1 / Real.sqrt 2 : ℝ) • familyMatrices g i)‖ / Real.sqrt M - 1) 0) =
      (fun g => max (‖complexGaussianMatrix (gaussianBlockIsometry n N M g)‖ / Real.sqrt M - 1) 0) from
      funext (fun g => by rw [gaussianBlock_matrix])]
  have heq : (∫ g : GaussianCoordinates n N M,
      max (‖complexGaussianMatrix (gaussianBlockIsometry n N M g)‖ / Real.sqrt M - 1) 0
        ∂stdGaussian _) =
      ∫ x, max (‖complexGaussianMatrix x‖ / Real.sqrt M - 1) 0
        ∂stdGaussian (EuclideanSpace ℂ (Fin (n * N) × Fin M)) := by
    rw [← stdGaussian_map (gaussianBlockIsometry n N M)]
    symm
    apply integral_map (gaussianBlockIsometry n N M).continuous.measurable.aemeasurable
    exact (by unfold complexGaussianMatrix matrixOfVector; fun_prop :
      Continuous (fun x : EuclideanSpace ℂ (Fin (n * N) × Fin M) =>
        max (‖complexGaussianMatrix x‖ / Real.sqrt M - 1) 0)).aestronglyMeasurable
  rw [heq]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    complex_gaussian_normalized_excess_le (N := n * N) (M := M)

end LehnerEdges

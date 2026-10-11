import LehnerEdges.Purification
import LehnerEdges.CompactComparison
import LehnerEdges.GaussianMatrices

/-! Full continuous Gaussian comparison on the Frobenius unit sphere. The
polar contraction proof handles singular purifications without basis extension. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace LehnerEdges

abbrev UnitPurification (N M : ℕ) :=
  {x : EuclideanSpace ℂ (Fin N × Fin M) // ‖x‖ = 1}

instance unitPurification_nonempty {N M : ℕ} [NeZero N] [NeZero M] :
    Nonempty (UnitPurification N M) := by
  refine ⟨⟨EuclideanSpace.single (0, 0) 1, ?_⟩⟩
  simp

def purificationMatrix {N M : ℕ} (u : UnitPurification N M) : Matrix (Fin N) (Fin M) ℂ :=
  matrixOfVector u.val

theorem purificationMatrix_frobeniusSq {N M : ℕ} (u : UnitPurification N M) :
    frobeniusSq (purificationMatrix u) = 1 := by
  rw [← matrixVector_norm_sq]
  change ‖u.val‖ ^ 2 = 1
  rw [u.property, one_pow]

theorem continuous_purificationMatrix {N M : ℕ} :
    Continuous (purificationMatrix (N := N) (M := M)) := by
  unfold purificationMatrix matrixOfVector
  fun_prop

def purificationDrift {N M : ℕ} (A₀ : Mat N) (u : UnitPurification N M) : ℝ :=
  (A₀ * (purificationMatrix u * (purificationMatrix u).conjTranspose)).trace.re

theorem continuous_purificationDrift {N M : ℕ} (A₀ : Mat N) :
    Continuous (purificationDrift (M := M) A₀) := by
  have h := continuous_purificationMatrix (N := N) (M := M)
  unfold purificationDrift
  fun_prop

theorem purificationDrift_bddAbove {N M : ℕ} (A₀ : Mat N) (h₀ : A₀.IsHermitian) :
    BddAbove (Set.range (purificationDrift (M := M) A₀)) := by
  refine ⟨‖A₀‖, ?_⟩
  rintro _ ⟨u, rfl⟩
  have h := density_trace_le_norm
    (purificationDensity (purificationMatrix u) (purificationMatrix_frobeniusSq u)) A₀ h₀
  change (A₀ * (purificationMatrix u * (purificationMatrix u).conjTranspose)).trace.re ≤ ‖A₀‖
  rw [trace_mul_comm]
  exact h

/-- Full continuous-index comparison on unit Frobenius matrices, with the
paper's deterministic density drift and exact GUE/complex Gaussian scaling.
There are no assumed moment bounds or supremum measurability hypotheses. -/
theorem full_purification_comparison {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).PosSemidef) :
    (∫ x, linearSup (fun u : UnitPurification N M =>
        purificationGueCoefficient A (purificationMatrix u)) (purificationDrift A₀) x
      ∂stdGaussian (GaussianCoordinates n M M)) ≤
    ∫ y, linearSup (fun u : UnitPurification N M =>
        purificationComplexCoefficient A (purificationMatrix u)) (purificationDrift A₀) y
      ∂stdGaussian (GaussianCoordinates n N M) := by
  apply separable_linear_gaussian_comparison _ _ _
    ⟨Real.sqrt ‖squareFunction A‖ / Real.sqrt M,
      div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)⟩
    ⟨(Real.sqrt 2 / Real.sqrt M) * Real.sqrt ‖squareFunction A‖,
      mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)⟩
  · exact fun u => purificationGueCoefficient_norm_le A (fun i => (hA i).isHermitian)
      (purificationMatrix u) (purificationMatrix_frobeniusSq u)
  · exact fun u => purificationComplexCoefficient_norm_le A (fun i => (hA i).isHermitian)
      (purificationMatrix u) (purificationMatrix_frobeniusSq u)
  · exact purificationDrift_bddAbove A₀ h₀
  · exact (continuous_purificationGueCoefficient A).comp continuous_purificationMatrix
  · exact (continuous_purificationComplexCoefficient A).comp continuous_purificationMatrix
  · exact continuous_purificationDrift A₀
  · exact fun u v => purification_coefficient_increment A hA
      (purificationMatrix u) (purificationMatrix v)

end LehnerEdges

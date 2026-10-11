import LehnerEdges.GueModel
import LehnerEdges.GaussianEdgeComparison

/-! The exact matrix norm is the maximum of the two full quadratic Gaussian
processes. In particular, neither spectral edge is defined by a surrogate. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace LehnerEdges

def spectralScale {n N : ℕ} (A : Fin n → Mat N) (M : ℕ) : ℝ≥0 :=
  ⟨Real.sqrt ‖squareFunction A‖ / Real.sqrt M,
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)⟩

def quadraticGueSup {n N M : ℕ} (A₀ : Mat N) (A : Fin n → Mat N)
    (g : GaussianCoordinates n M M) : ℝ :=
  linearSup (fun u : UnitPurification N M => purificationGueCoefficient A (purificationMatrix u))
    (purificationDrift A₀) g

theorem quadraticGueSup_lipschitz {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) :
    LipschitzWith (spectralScale A M) (quadraticGueSup (M := M) A₀ A) := by
  apply linearSup_lipschitz _ _ _
  · exact fun u => purificationGueCoefficient_norm_le A hA
      (purificationMatrix u) (purificationMatrix_frobeniusSq u)
  · exact purificationDrift_bddAbove A₀ h₀

theorem le_quadraticGueSup {n N M : ℕ} [NeZero N]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (g : GaussianCoordinates n M M) (u : UnitPurification N M) :
    purificationDrift A₀ u + inner ℝ (purificationGueCoefficient A (purificationMatrix u)) g ≤
      quadraticGueSup A₀ A g := by
  apply le_linearSup _ _ (spectralScale A M)
  · exact fun u => purificationGueCoefficient_norm_le A hA
      (purificationMatrix u) (purificationMatrix_frobeniusSq u)
  · exact purificationDrift_bddAbove A₀ h₀

theorem purificationDrift_neg {N M : ℕ} (A₀ : Mat N) (u : UnitPurification N M) :
    purificationDrift (-A₀) u = -purificationDrift A₀ u := by
  simp only [purificationDrift, Matrix.neg_mul, trace_neg, Complex.neg_re]

theorem transposedGueMatrixModel_negative_rayleigh {n N M : ℕ}
    (A₀ : Mat N) (A : Fin n → Mat N) (hA : ∀ i, (A i).IsHermitian)
    (g : GaussianCoordinates n M M) (u : UnitPurification N M) :
    -matrixRayleigh (transposedGueMatrixModel A₀ A g) u =
      purificationDrift (-A₀) u + inner ℝ (purificationGueCoefficient A (purificationMatrix u)) (-g) := by
  rw [transposedGueMatrixModel_rayleigh A₀ A hA, purificationDrift_neg, inner_neg_right]
  ring

theorem transposedGueMatrixModel_norm_eq_max {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (g : GaussianCoordinates n M M) :
    ‖transposedGueMatrixModel A₀ A g‖ =
      max (quadraticGueSup A₀ A g) (quadraticGueSup (-A₀) A (-g)) := by
  apply le_antisymm
  · rw [opNorm_eq_signed_rayleigh_sup (transposedGueMatrixModel_hermitian A₀ A h₀ hA g)]
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨p, rfl⟩
    cases hb : p.1
    · simp only [signedMatrixRayleigh, signVector, hb, Bool.false_eq_true, ↓reduceIte]
      rw [transposedGueMatrixModel_negative_rayleigh A₀ A hA]
      exact (le_quadraticGueSup (-A₀) A h₀.neg hA (-g) p.2).trans (le_max_right _ _)
    · simp only [signedMatrixRayleigh, signVector, hb, ↓reduceIte]
      rw [transposedGueMatrixModel_rayleigh A₀ A hA]
      exact (le_quadraticGueSup A₀ A h₀ hA g p.2).trans (le_max_left _ _)
  · apply max_le
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨u, rfl⟩
      change purificationDrift A₀ u + inner ℝ (purificationGueCoefficient A (purificationMatrix u)) g ≤ _
      rw [← transposedGueMatrixModel_rayleigh A₀ A hA]
      exact (le_abs_self _).trans (abs_matrixRayleigh_le_norm _ _)
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨u, rfl⟩
      change purificationDrift (-A₀) u + inner ℝ (purificationGueCoefficient A (purificationMatrix u)) (-g) ≤ _
      rw [← transposedGueMatrixModel_negative_rayleigh A₀ A hA]
      exact (neg_le_abs _).trans (abs_matrixRayleigh_le_norm _ _)

theorem quadraticGueSup_neg_lipschitz {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) :
    LipschitzWith (spectralScale A M) (fun g : GaussianCoordinates n M M => quadraticGueSup A₀ A (-g)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_neg_neg] using (quadraticGueSup_lipschitz A₀ A h₀ hA).dist_le_mul (-x) (-y)

theorem integral_quadraticGueSup_neg {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) :
    (∫ g : GaussianCoordinates n M M, quadraticGueSup A₀ A (-g) ∂stdGaussian _) =
      ∫ g : GaussianCoordinates n M M, quadraticGueSup A₀ A g ∂stdGaussian _ := by
  conv_rhs => rw [← stdGaussian_map (LinearIsometryEquiv.neg ℝ (E := GaussianCoordinates n M M))]
  symm
  exact integral_map (LinearIsometryEquiv.neg ℝ).continuous.measurable.aemeasurable
    (quadraticGueSup_lipschitz A₀ A h₀ hA).continuous.aestronglyMeasurable

end LehnerEdges

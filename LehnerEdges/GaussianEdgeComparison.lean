import LehnerEdges.GaussianBlock

/-! Integrating the full purification comparison. The left-hand quantity is
the continuous quadratic Gaussian supremum; its identification with the
spectral edge of the Kronecker matrix model is a separate step. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace LehnerEdges

def gaussianBlockExcess {n N M : ℕ} (g : GaussianCoordinates n N M) : ℝ :=
  max (‖blockColumn (fun i => (1 / Real.sqrt 2 : ℝ) • familyMatrices g i)‖ / Real.sqrt M - 1) 0

theorem gaussianBlockExcess_integrable {n N M : ℕ} :
    Integrable (gaussianBlockExcess (n := n) (N := N) (M := M)) (stdGaussian _) := by
  have hi : Integrable (fun g : GaussianCoordinates n N M =>
      ‖complexGaussianMatrix (gaussianBlockIsometry n N M g)‖) (stdGaussian _) :=
    stdGaussian_integrable_of_lipschitz
      (complexGaussianMatrix_norm_lipschitz.comp (gaussianBlockIsometry n N M).lipschitz)
  unfold gaussianBlockExcess
  simp_rw [gaussianBlock_matrix]
  exact ((hi.div_const (Real.sqrt M)).sub (integrable_const 1)).pos_part

theorem purificationComplexSup_integrable {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) :
    Integrable (linearSup (fun u : UnitPurification N M =>
        purificationComplexCoefficient A (purificationMatrix u)) (purificationDrift A₀))
      (stdGaussian (GaussianCoordinates n N M)) := by
  apply linearSup_integrable _ _
    ⟨(Real.sqrt 2 / Real.sqrt M) * Real.sqrt ‖squareFunction A‖,
      mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)⟩
  · exact fun u => purificationComplexCoefficient_norm_le A hA
      (purificationMatrix u) (purificationMatrix_frobeniusSq u)
  · exact purificationDrift_bddAbove A₀ h₀

theorem purificationComplexSup_pointwise {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (g : GaussianCoordinates n N M) :
    linearSup (fun u : UnitPurification N M =>
        purificationComplexCoefficient A (purificationMatrix u)) (purificationDrift A₀) g ≤
      rhoPlus A₀ A + 2 * gaussianBlockExcess g * Real.sqrt ‖squareFunction A‖ := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨u, rfl⟩
  exact purification_comparison_pointwise A₀ A h₀ hA u g

/-- An integrated edge-process bound with explicit constants, proved using
real Gaussian domination rather than assuming a complex Chevet theorem. -/
theorem gaussian_purification_edge_bound {n N M : ℕ} [NeZero n] [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).PosSemidef) :
    (∫ x, linearSup (fun u : UnitPurification N M =>
        purificationGueCoefficient A (purificationMatrix u)) (purificationDrift A₀) x
      ∂stdGaussian (GaussianCoordinates n M M)) ≤
      rhoPlus A₀ A + 2 * ((Real.sqrt ((n * N : ℕ) * 2) + 1) / Real.sqrt M) *
        Real.sqrt ‖squareFunction A‖ := by
  apply (full_purification_comparison A₀ A h₀ hA).trans
  have hi := gaussianBlockExcess_integrable (n := n) (N := N) (M := M)
  calc
    _ ≤ ∫ g : GaussianCoordinates n N M,
        rhoPlus A₀ A + 2 * gaussianBlockExcess g * Real.sqrt ‖squareFunction A‖ ∂stdGaussian _ :=
      integral_mono (purificationComplexSup_integrable A₀ A h₀ (fun i => (hA i).isHermitian))
        ((integrable_const _).add ((hi.const_mul 2).mul_const _))
        (purificationComplexSup_pointwise A₀ A h₀ (fun i => (hA i).isHermitian))
    _ = rhoPlus A₀ A + 2 * (∫ g, gaussianBlockExcess g ∂stdGaussian _) *
        Real.sqrt ‖squareFunction A‖ := by
      rw [integral_add (integrable_const _) ((hi.const_mul 2).mul_const _),
        integral_const, probReal_univ, one_smul, integral_mul_const, integral_const_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left gaussianBlock_normalized_excess_le (by norm_num)) (Real.sqrt_nonneg _))

theorem realification_error_le_six (d m : ℝ) (hd : 1 ≤ d) (hm : 0 ≤ m) :
    2 * ((Real.sqrt (d * 2) + 1) / Real.sqrt m) ≤ 6 * Real.sqrt (d / m) := by
  have hd0 : 0 ≤ d := by linarith
  have hone : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd
  have htwo : Real.sqrt 2 ≤ (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hrow : Real.sqrt (d * 2) ≤ 2 * Real.sqrt d := by
    rw [Real.sqrt_mul hd0]
    nlinarith [mul_le_mul_of_nonneg_left htwo (Real.sqrt_nonneg d)]
  calc
    _ = (2 * (Real.sqrt (d * 2) + 1)) / Real.sqrt m := by ring
    _ ≤ (6 * Real.sqrt d) / Real.sqrt m :=
      div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_div hd0 m]; ring

/-- The positive-part Wishart expectation in Lemma 5.1, with its explicit
constant three. This alternative proof uses realification and Gaussian
exponential moments, and does not assume the sharp complex mean estimate. -/
theorem gaussian_wishart_positive_excess_le_three {N M : ℕ} [NeZero N] [NeZero M] :
    (∫ g, max (Real.sqrt ‖wishartMatrix (complexGaussianMatrix g)‖ - 1) 0
      ∂stdGaussian (EuclideanSpace ℂ (Fin N × Fin M))) ≤
      3 * Real.sqrt ((N : ℝ) / M) := by
  simp_rw [wishart_sqrt_norm]
  apply complex_gaussian_normalized_excess_le.trans
  have h := realification_error_le_six (N : ℝ) M
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) (Nat.cast_nonneg M)
  linarith

/-- The explicit constant six for the full quadratic process. Identifying
this left-hand process with the Kronecker matrix edge remains separate. -/
theorem gaussian_purification_edge_bound_six {n N M : ℕ} [NeZero n] [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).PosSemidef) :
    (∫ x, linearSup (fun u : UnitPurification N M =>
        purificationGueCoefficient A (purificationMatrix u)) (purificationDrift A₀) x
      ∂stdGaussian (GaussianCoordinates n M M)) ≤
      rhoPlus A₀ A + 6 * Real.sqrt ((n : ℝ) * N / M) * Real.sqrt ‖squareFunction A‖ := by
  apply (gaussian_purification_edge_bound A₀ A h₀ hA).trans
  apply add_le_add le_rfl
  rw [mul_assoc (2 : ℝ)]
  have hd : 1 ≤ (n : ℝ) * N := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne N))
  have he := realification_error_le_six ((n : ℝ) * N) M hd (Nat.cast_nonneg M)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using
    mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg ‖squareFunction A‖)

end LehnerEdges

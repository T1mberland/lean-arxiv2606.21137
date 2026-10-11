import LehnerEdges.RealGaussianNorm
import LehnerEdges.Realification
import LehnerEdges.Wishart

/-! A real Gaussian domination of the standard complex Gaussian matrix norm.
The column term remains exactly `sqrt M`; only the row dimension is doubled. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Matrix.Norms.L2Operator
namespace LehnerEdges

def realStackEquiv (N M : ℕ) : ((Fin N × Fin M) × Fin 2) ≃ (Fin (N * 2) × Fin M) where
  toFun := fun p => (finProdFinEquiv (p.1.1, p.2), p.1.2)
  invFun := fun p => (((finProdFinEquiv.symm p.1).1, p.2), (finProdFinEquiv.symm p.1).2)
  left_inv := by intro p; simp
  right_inv := by
    intro p
    apply Prod.ext
    · change finProdFinEquiv (finProdFinEquiv.symm p.1) = p.1
      exact Equiv.apply_symm_apply _ _
    · rfl

def complexGaussianRealStack (N M : ℕ) :
    EuclideanSpace ℂ (Fin N × Fin M) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (N * 2) × Fin M) :=
  (complexRealification (Fin N × Fin M)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (realStackEquiv N M))

theorem complexGaussianRealStack_apply {N M : ℕ}
    (g : EuclideanSpace ℂ (Fin N × Fin M)) (i : Fin N) (j : Fin M) (k : Fin 2) :
    complexGaussianRealStack N M g (finProdFinEquiv (i, k), j) =
      complexRealification (Fin N × Fin M) g ((i, j), k) := by
  change complexRealification (Fin N × Fin M) g
    ((realStackEquiv N M).symm (finProdFinEquiv (i, k), j)) = _
  exact congrArg (fun p => complexRealification (Fin N × Fin M) g p)
    ((realStackEquiv N M).symm_apply_apply ((i, j), k))

def mixingMatrix (N : ℕ) : Matrix (Fin N) (Fin (N * 2)) ℂ :=
  fun i k => if i = (finProdFinEquiv.symm k).1 then
    (if (finProdFinEquiv.symm k).2 = 0 then 1 else Complex.I) else 0

theorem mixingMatrix_gram (N : ℕ) :
    mixingMatrix N * (mixingMatrix N).conjTranspose = (2 : ℝ) • (1 : Mat N) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin N × Fin 2 ≃ Fin (N * 2))]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, mixingMatrix, Equiv.symm_apply_apply]
  calc
    _ = ∑ k : Fin N, if i = k then (if j = k then (2 : ℂ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hik : i = k <;> by_cases hjk : j = k <;> norm_num [hik, hjk]
    _ = _ := by simp [Matrix.one_apply, eq_comm]

theorem mixingMatrix_norm {N : ℕ} [NeZero N] : ‖mixingMatrix N‖ = Real.sqrt 2 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (mixingMatrix N).conjTranspose
  rw [conjTranspose_conjTranspose, mixingMatrix_gram, norm_smul, Real.norm_ofNat,
    norm_one, mul_one, l2_opNorm_conjTranspose] at h
  rw [← pow_two] at h
  rw [← Real.sqrt_sq (norm_nonneg (mixingMatrix N)), ← h]

theorem complexGaussianMatrix_eq_mixing {N M : ℕ}
    (g : EuclideanSpace ℂ (Fin N × Fin M)) :
    complexGaussianMatrix g = (1 / Real.sqrt 2 : ℝ) •
      (mixingMatrix N * (realMatrixOfVector (complexGaussianRealStack N M g)).map Complex.ofReal) := by
  unfold complexGaussianMatrix
  apply congrArg (fun T : Matrix (Fin N) (Fin M) ℂ => (1 / Real.sqrt 2 : ℝ) • T)
  ext i j
  simp only [Matrix.mul_apply]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin N × Fin 2 ≃ Fin (N * 2))]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, mixingMatrix, Equiv.symm_apply_apply]
  simp [realMatrixOfVector, complexGaussianRealStack_apply, matrixOfVector,
    mul_ite, ite_mul, Finset.sum_add_distrib, eq_comm, Complex.re_add_im, mul_comm Complex.I]

theorem complexGaussianMatrix_norm_le_realStack {N M : ℕ} [NeZero N]
    (g : EuclideanSpace ℂ (Fin N × Fin M)) :
    ‖complexGaussianMatrix g‖ ≤ ‖realMatrixOfVector (complexGaussianRealStack N M g)‖ := by
  rw [complexGaussianMatrix_eq_mixing, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg zero_le_one (Real.sqrt_nonneg _))]
  calc
    _ ≤ (1 / Real.sqrt 2) * (‖mixingMatrix N‖ *
        ‖(realMatrixOfVector (complexGaussianRealStack N M g)).map Complex.ofReal‖) :=
      mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _)
        (div_nonneg zero_le_one (Real.sqrt_nonneg _))
    _ ≤ (1 / Real.sqrt 2) * (Real.sqrt 2 *
        ‖realMatrixOfVector (complexGaussianRealStack N M g)‖) := by
      rw [mixingMatrix_norm]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (complexify_opNorm_le _) (Real.sqrt_nonneg _))
        (div_nonneg zero_le_one (Real.sqrt_nonneg _))
    _ = _ := by field_simp

theorem integral_realStack_norm {N M : ℕ} :
    (∫ g, ‖realMatrixOfVector (complexGaussianRealStack N M g)‖
      ∂stdGaussian (EuclideanSpace ℂ (Fin N × Fin M))) =
    ∫ x, ‖realMatrixOfVector x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin (N * 2) × Fin M)) := by
  rw [← stdGaussian_map (complexGaussianRealStack N M)]
  symm
  apply integral_map (complexGaussianRealStack N M).continuous.measurable.aemeasurable
  exact (show Continuous (fun x : EuclideanSpace ℝ (Fin (N * 2) × Fin M) =>
    ‖realMatrixOfVector x‖) by unfold realMatrixOfVector; fun_prop).aestronglyMeasurable

/-- A sufficient realification estimate: the column constant is one and the
real row dimension is `2N`. This is weaker than the sharp complex Chevet bound. -/
theorem complex_gaussian_matrix_norm_mean_le {N M : ℕ} [NeZero N] [NeZero M] :
    (∫ g, ‖complexGaussianMatrix g‖ ∂stdGaussian (EuclideanSpace ℂ (Fin N × Fin M))) ≤
      Real.sqrt (N * 2) + Real.sqrt M := by
  haveI : NeZero (N * 2) := ⟨Nat.mul_ne_zero (NeZero.ne N) (by decide)⟩
  have hreal : Integrable (fun g : EuclideanSpace ℂ (Fin N × Fin M) =>
      ‖realMatrixOfVector (complexGaussianRealStack N M g)‖) (stdGaussian _) :=
    stdGaussian_integrable_of_lipschitz
      (realMatrixOfVector_norm_lipschitz.comp (complexGaussianRealStack N M).lipschitz)
  calc
    _ ≤ _ := integral_mono
      (stdGaussian_integrable_of_lipschitz complexGaussianMatrix_norm_lipschitz)
      hreal complexGaussianMatrix_norm_le_realStack
    _ = _ := integral_realStack_norm
    _ ≤ _ := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        real_gaussian_matrix_norm_mean_le (N := N * 2) (M := M)

theorem integral_realStack_positive_excess {N M : ℕ} :
    (∫ g, max (‖realMatrixOfVector (complexGaussianRealStack N M g)‖ - Real.sqrt M) 0
      ∂stdGaussian (EuclideanSpace ℂ (Fin N × Fin M))) =
    ∫ x, max (‖realMatrixOfVector x‖ - Real.sqrt M) 0
      ∂stdGaussian (EuclideanSpace ℝ (Fin (N * 2) × Fin M)) := by
  rw [← stdGaussian_map (complexGaussianRealStack N M)]
  symm
  apply integral_map (complexGaussianRealStack N M).continuous.measurable.aemeasurable
  exact (show Continuous (fun x : EuclideanSpace ℝ (Fin (N * 2) × Fin M) =>
    max (‖realMatrixOfVector x‖ - Real.sqrt M) 0) by unfold realMatrixOfVector; fun_prop).aestronglyMeasurable

theorem complex_gaussian_matrix_positive_excess_le {N M : ℕ} [NeZero N] [NeZero M] :
    (∫ g, max (‖complexGaussianMatrix g‖ - Real.sqrt M) 0
      ∂stdGaussian (EuclideanSpace ℂ (Fin N × Fin M))) ≤ Real.sqrt (N * 2) + 1 := by
  haveI : NeZero (N * 2) := ⟨Nat.mul_ne_zero (NeZero.ne N) (by decide)⟩
  have hreal : Integrable (fun g : EuclideanSpace ℂ (Fin N × Fin M) =>
      ‖realMatrixOfVector (complexGaussianRealStack N M g)‖) (stdGaussian _) :=
    stdGaussian_integrable_of_lipschitz
      (realMatrixOfVector_norm_lipschitz.comp (complexGaussianRealStack N M).lipschitz)
  calc
    _ ≤ _ := integral_mono
      ((stdGaussian_integrable_of_lipschitz complexGaussianMatrix_norm_lipschitz).sub
        (integrable_const _)).pos_part (hreal.sub (integrable_const _)).pos_part
      (fun g => max_le_max (sub_le_sub_right (complexGaussianMatrix_norm_le_realStack g) _) le_rfl)
    _ = _ := integral_realStack_positive_excess
    _ ≤ _ := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        real_gaussian_matrix_positive_excess_le (N := N * 2) (M := M)

theorem normalized_positive_excess_eq (x r : ℝ) (hr : 0 < r) :
    max (x / r - 1) 0 = max (x - r) 0 / r := by
  rw [← max_div_div_right hr.le, sub_div, zero_div, div_self hr.ne']

theorem complex_gaussian_normalized_excess_le {N M : ℕ} [NeZero N] [NeZero M] :
    (∫ g, max (‖complexGaussianMatrix g‖ / Real.sqrt M - 1) 0
      ∂stdGaussian (EuclideanSpace ℂ (Fin N × Fin M))) ≤
      (Real.sqrt (N * 2) + 1) / Real.sqrt M := by
  have hM : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos M))
  simp_rw [normalized_positive_excess_eq _ _ hM]
  rw [integral_div]
  exact div_le_div_of_nonneg_right complex_gaussian_matrix_positive_excess_le hM.le

end LehnerEdges

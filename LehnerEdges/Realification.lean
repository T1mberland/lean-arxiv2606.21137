import LehnerEdges.GaussianMatrices
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Real and imaginary coordinates as a real Hilbert space isometry, and the
operator norm estimate for complexifying a real matrix. -/

noncomputable section
open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator
namespace LehnerEdges

def vectorRe {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => (z i).re)

def vectorIm {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => (z i).im)

theorem vectorReIm_norm_sq {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    ‖vectorRe z‖ ^ 2 + ‖vectorIm z‖ ^ 2 = ‖z‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq,
    vectorRe, vectorIm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, pow_two]

theorem complexify_mulVec_re {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (z : EuclideanSpace ℂ κ) :
    vectorRe ((EuclideanSpace.equiv ι ℂ).symm ((A.map Complex.ofReal) *ᵥ z)) =
      (EuclideanSpace.equiv ι ℝ).symm (A *ᵥ vectorRe z) := by
  ext i
  simp [vectorRe, Matrix.mulVec, dotProduct, Complex.mul_re]

theorem complexify_mulVec_im {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (z : EuclideanSpace ℂ κ) :
    vectorIm ((EuclideanSpace.equiv ι ℂ).symm ((A.map Complex.ofReal) *ᵥ z)) =
      (EuclideanSpace.equiv ι ℝ).symm (A *ᵥ vectorIm z) := by
  ext i
  simp [vectorIm, Matrix.mulVec, dotProduct, Complex.mul_im]

/-- Complexifying a real matrix does not increase its Euclidean operator
norm. The proof controls real and imaginary vectors separately, in squares. -/
theorem complexify_opNorm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) : ‖A.map Complex.ofReal‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro z
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  change ‖(EuclideanSpace.equiv ι ℂ).symm ((A.map Complex.ofReal) *ᵥ z)‖ ^ 2 ≤ _
  rw [← vectorReIm_norm_sq, complexify_mulVec_re, complexify_mulVec_im, mul_pow,
    ← vectorReIm_norm_sq z, mul_add]
  apply add_le_add
  · simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (Matrix.l2_opNorm_mulVec A (vectorRe z)) 2
  · simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (Matrix.l2_opNorm_mulVec A (vectorIm z)) 2

def complexRealification (ι : Type*) [Fintype ι] :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ι × Fin 2) :=
  (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ι => Complex.orthonormalBasisOneI.repr)).trans
    ((LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : ι) (_ : Fin 2) => ℝ)).symm.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.sigmaEquivProd ι (Fin 2))))

@[simp] theorem complexRealification_zero {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℂ ι) (i : ι) : complexRealification ι z (i, 0) = (z i).re := rfl

@[simp] theorem complexRealification_one {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℂ ι) (i : ι) : complexRealification ι z (i, 1) = (z i).im := rfl

theorem complexRealification_gaussian {ι : Type*} [Fintype ι] :
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℂ ι)).map (complexRealification ι) =
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (ι × Fin 2)) :=
  ProbabilityTheory.stdGaussian_map _

end LehnerEdges

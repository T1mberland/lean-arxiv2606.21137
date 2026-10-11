import LehnerEdges.KroneckerRayleigh

/-! Matching the quadratic Gaussian coefficients to the actual Kronecker
matrix, including the vectorization transpose and its Gaussian invariance. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace LehnerEdges

theorem frobeniusPair_symm {N M : ℕ} (K Z : Matrix (Fin N) (Fin M) ℂ) :
    frobeniusPair K Z = frobeniusPair Z K := by
  rw [frobeniusPair, ← re_trace_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose]
  rfl

theorem frobeniusPair_hermitian_projection {M : ℕ} (K Z : Mat M) (hK : K.IsHermitian) :
    frobeniusPair K Z = (K * gueProjection Z).trace.re := by
  calc
    _ = frobeniusPair Z K := frobeniusPair_symm _ _
    _ = frobeniusPair (gueProjection Z) K := (gueProjection_pair Z K hK).symm
    _ = _ := by rw [frobeniusPair_symm, frobeniusPair, hK.eq]

theorem purification_gue_pair {n N M : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) (S : Matrix (Fin N) (Fin M) ℂ)
    (g : GaussianCoordinates n M M) :
    inner ℝ (purificationGueCoefficient A S) g =
      (1 / Real.sqrt M) * ∑ i,
        (S.conjTranspose * A i * S * gueProjection (familyMatrices g i)).trace.re := by
  have hg : familyVector (familyMatrices g) = g := rfl
  rw [purificationGueCoefficient, real_inner_smul_left, ← hg, familyVector_real_inner]
  simp only [familyMatrices_familyVector]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact frobeniusPair_hermitian_projection _ _ (isHermitian_conjTranspose_mul_mul S (hA i))

theorem transposedGueMatrixModel_rayleigh {n N M : ℕ} (A₀ : Mat N) (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) (g : GaussianCoordinates n M M) (u : UnitPurification N M) :
    matrixRayleigh (transposedGueMatrixModel A₀ A g) u =
      purificationDrift A₀ u + inner ℝ (purificationGueCoefficient A (purificationMatrix u)) g := by
  rw [transposedGueMatrixModel, matrixRayleigh_add, matrixRayleigh_real_smul,
    matrixRayleigh_sum, matrixRayleigh_kronecker_one, purification_gue_pair A hA]
  simp only [matrixRayleigh_kronecker_transpose]

def gueTransposeEquiv (n M : ℕ) :
    (Fin n × Fin M × Fin M) ≃ (Fin n × Fin M × Fin M) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)

def gueTransposeIsometry (n M : ℕ) :
    GaussianCoordinates n M M ≃ₗᵢ[ℝ] GaussianCoordinates n M M :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℂ (gueTransposeEquiv n M)

theorem gueTranspose_family {n M : ℕ} (g : GaussianCoordinates n M M) (i : Fin n) :
    familyMatrices (gueTransposeIsometry n M g) i = (familyMatrices g i).transpose := rfl

theorem gueProjection_transpose {M : ℕ} (Z : Mat M) :
    gueProjection Z.transpose = (gueProjection Z).transpose := by
  simp only [gueProjection, transpose_smul, transpose_add,
    conjTranspose_transpose, transpose_conjTranspose]

theorem gueMatrixModel_transpose {n N M : ℕ} (A₀ : Mat N) (A : Fin n → Mat N)
    (g : GaussianCoordinates n M M) :
    gueMatrixModel A₀ A (gueTransposeIsometry n M g) = transposedGueMatrixModel A₀ A g := by
  simp only [gueMatrixModel, transposedGueMatrixModel, gueTranspose_family, gueProjection_transpose]

theorem continuous_gueMatrixModel {n N M : ℕ} (A₀ : Mat N) (A : Fin n → Mat N) :
    Continuous (gueMatrixModel (M := M) A₀ A) := by
  unfold gueMatrixModel gueProjection familyMatrices Matrix.kroneckerMap
  fun_prop

/-- The transpose introduced by vectorization changes neither the actual
matrix law nor its expected operator norm. -/
theorem integral_gueMatrixModel_transpose {n N M : ℕ} (A₀ : Mat N) (A : Fin n → Mat N) :
    (∫ g, ‖gueMatrixModel A₀ A g‖ ∂stdGaussian (GaussianCoordinates n M M)) =
      ∫ g, ‖transposedGueMatrixModel A₀ A g‖ ∂stdGaussian (GaussianCoordinates n M M) := by
  conv_lhs => rw [← stdGaussian_map (gueTransposeIsometry n M)]
  rw [integral_map (gueTransposeIsometry n M).continuous.measurable.aemeasurable
    (continuous_gueMatrixModel A₀ A).norm.aestronglyMeasurable]
  simp only [gueMatrixModel_transpose]

/-- Every joint Hermitian test of the constructed GUE family is the
corresponding standard real Gaussian linear functional. -/
theorem gueFamily_pair_eq_innerSL {n M : ℕ} (K : Fin n → Mat M)
    (hK : ∀ i, (K i).IsHermitian) :
    (fun g : GaussianCoordinates n M M =>
      ∑ i, frobeniusPair (gueProjection (familyMatrices g i)) (K i)) =
        innerSL ℝ (familyVector K) := by
  funext g
  have h := familyVector_real_inner K (familyMatrices g)
  change inner ℝ (familyVector K) g = ∑ i, frobeniusPair (K i) (familyMatrices g i) at h
  change _ = inner ℝ (familyVector K) g
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rw [gueProjection_pair _ _ (hK i), frobeniusPair_symm]

/-- Joint GUE normalization and independence encoded by all Hermitian
linear tests: mean zero and variance the sum of the squared Frobenius norms.
There are no hypotheses about the law left to the caller. -/
theorem gueFamily_pair_law {n M : ℕ} (K : Fin n → Mat M)
    (hK : ∀ i, (K i).IsHermitian) :
    (stdGaussian (GaussianCoordinates n M M)).map
      (fun g => ∑ i, frobeniusPair (gueProjection (familyMatrices g i)) (K i)) =
        gaussianReal 0 (∑ i, frobeniusSq (K i)).toNNReal := by
  rw [gueFamily_pair_eq_innerSL K hK]
  have hg := (IsGaussian.hasGaussianLaw_id (μ := stdGaussian (GaussianCoordinates n M M))).map
    (innerSL ℝ (familyVector K))
  have h := hg.map_eq_gaussianReal
  simp only [Function.comp_id, integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, familyVector_norm_sq] at h
  exact h

end LehnerEdges

import LehnerEdges.TraceDuality
import LehnerEdges.GaussianComparison
import LehnerEdges.ProcessLipschitz
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! Direct indexing by purifications avoids extending a partial isometry to a
coisometry. Only the action on the support of the compressed coefficient is
needed in the two-fiber proof. -/

noncomputable section
open Matrix
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace LehnerEdges

theorem frobeniusSq_mul_supported {L N M : ℕ}
    (X : Matrix (Fin L) (Fin N) ℂ) (W : Matrix (Fin N) (Fin M) ℂ)
    (hX : X * W * W.conjTranspose = X) : frobeniusSq (X * W) = frobeniusSq X := by
  simp only [frobeniusSq, conjTranspose_mul]
  rw [Matrix.mul_assoc, trace_mul_comm W.conjTranspose,
    Matrix.mul_assoc X.conjTranspose (X * W) W.conjTranspose, hX]

theorem frobeniusSq_adjoint_mul_supported {L N M : ℕ}
    (X : Matrix (Fin N) (Fin L) ℂ) (W : Matrix (Fin N) (Fin M) ℂ)
    (hX : W * W.conjTranspose * X = X) :
    frobeniusSq (W.conjTranspose * X) = frobeniusSq X := by
  simp only [frobeniusSq, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc W W.conjTranspose X, hX]

theorem supported_left_of_right {N M : ℕ} {P : Mat N}
    (hP : P.IsHermitian) (W : Matrix (Fin N) (Fin M) ℂ)
    (h : P * W * W.conjTranspose = P) : W * W.conjTranspose * P = P := by
  have ht := congrArg Matrix.conjTranspose h
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose, hP.eq, Matrix.mul_assoc] using ht

theorem frobeniusSq_compress_supported {N M : ℕ} {P : Mat N}
    (hP : P.IsHermitian) (W : Matrix (Fin N) (Fin M) ℂ)
    (h : P * W * W.conjTranspose = P) :
    frobeniusSq (W.conjTranspose * P * W) = frobeniusSq P := by
  have hl := supported_left_of_right hP W h
  have hl' : W * W.conjTranspose * (P * W) = P * W := by
    rw [← Matrix.mul_assoc, hl]
  rw [Matrix.mul_assoc, frobeniusSq_adjoint_mul_supported _ W hl',
    frobeniusSq_mul_supported _ W h]

/-- The two-fiber inequality requires identity only on the coefficient's
support. In particular polar contractions can replace full coisometries. -/
theorem two_fiber_supported_increment {N M : ℕ} {P Q : Mat N}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (W V : Matrix (Fin N) (Fin M) ℂ)
    (hW : P * W * W.conjTranspose = P)
    (hV : Q * V * V.conjTranspose = Q) :
    frobeniusSq (W.conjTranspose * P * W - V.conjTranspose * Q * V) ≤
      2 * frobeniusSq (P * W - Q * V) := by
  have hcross := positive_cross_bound hP hQ (W * V.conjTranspose)
  have hpq := frobeniusSq_nonneg (P - Q)
  have hright : ((P * W).conjTranspose * (Q * V)).trace.re =
      (P * Q * (W * V.conjTranspose).conjTranspose).trace.re := by
    simp only [conjTranspose_mul, hP.isHermitian.eq, conjTranspose_conjTranspose]
    rw [Matrix.mul_assoc, trace_mul_comm W.conjTranspose]
    simp only [Matrix.mul_assoc]
  have hcompressed : ((W.conjTranspose * P * W).conjTranspose *
      (V.conjTranspose * Q * V)).trace.re =
      (P * (W * V.conjTranspose) * Q * (W * V.conjTranspose).conjTranspose).trace.re := by
    simp only [conjTranspose_mul, hP.isHermitian.eq, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [trace_mul_comm W.conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [frobeniusSq_sub] at hpq
  simp only [frobeniusSq, hP.isHermitian.eq, hQ.isHermitian.eq] at hpq
  rw [frobeniusSq_sub, frobeniusSq_sub,
    frobeniusSq_compress_supported hP.isHermitian W hW,
    frobeniusSq_compress_supported hQ.isHermitian V hV,
    frobeniusSq_mul_supported _ W hW, frobeniusSq_mul_supported _ V hV,
    hcompressed, hright]
  simp only [frobeniusSq, hP.isHermitian.eq, hQ.isHermitian.eq]
  linarith

theorem polarContraction_support {N M : ℕ} (S : Matrix (Fin N) (Fin M) ℂ) :
    CFC.sqrt (S * S.conjTranspose) * polarContraction S * (polarContraction S).conjTranspose =
      CFC.sqrt (S * S.conjTranspose) := by
  rw [polarContraction_factorization]
  have h := congrArg Matrix.conjTranspose (polarContraction_mul_adjoint S)
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose,
    (CFC.sqrt_nonneg (S * S.conjTranspose)).posSemidef.isHermitian.eq] using h

theorem compressed_polar_support {N M : ℕ} (S : Matrix (Fin N) (Fin M) ℂ) (A : Mat N) :
    compressed (S * S.conjTranspose) A * polarContraction S *
      (polarContraction S).conjTranspose = compressed (S * S.conjTranspose) A := by
  simp only [compressed, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (CFC.sqrt (S * S.conjTranspose)) (polarContraction S)
      (polarContraction S).conjTranspose, polarContraction_support]

theorem compressed_mul_polar {N M : ℕ} (S : Matrix (Fin N) (Fin M) ℂ) (A : Mat N) :
    compressed (S * S.conjTranspose) A * polarContraction S =
      CFC.sqrt (S * S.conjTranspose) * A * S := by
  simp only [compressed, Matrix.mul_assoc, polarContraction_factorization]

theorem polar_compressed_polar {N M : ℕ} (S : Matrix (Fin N) (Fin M) ℂ) (A : Mat N) :
    (polarContraction S).conjTranspose * compressed (S * S.conjTranspose) A *
      polarContraction S = S.conjTranspose * A * S := by
  have hs : (polarContraction S).conjTranspose * CFC.sqrt (S * S.conjTranspose) =
      S.conjTranspose := by
    have h := congrArg Matrix.conjTranspose (polarContraction_factorization S)
    simpa only [conjTranspose_mul, (CFC.sqrt_nonneg (S * S.conjTranspose)).posSemidef.isHermitian.eq] using h
  simp only [compressed, Matrix.mul_assoc, polarContraction_factorization]
  rw [← Matrix.mul_assoc (polarContraction S).conjTranspose (CFC.sqrt (S * S.conjTranspose)), hs]

/-- Increment domination directly on rectangular purifications; no full-rank
assumption and no dimension inequality `M ≥ N` is needed. -/
theorem purification_increment {N M : ℕ} (A : Mat N) (hA : A.PosSemidef)
    (S T : Matrix (Fin N) (Fin M) ℂ) :
    frobeniusSq (S.conjTranspose * A * S - T.conjTranspose * A * T) ≤
      2 * frobeniusSq (CFC.sqrt (S * S.conjTranspose) * A * S -
        CFC.sqrt (T * T.conjTranspose) * A * T) := by
  have h := two_fiber_supported_increment
    (compressed_posSemidef (S * S.conjTranspose) A hA)
    (compressed_posSemidef (T * T.conjTranspose) A hA)
    (polarContraction S) (polarContraction T)
    (compressed_polar_support S A) (compressed_polar_support T A)
  simpa only [polar_compressed_polar, compressed_mul_polar] using h

def purificationDensity {N M : ℕ} (S : Matrix (Fin N) (Fin M) ℂ)
    (hS : frobeniusSq S = 1) : Density N := by
  refine ⟨S * S.conjTranspose, Matrix.posSemidef_self_mul_conjTranspose S, ?_⟩
  apply Complex.ext
  · change (S * S.conjTranspose).trace.re = 1
    rw [trace_mul_comm]
    exact hS
  · exact (Complex.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose S).trace_nonneg).2.symm

def purificationGueCoefficient {n N M : ℕ} (A : Fin n → Mat N)
    (S : Matrix (Fin N) (Fin M) ℂ) : GaussianCoordinates n M M :=
  (1 / Real.sqrt M) • familyVector (fun i => S.conjTranspose * A i * S)

def purificationComplexCoefficient {n N M : ℕ} (A : Fin n → Mat N)
    (S : Matrix (Fin N) (Fin M) ℂ) : GaussianCoordinates n N M :=
  (Real.sqrt 2 / Real.sqrt M) • familyVector
    (fun i => CFC.sqrt (S * S.conjTranspose) * A i * S)

theorem purification_coefficient_increment {n N M : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).PosSemidef) (S T : Matrix (Fin N) (Fin M) ℂ) :
    ‖purificationGueCoefficient A S - purificationGueCoefficient A T‖ ^ 2 ≤
      ‖purificationComplexCoefficient A S - purificationComplexCoefficient A T‖ ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => purification_increment (A i) (hA i) S T)
  rw [← Finset.mul_sum] at h
  simp only [purificationGueCoefficient, purificationComplexCoefficient, ← smul_sub,
    familyVector_sub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, familyVector_norm_sq,
    div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  convert mul_le_mul_of_nonneg_left h (sq_nonneg (1 / Real.sqrt M)) using 1 <;>
    simp only [div_pow, one_pow] <;> ring

theorem purification_compressed_hermitian {N M : ℕ}
    (S : Matrix (Fin N) (Fin M) ℂ) {A : Mat N} (hA : A.IsHermitian) :
    (compressed (S * S.conjTranspose) A).IsHermitian := by
  simpa only [compressed,
    (CFC.sqrt_nonneg (S * S.conjTranspose)).posSemidef.isHermitian.eq] using
    isHermitian_conjTranspose_mul_mul (CFC.sqrt (S * S.conjTranspose)) hA

theorem purification_frobeniusSq {N M : ℕ}
    (S : Matrix (Fin N) (Fin M) ℂ) {A : Mat N} (hA : A.IsHermitian) :
    frobeniusSq (S.conjTranspose * A * S) =
      frobeniusSq (compressed (S * S.conjTranspose) A) := by
  rw [← polar_compressed_polar S A]
  exact frobeniusSq_compress_supported (purification_compressed_hermitian S hA)
    (polarContraction S) (compressed_polar_support S A)

theorem purification_rectangular_frobeniusSq {N M : ℕ}
    (S : Matrix (Fin N) (Fin M) ℂ) (A : Mat N) :
    frobeniusSq (CFC.sqrt (S * S.conjTranspose) * A * S) =
      frobeniusSq (compressed (S * S.conjTranspose) A) := by
  rw [← compressed_mul_polar S A]
  exact frobeniusSq_mul_supported _ _ (compressed_polar_support S A)

theorem purification_sum_frobeniusSq_le {n N M : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) (S : Matrix (Fin N) (Fin M) ℂ)
    (hS : frobeniusSq S = 1) :
    (∑ i, frobeniusSq (S.conjTranspose * A i * S)) ≤ ‖squareFunction A‖ := by
  simp only [purification_frobeniusSq S (hA _)]
  exact sum_compressed_frobeniusSq_le A hA (purificationDensity S hS)

theorem purificationGueCoefficient_norm_le {n N M : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) (S : Matrix (Fin N) (Fin M) ℂ)
    (hS : frobeniusSq S = 1) :
    ‖purificationGueCoefficient A S‖ ≤ Real.sqrt ‖squareFunction A‖ / Real.sqrt M := by
  have hs : ‖familyVector (fun i => S.conjTranspose * A i * S)‖ ^ 2 ≤ ‖squareFunction A‖ := by
    rw [familyVector_norm_sq]
    exact purification_sum_frobeniusSq_le A hA S hS
  have hn := Real.le_sqrt_of_sq_le hs
  simp only [purificationGueCoefficient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg zero_le_one (Real.sqrt_nonneg _))]
  calc _ ≤ (1 / Real.sqrt M) * Real.sqrt ‖squareFunction A‖ :=
         mul_le_mul_of_nonneg_left hn (div_nonneg zero_le_one (Real.sqrt_nonneg _))
       _ = _ := by ring

theorem purificationComplexCoefficient_norm_le {n N M : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) (S : Matrix (Fin N) (Fin M) ℂ)
    (hS : frobeniusSq S = 1) :
    ‖purificationComplexCoefficient A S‖ ≤
      (Real.sqrt 2 / Real.sqrt M) * Real.sqrt ‖squareFunction A‖ := by
  have hs : ‖familyVector (fun i => CFC.sqrt (S * S.conjTranspose) * A i * S)‖ ^ 2 ≤
      ‖squareFunction A‖ := by
    rw [familyVector_norm_sq]
    simp only [purification_rectangular_frobeniusSq]
    exact sum_compressed_frobeniusSq_le A hA (purificationDensity S hS)
  have hn := Real.le_sqrt_of_sq_le hs
  simp only [purificationComplexCoefficient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_left hn (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem continuous_sqrt_gram {N M : ℕ} :
    Continuous (fun S : Matrix (Fin N) (Fin M) ℂ => CFC.sqrt (S * S.conjTranspose)) := by
  apply CFC.continuousOn_sqrt.comp_continuous
  · fun_prop
  · exact fun S => (Matrix.posSemidef_self_mul_conjTranspose S).nonneg

theorem continuous_purificationGueCoefficient {n N M : ℕ} (A : Fin n → Mat N) :
    Continuous (purificationGueCoefficient (M := M) A) := by
  unfold purificationGueCoefficient familyVector
  fun_prop

theorem continuous_purificationComplexCoefficient {n N M : ℕ} (A : Fin n → Mat N) :
    Continuous (purificationComplexCoefficient (M := M) A) := by
  have h := continuous_sqrt_gram (N := N) (M := M)
  unfold purificationComplexCoefficient familyVector
  fun_prop

end LehnerEdges

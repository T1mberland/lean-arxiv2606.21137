import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite-dimensional matrix objects in Collins–Yamagishi, arXiv:2606.21137v2.
The operator norm below is the Euclidean operator norm, not the entrywise or
maximum-row-sum matrix norm. -/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace LehnerEdges

abbrev Mat (N : ℕ) := Matrix (Fin N) (Fin N) ℂ

/-- The density matrices, with the unnormalized matrix trace. -/
def Density (N : ℕ) := {C : Mat N // C.PosSemidef ∧ C.trace = 1}

/-- The covariance map, meaningful for all Hermitian coefficient families. -/
def covariance {N n : ℕ} (A : Fin n → Mat N) (C : Mat N) : Mat N :=
  ∑ i, A i * C * A i

/-- The square-function matrix of the coefficients. -/
def squareFunction {N n : ℕ} (A : Fin n → Mat N) : Mat N := ∑ i, A i ^ 2

/-- The compressed coefficient `B_i(C)` from Section 4. -/
def compressed {N : ℕ} (C A : Mat N) : Mat N := CFC.sqrt C * A * CFC.sqrt C

/-- The matrix `E_C` from equation (4). -/
def energy {N n : ℕ} (A : Fin n → Mat N) (C : Mat N) : Mat N :=
  CFC.sqrt C * covariance A C * CFC.sqrt C

/-- Stiefel coisometries, in the paper's orientation `W W* = I_N`. -/
def Stiefel (N M : ℕ) :=
  {W : Matrix (Fin N) (Fin M) ℂ // W * W.conjTranspose = 1}

/-- The actual rectangular Schatten 1-norm, defined through `sqrt(A A*)`. -/
def traceNorm {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) : ℝ :=
  (CFC.sqrt (A * A.conjTranspose)).trace.re

/-- The real Frobenius pairing, equation in Section 2. -/
def frobeniusPair {N M : ℕ} (A B : Matrix (Fin N) (Fin M) ℂ) : ℝ :=
  (A.conjTranspose * B).trace.re

theorem covariance_one {N n : ℕ} (A : Fin n → Mat N) :
    covariance A 1 = squareFunction A := by
  simp [covariance, squareFunction, pow_two]

theorem compressed_posSemidef {N : ℕ} (C A : Mat N) (hA : A.PosSemidef) :
    (compressed C A).PosSemidef := by
  simpa [compressed, (CFC.sqrt_nonneg C).posSemidef.isHermitian.eq] using
    hA.conjTranspose_mul_mul_same (CFC.sqrt C)

theorem energy_eq_sum_sq {N n : ℕ} (A : Fin n → Mat N) (C : Mat N)
    (hC : C.PosSemidef) :
    energy A C = ∑ i, (compressed C (A i)) ^ 2 := by
  simp only [energy, covariance, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [compressed, pow_two]
  have hs : CFC.sqrt C * CFC.sqrt C = C := CFC.sqrt_mul_sqrt_self C hC.nonneg
  simp only [mul_assoc] at hs ⊢
  simp only [← mul_assoc] at hs ⊢
  rw [mul_assoc (CFC.sqrt C * A i) (CFC.sqrt C) (CFC.sqrt C), hs]

theorem covariance_posSemidef {N n : ℕ} (A : Fin n → Mat N) (C : Mat N)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.PosSemidef) :
    (covariance A C).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply Finset.sum_nonneg
  intro i _
  have hi : (A i * C * A i).PosSemidef := by
    simpa [(hA i).eq] using hC.conjTranspose_mul_mul_same (A i)
  exact hi.nonneg

theorem energy_posSemidef {N n : ℕ} (A : Fin n → Mat N) (C : Mat N)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.PosSemidef) :
    (energy A C).PosSemidef := by
  simpa [energy, (CFC.sqrt_nonneg C).posSemidef.isHermitian.eq] using
    (covariance_posSemidef A C hA hC).conjTranspose_mul_mul_same (CFC.sqrt C)

/-- Squared Frobenius norm, expressed without choosing a matrix norm instance. -/
def frobeniusSq {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) : ℝ :=
  (A.conjTranspose * A).trace.re

theorem frobeniusSq_nonneg {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :
    0 ≤ frobeniusSq A :=
  (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg).1

theorem re_trace_mul_nonneg {N : ℕ} {P Q : Mat N}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace.re := by
  have h := (hQ.conjTranspose_mul_mul_same (CFC.sqrt P)).trace_nonneg
  rw [(CFC.sqrt_nonneg P).posSemidef.isHermitian.eq,
    trace_mul_cycle, CFC.sqrt_mul_sqrt_self P hP.nonneg] at h
  exact (Complex.nonneg_iff.mp h).1

@[simp] theorem re_trace_conjTranspose {N : ℕ} (A : Mat N) :
    A.conjTranspose.trace.re = A.trace.re := by
  simp [trace_conjTranspose]

theorem frobeniusSq_sub {N M : ℕ} (A B : Matrix (Fin N) (Fin M) ℂ) :
    frobeniusSq (A - B) = frobeniusSq A + frobeniusSq B -
      2 * (A.conjTranspose * B).trace.re := by
  have hc : (B.conjTranspose * A).trace.re = (A.conjTranspose * B).trace.re := by
    rw [← re_trace_conjTranspose (A.conjTranspose * B), conjTranspose_mul,
      conjTranspose_conjTranspose]
  simp only [frobeniusSq, conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, trace_sub,
    Complex.sub_re, hc]
  ring

theorem frobeniusSq_eq_sum {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :
    frobeniusSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  simp only [frobeniusSq, trace, diag, mul_apply, conjTranspose_apply,
    Complex.re_sum, Complex.mul_re, RCLike.star_def, Complex.conj_re, Complex.conj_im]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Flattening a matrix into its Frobenius Hilbert space. -/
def matrixVector {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :
    EuclideanSpace ℂ (Fin N × Fin M) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

theorem matrixVector_norm_sq {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :
    ‖matrixVector A‖ ^ 2 = frobeniusSq A := by
  rw [EuclideanSpace.norm_sq_eq, frobeniusSq_eq_sum]
  simp only [matrixVector, WithLp.ofLp_toLp, Fintype.sum_prod_type]

theorem matrixVector_inner {N M : ℕ} (A B : Matrix (Fin N) (Fin M) ℂ) :
    inner ℂ (matrixVector A) (matrixVector B) = (A.conjTranspose * B).trace := by
  simp only [matrixVector, PiLp.inner_apply, RCLike.inner_apply,
    Fintype.sum_prod_type, trace, diag, mul_apply, conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem trace_cauchy_schwarz_sq {N M : ℕ} (A B : Matrix (Fin N) (Fin M) ℂ) :
    ‖(A.conjTranspose * B).trace‖ ^ 2 ≤ frobeniusSq A * frobeniusSq B := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (matrixVector A) (matrixVector B)
  have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  simpa only [matrixVector_inner, mul_pow, matrixVector_norm_sq] using hh

end LehnerEdges

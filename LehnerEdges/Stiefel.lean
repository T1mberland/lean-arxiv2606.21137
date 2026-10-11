import LehnerEdges.MatrixBasics

/-! An elementary proof of Lemma 4.1. The proof uses trace positivity and
square completion, so does not need the general Araki–Yamagami inequality. -/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace LehnerEdges

theorem frobeniusSq_mul_coisometry {L N M : ℕ}
    (X : Matrix (Fin L) (Fin N) ℂ) (W : Stiefel N M) :
    frobeniusSq (X * W.val) = frobeniusSq X := by
  unfold frobeniusSq
  simp only [conjTranspose_mul]
  rw [Matrix.mul_assoc, trace_mul_comm W.val.conjTranspose,
    Matrix.mul_assoc, Matrix.mul_assoc, W.property, Matrix.mul_one]

theorem frobeniusSq_coisometry_adjoint_mul {L N M : ℕ}
    (X : Matrix (Fin N) (Fin L) ℂ) (W : Stiefel N M) :
    frobeniusSq (W.val.conjTranspose * X) = frobeniusSq X := by
  unfold frobeniusSq
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc W.val W.val.conjTranspose, W.property, Matrix.one_mul]

theorem re_trace_cross {N : ℕ} (P Q K : Mat N)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    (P * K * Q).trace.re = (P * Q * K.conjTranspose).trace.re := by
  rw [← re_trace_conjTranspose (P * K * Q), conjTranspose_mul,
    conjTranspose_mul, hP.eq, hQ.eq, trace_mul_cycle']
  simp only [Matrix.mul_assoc]

theorem positive_cross_bound {N : ℕ} {P Q : Mat N}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (K : Mat N) :
    2 * (P * Q * K.conjTranspose).trace.re ≤
      (P * Q).trace.re + (P * K * Q * K.conjTranspose).trace.re := by
  have h := re_trace_mul_nonneg hP (hQ.mul_mul_conjTranspose_same (1 - K))
  simp only [conjTranspose_sub, conjTranspose_one, mul_sub, sub_mul, mul_one, one_mul,
    trace_sub, Complex.sub_re, ← mul_assoc] at h
  rw [re_trace_cross P Q K hP.isHermitian hQ.isHermitian] at h
  linarith

theorem stiefel_pair_right {N M : ℕ} (P Q : Mat N) (W V : Stiefel N M)
    (hP : P.IsHermitian) :
    ((P * W.val).conjTranspose * (Q * V.val)).trace.re =
      (P * Q * (W.val * V.val.conjTranspose).conjTranspose).trace.re := by
  simp only [conjTranspose_mul, hP.eq, conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc, trace_mul_comm W.val.conjTranspose]
  simp only [Matrix.mul_assoc]

theorem stiefel_pair_compressed {N M : ℕ} (P Q : Mat N) (W V : Stiefel N M)
    (hP : P.IsHermitian) :
    ((W.val.conjTranspose * P * W.val).conjTranspose *
      (V.val.conjTranspose * Q * V.val)).trace.re =
      (P * (W.val * V.val.conjTranspose) * Q *
        (W.val * V.val.conjTranspose).conjTranspose).trace.re := by
  simp only [conjTranspose_mul, hP.eq, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm W.val.conjTranspose]
  simp only [Matrix.mul_assoc]

/-- Lemma 4.1, with precisely the squared Frobenius norms and factor `2`. -/
theorem two_fiber_stiefel_increment {N M : ℕ} {P Q : Mat N}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (W V : Stiefel N M) :
    frobeniusSq (W.val.conjTranspose * P * W.val - V.val.conjTranspose * Q * V.val) ≤
      2 * frobeniusSq (P * W.val - Q * V.val) := by
  have hcross := positive_cross_bound hP hQ (W.val * V.val.conjTranspose)
  have hpq := frobeniusSq_nonneg (P - Q)
  rw [frobeniusSq_sub] at hpq
  simp only [frobeniusSq, hP.isHermitian.eq, hQ.isHermitian.eq] at hpq
  rw [frobeniusSq_sub, frobeniusSq_sub,
    frobeniusSq_mul_coisometry, frobeniusSq_mul_coisometry,
    frobeniusSq_coisometry_adjoint_mul, frobeniusSq_coisometry_adjoint_mul,
    frobeniusSq_mul_coisometry, frobeniusSq_mul_coisometry,
    stiefel_pair_compressed P Q W V hP.isHermitian,
    stiefel_pair_right P Q W V hP.isHermitian]
  simp only [frobeniusSq, hP.isHermitian.eq, hQ.isHermitian.eq]
  linarith

/-- The exact matrix inequality needed for increments of the full processes,
including two different density matrices. -/
theorem compressed_increment {N M n : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).PosSemidef) (C D : Density N) (W V : Stiefel N M) :
    (∑ i, frobeniusSq (W.val.conjTranspose * compressed C.val (A i) * W.val -
      V.val.conjTranspose * compressed D.val (A i) * V.val)) ≤
      2 * ∑ i, frobeniusSq (compressed C.val (A i) * W.val -
        compressed D.val (A i) * V.val) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => two_fiber_stiefel_increment
    (compressed_posSemidef C.val (A i) (hA i))
    (compressed_posSemidef D.val (A i) (hA i)) W V

end LehnerEdges

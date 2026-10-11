import LehnerEdges.TraceNorm

/-! Polar factorization and the trace-norm variational formula over contractions.
The contraction formula works in all rectangular dimensions, including singular
matrices. It does not assert the coisometry version of Lemma 2.1. -/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace LehnerEdges

theorem polarContraction_factorization {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :
    CFC.sqrt (A * A.conjTranspose) * polarContraction A = A := by
  let E := A * A.conjTranspose
  have hE : E.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  have hz : (1 - CFC.sqrt E * inverseSqrt E) * E = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, inverseSqrt_mul E hE,
      CFC.sqrt_mul_sqrt_self E hE.nonneg, sub_self]
  have h := (Matrix.mul_self_mul_conjTranspose_eq_zero A
    (1 - CFC.sqrt E * inverseSqrt E)).mp hz
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  simpa only [polarContraction, Matrix.mul_assoc] using h.symm

/-- A positive matrix defines a functional of norm equal to its trace. -/
theorem abs_re_trace_pos_mul_le {N : ℕ} {P : Mat N} (hP : P.PosSemidef) (T : Mat N) :
    |(P * T).trace.re| ≤ ‖T‖ * P.trace.re := by
  let S := CFC.sqrt P
  have hS : S.conjTranspose = S := (CFC.sqrt_nonneg P).posSemidef.isHermitian.eq
  have hSq : S * S = P := CFC.sqrt_mul_sqrt_self P hP.nonneg
  have hfr : frobeniusSq S = P.trace.re := by rw [frobeniusSq, hS, hSq]
  have ht : (S.conjTranspose * (T * S)).trace = (P * T).trace := by
    rw [hS, ← Matrix.mul_assoc, trace_mul_cycle, hSq]
  have hcs := trace_cauchy_schwarz_sq S (T * S)
  rw [ht, hfr] at hcs
  have hi := frobeniusSq_mul_le T S
  rw [hfr] at hi
  have hr := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr
    (Complex.abs_re_le_norm (P * T).trace)
  have hp0 : 0 ≤ P.trace.re := (Complex.nonneg_iff.mp hP.trace_nonneg).1
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) hp0)).mp
  calc |(P * T).trace.re| ^ 2 ≤ ‖(P * T).trace‖ ^ 2 := hr
       _ ≤ P.trace.re * frobeniusSq (T * S) := hcs
       _ ≤ P.trace.re * (‖T‖ ^ 2 * P.trace.re) := mul_le_mul_of_nonneg_left hi hp0
       _ = (‖T‖ * P.trace.re) ^ 2 := by ring

/-- Rectangular trace duality, with no rank hypothesis. -/
theorem abs_frobeniusPair_le_traceNorm {N M : ℕ} (W A : Matrix (Fin N) (Fin M) ℂ) :
    |frobeniusPair W A| ≤ ‖W‖ * traceNorm A := by
  let P := CFC.sqrt (A * A.conjTranspose)
  let K := polarContraction A
  have hP : P.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have he : frobeniusPair W A = (P * (K * W.conjTranspose)).trace.re := by
    rw [frobeniusPair, trace_mul_comm, ← polarContraction_factorization A]
    exact congrArg (fun X : Mat N => X.trace.re) (Matrix.mul_assoc P K W.conjTranspose)
  have hk : ‖K * W.conjTranspose‖ ≤ ‖W‖ := by
    calc _ ≤ ‖K‖ * ‖W.conjTranspose‖ := Matrix.l2_opNorm_mul _ _
         _ ≤ 1 * ‖W.conjTranspose‖ :=
           mul_le_mul_of_nonneg_right (polarContraction_norm_le A) (norm_nonneg _)
         _ = _ := by rw [one_mul, l2_opNorm_conjTranspose]
  rw [he]
  exact (abs_re_trace_pos_mul_le hP _).trans
    (mul_le_mul_of_nonneg_right hk (traceNorm_nonneg A))

theorem polarContraction_pair {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :
    frobeniusPair (polarContraction A) A = traceNorm A := by
  rw [frobeniusPair, ← re_trace_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, trace_mul_comm,
    polarContraction_mul_adjoint, traceNorm]

/-- The trace norm is an attained supremum over the operator-norm unit ball.
This is the contraction form of the trace variational formula. -/
theorem traceNorm_eq_sup_contractions {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :
    traceNorm A = sSup (Set.range (fun W : {W : Matrix (Fin N) (Fin M) ℂ // ‖W‖ ≤ 1} =>
      frobeniusPair W.val A)) := by
  have hb (W : {W : Matrix (Fin N) (Fin M) ℂ // ‖W‖ ≤ 1}) :
      frobeniusPair W.val A ≤ traceNorm A :=
    (le_abs_self _).trans ((abs_frobeniusPair_le_traceNorm W.val A).trans
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right W.property (traceNorm_nonneg A)))
  apply le_antisymm
  · apply le_csSup (show BddAbove (Set.range _) from ⟨traceNorm A, by rintro _ ⟨W, rfl⟩; exact hb W⟩)
    exact ⟨⟨polarContraction A, polarContraction_norm_le A⟩, polarContraction_pair A⟩
  · apply csSup_le
    · exact ⟨_, ⟨⟨polarContraction A, polarContraction_norm_le A⟩, rfl⟩⟩
    · rintro _ ⟨W, rfl⟩
      exact hb W

end LehnerEdges

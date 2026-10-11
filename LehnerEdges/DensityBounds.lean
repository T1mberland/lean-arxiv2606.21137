import LehnerEdges.TraceNorm

/-! The square-function bound of Proposition 5.2, valid even for signed
Hermitian coefficients. All traces are unnormalized. -/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace LehnerEdges

theorem frobeniusSq_sqrt {N : ℕ} (P : Mat N) (hP : P.PosSemidef) :
    frobeniusSq (CFC.sqrt P) = P.trace.re := by
  rw [frobeniusSq, (CFC.sqrt_nonneg P).posSemidef.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self P hP.nonneg]

theorem density_trace_le_norm {N : ℕ} (C : Density N) (B : Mat N)
    (hB : B.IsHermitian) : (C.val * B).trace.re ≤ ‖B‖ := by
  have hb : B ≤ ‖B‖ • (1 : Mat N) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (show IsSelfAdjoint B from hB).le_algebraMap_norm_self
  have h := re_trace_mul_nonneg C.property.1 (Matrix.le_iff.mp hb)
  simpa only [mul_sub, Matrix.mul_smul, mul_one, trace_sub, trace_smul,
    C.property.2, Complex.real_smul, smul_eq_mul, mul_one, Complex.ofReal_re, Complex.sub_re,
    sub_nonneg] using h

theorem squareFunction_posSemidef {N n : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) : (squareFunction A).PosSemidef := by
  rw [← covariance_one]
  exact covariance_posSemidef A 1 hA Matrix.PosSemidef.one

theorem trace_covariance {N n : ℕ} (A : Fin n → Mat N) (C : Mat N) :
    (covariance A C).trace = (C * squareFunction A).trace := by
  simp only [covariance, squareFunction, Finset.mul_sum, trace_sum, pow_two]
  apply Finset.sum_congr rfl
  intro i _
  calc (A i * C * A i).trace = (A i * A i * C).trace := trace_mul_cycle _ _ _
       _ = (C * (A i * A i)).trace := trace_mul_comm _ _

theorem traceNorm_sqrt_mul_sqrt {N : ℕ} (C D : Mat N)
    (hD : D.PosSemidef) :
    traceNorm (CFC.sqrt C * CFC.sqrt D) =
      (CFC.sqrt (CFC.sqrt C * D * CFC.sqrt C)).trace.re := by
  simp only [traceNorm, conjTranspose_mul,
    (CFC.sqrt_nonneg C).posSemidef.isHermitian.eq,
    (CFC.sqrt_nonneg D).posSemidef.isHermitian.eq, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (CFC.sqrt D) (CFC.sqrt D),
    CFC.sqrt_mul_sqrt_self D hD.nonneg]

/-- The density-matrix square-root trace estimate. Both matrices may be singular. -/
theorem fidelity_bound {N : ℕ} (C D : Mat N) (hC : C.PosSemidef) (hD : D.PosSemidef) :
    (CFC.sqrt (CFC.sqrt C * D * CFC.sqrt C)).trace.re ≤
      Real.sqrt C.trace.re * Real.sqrt D.trace.re := by
  simpa only [traceNorm_sqrt_mul_sqrt C D hD, frobeniusSq_sqrt C hC,
    frobeniusSq_sqrt D hD] using
    traceNorm_mul_le_frobenius (CFC.sqrt C) (CFC.sqrt D)

/-- The bound for `Bmax` in Proposition 5.2, pointwise for every density matrix.
Termwise positivity is unnecessary for this part of the proof. -/
theorem density_energy_bound {N n : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) (C : Density N) :
    (CFC.sqrt (energy A C.val)).trace.re ≤ Real.sqrt ‖squareFunction A‖ := by
  have hη := covariance_posSemidef A C.val hA C.property.1
  have hf := fidelity_bound C.val (covariance A C.val) C.property.1 hη
  simp only [C.property.2, Complex.one_re, Real.sqrt_one, one_mul] at hf
  have hb : (covariance A C.val).trace.re ≤ ‖squareFunction A‖ := by
    rw [trace_covariance]
    exact density_trace_le_norm C _ (squareFunction_posSemidef A hA).isHermitian
  exact hf.trans (Real.sqrt_le_sqrt hb)

/-- Uniform deterministic block estimate from Proposition 5.2. -/
theorem comparison_block_bound {N d M : ℕ} (R : Matrix (Fin N) (Fin d) ℂ)
    (Γ : Matrix (Fin d) (Fin M) ℂ) {m : ℝ} (hm : 0 < m) :
    (1 / Real.sqrt m) * traceNorm (R * Γ) ≤
      (‖Γ‖ / Real.sqrt m) * traceNorm R := by
  have hs : 0 ≤ 1 / Real.sqrt m := le_of_lt (one_div_pos.mpr (Real.sqrt_pos.mpr hm))
  have h := mul_le_mul_of_nonneg_left (traceNorm_mul_le R Γ) hs
  calc _ ≤ (1 / Real.sqrt m) * (‖Γ‖ * traceNorm R) := h
       _ = _ := by ring

end LehnerEdges

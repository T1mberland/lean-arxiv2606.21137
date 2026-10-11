import LehnerEdges.DensityBounds

/-! The square completion underlying Lemma 3.2. -/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace LehnerEdges

/-- The trace AM–GM inequality in the normalized variable `Y` of Lemma 3.2.
The matrix `E` may be singular; `Y` must be positive definite. -/
theorem trace_amgm {N : ℕ} {E Y : Mat N}
    (hE : E.PosSemidef) (hY : Y.PosDef) :
    2 * (CFC.sqrt E).trace.re ≤ Y.trace.re + (E * Y⁻¹).trace.re := by
  let R := CFC.sqrt Y
  let T := CFC.sqrt E * R⁻¹
  have hR : R.PosSemidef := (CFC.sqrt_nonneg Y).posSemidef
  have hRunit : IsUnit R := hY.isStrictlyPositive.sqrt.isUnit
  have hRinv : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R (R.isUnit_iff_isUnit_det.mp hRunit)
  have hRinv2 : R⁻¹ * R⁻¹ = Y⁻¹ := by
    rw [show R⁻¹ = CFC.sqrt Y⁻¹ from hY.posSemidef.inv_sqrt]
    exact CFC.sqrt_mul_sqrt_self Y⁻¹ hY.posSemidef.inv.nonneg
  have hRR : frobeniusSq R = Y.trace.re := by
    rw [frobeniusSq, hR.isHermitian.eq, CFC.sqrt_mul_sqrt_self Y hY.posSemidef.nonneg]
  have hTT : frobeniusSq T = (E * Y⁻¹).trace.re := by
    simp only [frobeniusSq, T, conjTranspose_mul, hR.inv.isHermitian.eq,
      (CFC.sqrt_nonneg E).posSemidef.isHermitian.eq, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (CFC.sqrt E) (CFC.sqrt E),
      CFC.sqrt_mul_sqrt_self E hE.nonneg, ← Matrix.mul_assoc, trace_mul_cycle,
      hRinv2, trace_mul_comm]
  have hRT : (R.conjTranspose * T).trace.re = (CFC.sqrt E).trace.re := by
    change (R.conjTranspose * (CFC.sqrt E * R⁻¹)).trace.re = _
    rw [hR.isHermitian.eq, ← Matrix.mul_assoc, trace_mul_cycle, hRinv, Matrix.one_mul]
  have h := frobeniusSq_nonneg (R - T)
  rw [frobeniusSq_sub, hRR, hTT, hRT] at h
  linarith

/-- The lower-bound direction of weighted trace AM–GM (Lemma 3.2).
Unlike a change of variables through `C⁻¹`, this proof covers singular `C`
directly by Schatten Cauchy–Schwarz. This is the direction needed for Remark 3.6. -/
theorem weighted_trace_amgm {N : ℕ} {C D Z : Mat N}
    (hC : C.PosSemidef) (hD : D.PosSemidef) (hZ : Z.PosDef) :
    2 * (CFC.sqrt (CFC.sqrt C * D * CFC.sqrt C)).trace.re ≤
      (C * Z).trace.re + (D * Z⁻¹).trace.re := by
  let R := CFC.sqrt Z
  have hR : R.PosSemidef := (CFC.sqrt_nonneg Z).posSemidef
  have hRu : IsUnit R := hZ.isStrictlyPositive.sqrt.isUnit
  have hRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R (R.isUnit_iff_isUnit_det.mp hRu)
  have hRi2 : R⁻¹ * R⁻¹ = Z⁻¹ := by
    rw [show R⁻¹ = CFC.sqrt Z⁻¹ from hZ.posSemidef.inv_sqrt]
    exact CFC.sqrt_mul_sqrt_self Z⁻¹ hZ.posSemidef.inv.nonneg
  let U := CFC.sqrt C * R
  let V := R⁻¹ * CFC.sqrt D
  have hUV : U * V = CFC.sqrt C * CFC.sqrt D := by
    simp only [U, V, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R R⁻¹, hRi, Matrix.one_mul]
  have hUU : frobeniusSq U = (C * Z).trace.re := by
    simp only [frobeniusSq, U, conjTranspose_mul, hR.isHermitian.eq,
      (CFC.sqrt_nonneg C).posSemidef.isHermitian.eq, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (CFC.sqrt C) (CFC.sqrt C),
      CFC.sqrt_mul_sqrt_self C hC.nonneg, ← Matrix.mul_assoc, trace_mul_cycle,
      CFC.sqrt_mul_sqrt_self Z hZ.posSemidef.nonneg, trace_mul_comm]
  have hVV : frobeniusSq V = (D * Z⁻¹).trace.re := by
    simp only [frobeniusSq, V, conjTranspose_mul, hR.inv.isHermitian.eq,
      (CFC.sqrt_nonneg D).posSemidef.isHermitian.eq, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R⁻¹ R⁻¹, hRi2, ← Matrix.mul_assoc, trace_mul_cycle,
      CFC.sqrt_mul_sqrt_self D hD.nonneg]
  have h := traceNorm_mul_le_frobenius U V
  rw [hUV, traceNorm_sqrt_mul_sqrt C D hD] at h
  have hsU := Real.sq_sqrt (frobeniusSq_nonneg U)
  have hsV := Real.sq_sqrt (frobeniusSq_nonneg V)
  have hsq := sq_nonneg (Real.sqrt (frobeniusSq U) - Real.sqrt (frobeniusSq V))
  rw [← hUU, ← hVV]
  nlinarith

end LehnerEdges

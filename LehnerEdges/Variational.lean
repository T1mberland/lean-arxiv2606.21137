import LehnerEdges.TraceAMGM

/-! Finite matrix spectral edges and the elementary minimax direction of
Remark 3.6. These definitions make no assertion about free operators. -/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace LehnerEdges

/-- The largest real spectral value. All results about this definition assume
Hermiticity and nonzero dimension, so its spectrum is nonempty and real. -/
def lambdaMax {N : ℕ} (B : Mat N) : ℝ := sSup (spectrum ℝ B)

def lambdaMin {N : ℕ} (B : Mat N) : ℝ := sInf (spectrum ℝ B)

def lehnerMatrix {N n : ℕ} (A₀ : Mat N) (A : Fin n → Mat N) (Z : Mat N) : Mat N :=
  A₀ + Z + covariance A Z⁻¹

/-- Equation (2), as a finite-dimensional variational quantity. -/
def rhoPlus {N n : ℕ} (A₀ : Mat N) (A : Fin n → Mat N) : ℝ :=
  sInf (Set.range (fun Z : {Z : Mat N // Z.PosDef} => lambdaMax (lehnerMatrix A₀ A Z.val)))

/-- Equation (3), with a supremum over negative definite matrices. -/
def rhoMinus {N n : ℕ} (A₀ : Mat N) (A : Fin n → Mat N) : ℝ :=
  sSup (Set.range (fun Z : {Z : Mat N // (-Z).PosDef} => lambdaMin (lehnerMatrix A₀ A Z.val)))

def rhoStar {N n : ℕ} (A₀ : Mat N) (A : Fin n → Mat N) : ℝ :=
  max (rhoPlus A₀ A) (-rhoMinus A₀ A)

def densityFunctional {N n : ℕ} (A₀ : Mat N) (A : Fin n → Mat N) (C : Density N) : ℝ :=
  (A₀ * C.val).trace.re + 2 * (CFC.sqrt (energy A C.val)).trace.re

theorem lambdaMax_le_iff {N : ℕ} [NeZero N] {B : Mat N} (hB : B.IsHermitian) (r : ℝ) :
    lambdaMax B ≤ r ↔ B ≤ r • (1 : Mat N) := by
  have hs : (spectrum ℝ B).Nonempty := ContinuousFunctionalCalculus.spectrum_nonempty B hB
  rw [show r • (1 : Mat N) = algebraMap ℝ (Mat N) r from (Algebra.algebraMap_eq_smul_one r).symm,
    le_algebraMap_iff_spectrum_le (show IsSelfAdjoint B from hB)]
  exact csSup_le_iff B.finite_real_spectrum.bddAbove hs

theorem le_lambdaMin_iff {N : ℕ} [NeZero N] {B : Mat N} (hB : B.IsHermitian) (r : ℝ) :
    r ≤ lambdaMin B ↔ r • (1 : Mat N) ≤ B := by
  have hs : (spectrum ℝ B).Nonempty := ContinuousFunctionalCalculus.spectrum_nonempty B hB
  rw [show r • (1 : Mat N) = algebraMap ℝ (Mat N) r from (Algebra.algebraMap_eq_smul_one r).symm,
    algebraMap_le_iff_le_spectrum (show IsSelfAdjoint B from hB)]
  exact le_csInf_iff B.finite_real_spectrum.bddBelow hs

theorem density_trace_le_lambdaMax {N : ℕ} [NeZero N] (C : Density N) {B : Mat N}
    (hB : B.IsHermitian) : (B * C.val).trace.re ≤ lambdaMax B := by
  have hb := (lambdaMax_le_iff hB (lambdaMax B)).mp le_rfl
  have h := re_trace_mul_nonneg C.property.1 (Matrix.le_iff.mp hb)
  rw [trace_mul_comm B]
  simpa only [mul_sub, Matrix.mul_smul, mul_one, trace_sub, trace_smul,
    C.property.2, Complex.real_smul, smul_eq_mul, mul_one, Complex.ofReal_re,
    Complex.sub_re, sub_nonneg] using h

/-- Spectral Lipschitz control in the Euclidean operator norm. -/
theorem lambdaMax_sub_le {N : ℕ} [NeZero N] {A B : Mat N}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    lambdaMax A - lambdaMax B ≤ ‖A - B‖ := by
  have hd : A - B ≤ ‖A - B‖ • (1 : Mat N) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (show IsSelfAdjoint (A - B) from hA.sub hB).le_algebraMap_norm_self
  have hb := (lambdaMax_le_iff hB (lambdaMax B)).mp le_rfl
  have ha : A ≤ (lambdaMax B + ‖A - B‖) • (1 : Mat N) := by
    calc A = (A - B) + B := (sub_add_cancel A B).symm
         _ ≤ ‖A - B‖ • (1 : Mat N) + lambdaMax B • (1 : Mat N) := add_le_add hd hb
         _ = _ := by rw [← add_smul, add_comm]
  have h := (lambdaMax_le_iff hA _).mpr ha
  linarith

theorem abs_lambdaMax_sub_le {N : ℕ} [NeZero N] {A B : Mat N}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    |lambdaMax A - lambdaMax B| ≤ ‖A - B‖ := by
  apply abs_le.mpr
  constructor
  · have h := lambdaMax_sub_le hB hA
    rw [norm_sub_rev B A] at h
    linarith
  · exact lambdaMax_sub_le hA hB

theorem lambdaMax_neg {N : ℕ} [NeZero N] {B : Mat N} (hB : B.IsHermitian) :
    lambdaMax (-B) = -lambdaMin B := by
  apply le_antisymm
  · apply (lambdaMax_le_iff hB.neg _).mpr
    have h := (le_lambdaMin_iff hB (lambdaMin B)).mp le_rfl
    simpa only [neg_smul] using neg_le_neg h
  · have h := (lambdaMax_le_iff hB.neg (lambdaMax (-B))).mp le_rfl
    have hb : -lambdaMax (-B) ≤ lambdaMin B := by
      apply (le_lambdaMin_iff hB _).mpr
      simpa only [neg_smul, neg_neg] using neg_le_neg h
    linarith

theorem lambdaMin_neg {N : ℕ} [NeZero N] {B : Mat N} (hB : B.IsHermitian) :
    lambdaMin (-B) = -lambdaMax B := by
  have h := lambdaMax_neg hB.neg
  simp only [neg_neg] at h
  linarith

theorem abs_lambdaMin_sub_le {N : ℕ} [NeZero N] {A B : Mat N}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    |lambdaMin A - lambdaMin B| ≤ ‖A - B‖ := by
  have h := abs_lambdaMax_sub_le hA.neg hB.neg
  rw [lambdaMax_neg hA, lambdaMax_neg hB] at h
  simpa only [neg_sub_neg, norm_sub_rev B A, abs_sub_comm] using h

/-- The operator norm is exactly the larger absolute spectral edge. -/
theorem opNorm_eq_max_edges {N : ℕ} [NeZero N] {B : Mat N} (hB : B.IsHermitian) :
    ‖B‖ = max (lambdaMax B) (-lambdaMin B) := by
  apply le_antisymm
  · rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum B (show IsSelfAdjoint B from hB) with h | h
    · exact (le_csSup B.finite_real_spectrum.bddAbove h).trans (le_max_left _ _)
    · have hi := csInf_le B.finite_real_spectrum.bddBelow h
      change lambdaMin B ≤ -‖B‖ at hi
      exact (by linarith : ‖B‖ ≤ -lambdaMin B).trans (le_max_right _ _)
  · apply max_le
    · apply (lambdaMax_le_iff hB _).mpr
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (show IsSelfAdjoint B from hB).le_algebraMap_norm_self
    · have h := (le_lambdaMin_iff hB (-‖B‖)).mpr (by
        simpa only [Algebra.algebraMap_eq_smul_one, neg_smul] using
          (show IsSelfAdjoint B from hB).neg_algebraMap_norm_le_self)
      linarith

theorem lehnerMatrix_hermitian {N n : ℕ} (A₀ : Mat N) (A : Fin n → Mat N)
    (h₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (Z : Mat N) (hZ : Z.PosDef) :
    (lehnerMatrix A₀ A Z).IsHermitian :=
  (h₀.add hZ.isHermitian).add (covariance_posSemidef A Z⁻¹ hA hZ.posSemidef.inv).isHermitian

/-- The pointwise inequality which replaces the Sion minimax step for the main
upper bound. No minimax equality or free-edge formula is assumed. -/
theorem densityFunctional_le_lehnerMatrix {N n : ℕ} [NeZero N]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (C : Density N) (Z : Mat N) (hZ : Z.PosDef) :
    densityFunctional A₀ A C ≤ lambdaMax (lehnerMatrix A₀ A Z) := by
  have hη := covariance_posSemidef A C.val hA C.property.1
  have h := weighted_trace_amgm C.property.1 hη hZ
  have ht : (covariance A C.val * Z⁻¹).trace = (covariance A Z⁻¹ * C.val).trace := by
    simp only [covariance, Finset.sum_mul, trace_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc (A i * C.val * A i * Z⁻¹).trace = ((A i * C.val) * (A i * Z⁻¹)).trace := by
           simp only [Matrix.mul_assoc]
         _ = ((A i * Z⁻¹) * (A i * C.val)).trace := trace_mul_comm _ _
         _ = (A i * Z⁻¹ * A i * C.val).trace := by simp only [Matrix.mul_assoc]
  have hb := density_trace_le_lambdaMax C (lehnerMatrix_hermitian A₀ A h₀ hA Z hZ)
  simp only [lehnerMatrix, add_mul, trace_add, Complex.add_re] at hb
  rw [ht, trace_mul_comm C.val Z] at h
  unfold densityFunctional energy lehnerMatrix
  linarith

/-- The density-matrix upper bound of Remark 3.6, sufficient for Theorem 7.2. -/
theorem densityFunctional_le_rhoPlus {N n : ℕ} [NeZero N]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (C : Density N) :
    densityFunctional A₀ A C ≤ rhoPlus A₀ A := by
  apply le_csInf
  · exact ⟨_, ⟨⟨1, Matrix.PosDef.one⟩, rfl⟩⟩
  · rintro _ ⟨Z, rfl⟩
    exact densityFunctional_le_lehnerMatrix A₀ A h₀ hA C Z.val Z.property

end LehnerEdges

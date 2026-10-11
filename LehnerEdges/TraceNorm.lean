import LehnerEdges.MatrixBasics
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Rectangular Schatten 1-norm estimates for Section 5. -/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace LehnerEdges

theorem re_trace_mono {N : ℕ} {A B : Mat N} (h : A ≤ B) :
    A.trace.re ≤ B.trace.re := by
  have hp := (Complex.nonneg_iff.mp (Matrix.le_iff.mp h).trace_nonneg).1
  simpa only [trace_sub, Complex.sub_re, sub_nonneg] using hp

theorem traceNorm_nonneg {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :
    0 ≤ traceNorm A :=
  (Complex.nonneg_iff.mp (CFC.sqrt_nonneg _).posSemidef.trace_nonneg).1

theorem mul_adjoint_le {N M : ℕ} (B : Matrix (Fin N) (Fin M) ℂ) :
    B * B.conjTranspose ≤ ‖B‖ ^ 2 • (1 : Mat N) := by
  have h : IsSelfAdjoint (B * B.conjTranspose) :=
    (Matrix.posSemidef_self_mul_conjTranspose B).isHermitian
  have hn : ‖B * B.conjTranspose‖ = ‖B‖ ^ 2 := by
    simpa only [conjTranspose_conjTranspose, l2_opNorm_conjTranspose, pow_two] using
      l2_opNorm_conjTranspose_mul_self B.conjTranspose
  simpa only [Algebra.algebraMap_eq_smul_one, hn] using h.le_algebraMap_norm_self

theorem adjoint_mul_le {N M : ℕ} (B : Matrix (Fin N) (Fin M) ℂ) :
    B.conjTranspose * B ≤ ‖B‖ ^ 2 • (1 : Mat M) := by
  simpa only [conjTranspose_conjTranspose, l2_opNorm_conjTranspose] using
    mul_adjoint_le B.conjTranspose

theorem conjugate_mono {L N : ℕ} (A : Matrix (Fin L) (Fin N) ℂ)
    {P Q : Mat N} (h : P ≤ Q) :
    A * P * A.conjTranspose ≤ A * Q * A.conjTranspose := by
  exact Matrix.le_iff.mpr (by
    simpa only [Matrix.mul_sub, Matrix.sub_mul] using
      (Matrix.le_iff.mp h).mul_mul_conjTranspose_same A)

theorem sqrt_smul_sq {N : ℕ} (P : Mat N) (hP : P.PosSemidef)
    {r : ℝ} (hr : 0 ≤ r) : CFC.sqrt (r ^ 2 • P) = r • CFC.sqrt P := by
  apply (CFC.sqrt_eq_iff _ _ (smul_nonneg (sq_nonneg r) hP.nonneg)
    (smul_nonneg hr (CFC.sqrt_nonneg P))).mpr
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
    CFC.sqrt_mul_sqrt_self P hP.nonneg, pow_two]

/-- The pointwise rectangular ideal estimate used in Proposition 5.2. -/
theorem traceNorm_mul_le {L N M : ℕ} (A : Matrix (Fin L) (Fin N) ℂ)
    (B : Matrix (Fin N) (Fin M) ℂ) :
    traceNorm (A * B) ≤ ‖B‖ * traceNorm A := by
  have h := conjugate_mono A (mul_adjoint_le B)
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at h
  have hs := CFC.sqrt_le_sqrt _ _ h
  simp only [sqrt_smul_sq _ (Matrix.posSemidef_self_mul_conjTranspose A)
    (norm_nonneg B)] at hs
  have ht := re_trace_mono hs
  simpa only [traceNorm, conjTranspose_mul, Matrix.mul_assoc, trace_smul,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using ht

theorem frobeniusSq_adjoint {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :
    frobeniusSq A.conjTranspose = frobeniusSq A := by
  simp only [frobeniusSq, conjTranspose_conjTranspose, trace_mul_comm A]

/-- The Frobenius ideal property, with the Euclidean operator norm. -/
theorem frobeniusSq_mul_le {L N M : ℕ} (A : Matrix (Fin L) (Fin N) ℂ)
    (B : Matrix (Fin N) (Fin M) ℂ) :
    frobeniusSq (A * B) ≤ ‖A‖ ^ 2 * frobeniusSq B := by
  have h := conjugate_mono B.conjTranspose (adjoint_mul_le A)
  simp only [conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one] at h
  have ht := re_trace_mono h
  simpa only [frobeniusSq, conjTranspose_mul, Matrix.mul_assoc, trace_smul,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using ht

/-- The Euclidean operator norm is at most the Frobenius norm. -/
theorem opNorm_le_frobenius {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :
    ‖A‖ ≤ Real.sqrt (frobeniusSq A) := by
  rw [l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
  rw [mul_pow, Real.sq_sqrt (frobeniusSq_nonneg A)]
  change ‖WithLp.toLp 2 (A *ᵥ x.ofLp)‖ ^ 2 ≤ frobeniusSq A * ‖x‖ ^ 2
  rw [EuclideanSpace.norm_sq_eq]
  have hrow (i : Fin N) : ‖(A *ᵥ x.ofLp) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * ‖x‖ ^ 2 := by
    let r : EuclideanSpace ℂ (Fin M) := WithLp.toLp 2 (fun j => star (A i j))
    have h := norm_inner_le_norm (𝕜 := ℂ) r x
    have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
    have hr : ‖r‖ ^ 2 = ∑ j, ‖A i j‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, r, norm_star]
    rw [mul_pow, hr] at hh
    simpa [PiLp.inner_apply, RCLike.inner_apply, r, mul_comm, mulVec, dotProduct] using hh
  calc (∑ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2) ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ‖x‖ ^ 2 :=
         Finset.sum_le_sum fun i _ => hrow i
       _ = frobeniusSq A * ‖x‖ ^ 2 := by rw [← Finset.sum_mul, frobeniusSq_eq_sum]

theorem opNorm_sq_le_frobeniusSq {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :
    ‖A‖ ^ 2 ≤ frobeniusSq A := by
  have h := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr (opNorm_le_frobenius A)
  simpa only [Real.sq_sqrt (frobeniusSq_nonneg A)] using h

/-- Generalized inverse square root. The total inverse gives zero on the kernel. -/
def inverseSqrt {N : ℕ} (E : Mat N) : Mat N :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) E

theorem inverseSqrt_hermitian {N : ℕ} (E : Mat N) :
    (inverseSqrt E).IsHermitian := IsSelfAdjoint.cfc

theorem inverseSqrt_mul {N : ℕ} (E : Mat N) (hE : E.PosSemidef) :
    inverseSqrt E * E = CFC.sqrt E := by
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ E) :=
    E.finite_real_spectrum.continuousOn g
  have hi : cfc (fun x : ℝ => x) E = E := cfc_id' ℝ E
  change cfc f E * E = _
  calc cfc f E * E = cfc f E * cfc (fun x : ℝ => x) E :=
         congrArg (fun T => cfc f E * T) hi.symm
       _ = cfc (fun x => f x * x) E := (cfc_mul _ _ _ (hc f) (hc id)).symm
       _ = CFC.sqrt E := by
        rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real NNReal.sqrt E hE.nonneg]
        apply cfc_congr
        intro x hx
        have hx0 : 0 ≤ x := by
          obtain ⟨i, rfl⟩ := hE.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
          exact hE.eigenvalues_nonneg i
        simp only [f, Real.coe_sqrt, Real.coe_toNNReal', max_eq_left hx0]
        by_cases hxz : x = 0
        · simp [hxz]
        · have hs : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hx0 (Ne.symm hxz))
          calc (Real.sqrt x)⁻¹ * x = (Real.sqrt x)⁻¹ * (Real.sqrt x * Real.sqrt x) := by
                 rw [Real.mul_self_sqrt hx0]
               _ = Real.sqrt x := by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

/-- A polar contraction for every rectangular matrix, with no rank assumption. -/
def polarContraction {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :=
  inverseSqrt (A * A.conjTranspose) * A

theorem polarContraction_mul_adjoint {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :
    polarContraction A * A.conjTranspose = CFC.sqrt (A * A.conjTranspose) := by
  rw [polarContraction, Matrix.mul_assoc,
    inverseSqrt_mul _ (Matrix.posSemidef_self_mul_conjTranspose A)]

theorem sqrt_eq_real_cfc {N : ℕ} (E : Mat N) (hE : E.PosSemidef) :
    CFC.sqrt E = cfc Real.sqrt E := by
  rw [CFC.sqrt_eq_real_sqrt E hE.nonneg, cfcₙ_eq_cfc]

theorem polarContraction_norm_le {N M : ℕ} (A : Matrix (Fin N) (Fin M) ℂ) :
    ‖polarContraction A‖ ≤ 1 := by
  let E := A * A.conjTranspose
  have hE : E.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ E) :=
    E.finite_real_spectrum.continuousOn g
  have hp : polarContraction A * (polarContraction A).conjTranspose =
      cfc (fun x : ℝ => Real.sqrt x * (Real.sqrt x)⁻¹) E := by
    calc _ = inverseSqrt E * E * inverseSqrt E := by
           simp only [polarContraction, E, conjTranspose_mul,
             (inverseSqrt_hermitian _).eq, Matrix.mul_assoc]
         _ = CFC.sqrt E * inverseSqrt E := by rw [inverseSqrt_mul E hE]
         _ = _ := by
           rw [sqrt_eq_real_cfc E hE, inverseSqrt,
             ← cfc_mul _ _ _ (hc _) (hc _)]
  have hp1 : polarContraction A * (polarContraction A).conjTranspose ≤ (1 : Mat N) := by
    rw [hp]
    apply cfc_le_one
    intro x _
    by_cases hx : Real.sqrt x = 0
    · simp [hx]
    · simp [hx]
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (Matrix.posSemidef_self_mul_conjTranspose (polarContraction A)).nonneg).mpr hp1
  have heq : ‖polarContraction A * (polarContraction A).conjTranspose‖ =
      ‖polarContraction A‖ ^ 2 := by
    simpa only [conjTranspose_conjTranspose, l2_opNorm_conjTranspose, pow_two] using
      l2_opNorm_conjTranspose_mul_self (polarContraction A).conjTranspose
  rw [heq] at hn
  nlinarith [norm_nonneg (polarContraction A)]

/-- The Schatten Cauchy–Schwarz estimate, without rank or dimension restrictions. -/
theorem traceNorm_mul_le_frobenius {L N M : ℕ}
    (A : Matrix (Fin L) (Fin N) ℂ) (B : Matrix (Fin N) (Fin M) ℂ) :
    traceNorm (A * B) ≤ Real.sqrt (frobeniusSq A) * Real.sqrt (frobeniusSq B) := by
  let K := polarContraction (A * B)
  have heq : traceNorm (A * B) = (A.conjTranspose * (K * B.conjTranspose)).trace.re := by
    rw [traceNorm, ← polarContraction_mul_adjoint, conjTranspose_mul,
      ← Matrix.mul_assoc, trace_mul_cycle K]
    simp only [Matrix.mul_assoc, K]
  have hcs := trace_cauchy_schwarz_sq A (K * B.conjTranspose)
  have hi := frobeniusSq_mul_le K B.conjTranspose
  have hk : ‖K‖ ^ 2 ≤ 1 := by
    have := polarContraction_norm_le (A * B)
    nlinarith [norm_nonneg K]
  have hib : frobeniusSq (K * B.conjTranspose) ≤ frobeniusSq B := by
    calc _ ≤ ‖K‖ ^ 2 * frobeniusSq B.conjTranspose := hi
         _ ≤ 1 * frobeniusSq B.conjTranspose := mul_le_mul_of_nonneg_right hk (frobeniusSq_nonneg _)
         _ = _ := by rw [one_mul, frobeniusSq_adjoint]
  have hre := Complex.abs_re_le_norm (A.conjTranspose * (K * B.conjTranspose)).trace
  have hre2 := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hre
  rw [sq_abs, ← heq] at hre2
  have hab := mul_le_mul_of_nonneg_left hib (frobeniusSq_nonneg A)
  have hsq : traceNorm (A * B) ^ 2 ≤ frobeniusSq A * frobeniusSq B :=
    hre2.trans (hcs.trans hab)
  have hsA := Real.sq_sqrt (frobeniusSq_nonneg A)
  have hsB := Real.sq_sqrt (frobeniusSq_nonneg B)
  have hpos : 0 ≤ Real.sqrt (frobeniusSq A) * Real.sqrt (frobeniusSq B) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ (traceNorm_nonneg _) hpos).mp
  simpa only [mul_pow, hsA, hsB] using hsq

end LehnerEdges

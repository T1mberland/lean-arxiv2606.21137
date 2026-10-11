import LehnerEdges.SignedComparison
import Mathlib.Analysis.Matrix.Spectrum

/-! Exact operator norm as a signed Rayleigh supremum. This statement uses
the actual Euclidean matrix operator norm, not a process-defined surrogate. -/

noncomputable section
open Matrix
open scoped InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace LehnerEdges

abbrev ComplexUnitSphere (κ : Type*) [Fintype κ] := {z : EuclideanSpace ℂ κ // ‖z‖ = 1}

def matrixRayleigh {κ : Type*} [Fintype κ] (B : Matrix κ κ ℂ) (u : ComplexUnitSphere κ) : ℝ :=
  (inner ℂ u.val ((EuclideanSpace.equiv κ ℂ).symm (B *ᵥ u.val))).re

def signedMatrixRayleigh {κ : Type*} [Fintype κ]
    (B : Matrix κ κ ℂ) (p : Bool × ComplexUnitSphere κ) : ℝ := signVector p.1 (matrixRayleigh B p.2)

theorem abs_matrixRayleigh_le_norm {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : Matrix κ κ ℂ) (u : ComplexUnitSphere κ) : |matrixRayleigh B u| ≤ ‖B‖ := by
  unfold matrixRayleigh
  calc
    _ ≤ ‖inner ℂ u.val ((EuclideanSpace.equiv κ ℂ).symm (B *ᵥ u.val))‖ := Complex.abs_re_le_norm _
    _ ≤ ‖u.val‖ * ‖(EuclideanSpace.equiv κ ℂ).symm (B *ᵥ u.val)‖ := norm_inner_le_norm _ _
    _ ≤ ‖B‖ := by
      rw [u.property, one_mul]
      simpa only [u.property, mul_one] using Matrix.l2_opNorm_mulVec B u.val

theorem signedMatrixRayleigh_le_norm {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : Matrix κ κ ℂ) (p : Bool × ComplexUnitSphere κ) : signedMatrixRayleigh B p ≤ ‖B‖ := by
  have h := abs_matrixRayleigh_le_norm B p.2
  cases hb : p.1
  · simpa only [signedMatrixRayleigh, signVector, hb, Bool.false_eq_true, ↓reduceIte] using
      (neg_le_abs _).trans h
  · simpa only [signedMatrixRayleigh, signVector, hb, ↓reduceIte] using
      (le_abs_self _).trans h

theorem eigenvector_matrixRayleigh {κ : Type*} [Fintype κ] [DecidableEq κ]
    {B : Matrix κ κ ℂ} (hB : B.IsHermitian) (i : κ) :
    matrixRayleigh B ⟨hB.eigenvectorBasis i, hB.eigenvectorBasis.norm_eq_one i⟩ = hB.eigenvalues i := by
  unfold matrixRayleigh
  rw [hB.mulVec_eigenvectorBasis i]
  change (inner ℂ (hB.eigenvectorBasis i) ((hB.eigenvalues i : ℂ) • hB.eigenvectorBasis i)).re = _
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hB.eigenvectorBasis.norm_eq_one]
  simp

theorem norm_mem_range_signedMatrixRayleigh {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {B : Matrix κ κ ℂ} (hB : B.IsHermitian) : ‖B‖ ∈ Set.range (signedMatrixRayleigh B) := by
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum B (show IsSelfAdjoint B from hB) with h | h
  · rw [hB.spectrum_real_eq_range_eigenvalues] at h
    obtain ⟨i, hi⟩ := h
    refine ⟨(true, ⟨hB.eigenvectorBasis i, hB.eigenvectorBasis.norm_eq_one i⟩), ?_⟩
    simpa only [signedMatrixRayleigh, signVector, ↓reduceIte, eigenvector_matrixRayleigh] using hi
  · rw [hB.spectrum_real_eq_range_eigenvalues] at h
    obtain ⟨i, hi⟩ := h
    refine ⟨(false, ⟨hB.eigenvectorBasis i, hB.eigenvectorBasis.norm_eq_one i⟩), ?_⟩
    simp only [signedMatrixRayleigh, signVector, Bool.false_eq_true, ↓reduceIte,
      eigenvector_matrixRayleigh, hi, neg_neg]

theorem opNorm_eq_signed_rayleigh_sup {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {B : Matrix κ κ ℂ} (hB : B.IsHermitian) :
    ‖B‖ = sSup (Set.range (signedMatrixRayleigh B)) := by
  apply le_antisymm
  · apply le_csSup
    · exact ⟨‖B‖, by rintro _ ⟨p, rfl⟩; exact signedMatrixRayleigh_le_norm B p⟩
    · exact norm_mem_range_signedMatrixRayleigh hB
  · apply csSup_le ⟨‖B‖, norm_mem_range_signedMatrixRayleigh hB⟩
    rintro _ ⟨p, rfl⟩
    exact signedMatrixRayleigh_le_norm B p

end LehnerEdges

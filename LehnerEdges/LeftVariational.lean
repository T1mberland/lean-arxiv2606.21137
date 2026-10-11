import LehnerEdges.Variational
import Mathlib.Tactic.Abel

/-! Sign symmetry of the finite variational edges. This does not invoke any
free operator or a minimax equality. -/

noncomputable section
open Matrix
open scoped Pointwise MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace LehnerEdges

theorem posDef_inv_neg {N : ℕ} {Z : Mat N} (hZ : Z.PosDef) : (-Z)⁻¹ = -Z⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [neg_mul_neg]
  exact Matrix.nonsing_inv_mul Z (Z.isUnit_iff_isUnit_det.mp hZ.isUnit)

theorem lehnerMatrix_neg_parameter {N n : ℕ} (A₀ : Mat N) (A : Fin n → Mat N)
    {Z : Mat N} (hZ : Z.PosDef) :
    lehnerMatrix A₀ A (-Z) = -lehnerMatrix (-A₀) A Z := by
  simp only [lehnerMatrix, covariance, posDef_inv_neg hZ, Matrix.mul_neg,
    Matrix.neg_mul, Finset.sum_neg_distrib, neg_add_rev, neg_neg]
  abel

theorem lambdaMin_lehner_neg {N n : ℕ} [NeZero N]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {Z : Mat N} (hZ : Z.PosDef) :
    lambdaMin (lehnerMatrix A₀ A (-Z)) = -lambdaMax (lehnerMatrix (-A₀) A Z) := by
  rw [lehnerMatrix_neg_parameter A₀ A hZ,
    lambdaMin_neg (lehnerMatrix_hermitian (-A₀) A h₀.neg hA Z hZ)]

/-- Exact sign symmetry of equations (2) and (3), for arbitrary Hermitian
coefficients. -/
theorem rhoMinus_eq_neg_rhoPlus {N n : ℕ} [NeZero N]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) : rhoMinus A₀ A = -rhoPlus (-A₀) A := by
  let f := fun Z : {Z : Mat N // Z.PosDef} => lambdaMax (lehnerMatrix (-A₀) A Z.val)
  let g := fun Z : {Z : Mat N // (-Z).PosDef} => lambdaMin (lehnerMatrix A₀ A Z.val)
  have hs : Set.range g = (fun r : ℝ => -r) '' Set.range f := by
    ext x
    constructor
    · rintro ⟨Z, rfl⟩
      refine ⟨f ⟨-Z.val, Z.property⟩, ⟨⟨-Z.val, Z.property⟩, rfl⟩, ?_⟩
      have h := lambdaMin_lehner_neg A₀ A h₀ hA Z.property
      simpa only [neg_neg] using h.symm
    · rintro ⟨x, ⟨Z, rfl⟩, rfl⟩
      refine ⟨⟨-Z.val, by simpa only [neg_neg] using Z.property⟩, ?_⟩
      exact lambdaMin_lehner_neg A₀ A h₀ hA Z.property
  change sSup (Set.range g) = -sInf (Set.range f)
  rw [hs]
  simpa only [Set.image_neg_eq_neg] using Real.sSup_neg (Set.range f)

theorem rhoStar_eq_max_rhoPlus {N n : ℕ} [NeZero N]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) :
    rhoStar A₀ A = max (rhoPlus A₀ A) (rhoPlus (-A₀) A) := by
  rw [rhoStar, rhoMinus_eq_neg_rhoPlus A₀ A h₀ hA, neg_neg]

/-- The elementary left-edge density inequality dual to Remark 3.6. -/
theorem rhoMinus_le_densityFunctional {N n : ℕ} [NeZero N]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (C : Density N) :
    rhoMinus A₀ A ≤ (A₀ * C.val).trace.re - 2 * (CFC.sqrt (energy A C.val)).trace.re := by
  rw [rhoMinus_eq_neg_rhoPlus A₀ A h₀ hA]
  have h := densityFunctional_le_rhoPlus (-A₀) A h₀.neg hA C
  simp only [densityFunctional, neg_mul, trace_neg, Complex.neg_re] at h
  linarith

end LehnerEdges

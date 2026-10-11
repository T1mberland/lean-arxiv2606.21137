import LehnerEdges.Variational

/-! Deterministic block matrix estimates in Proposition 5.2. -/

noncomputable section
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace LehnerEdges

def blockRow {n N : ℕ} (B : Fin n → Mat N) : Matrix (Fin N) (Fin (n * N)) ℂ :=
  fun a b => B (finProdFinEquiv.symm b).1 a (finProdFinEquiv.symm b).2

def blockColumn {n N M : ℕ} (Γ : Fin n → Matrix (Fin N) (Fin M) ℂ) :
    Matrix (Fin (n * N)) (Fin M) ℂ :=
  fun a b => Γ (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 b

theorem blockRow_mul_blockColumn {n N M : ℕ} (B : Fin n → Mat N)
    (Γ : Fin n → Matrix (Fin N) (Fin M) ℂ) :
    blockRow B * blockColumn Γ = ∑ i, B i * Γ i := by
  ext a b
  simp only [Matrix.sum_apply, mul_apply, blockRow, blockColumn]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]

theorem blockRow_mul_adjoint {n N : ℕ} (B : Fin n → Mat N) :
    blockRow B * (blockRow B).conjTranspose = ∑ i, B i * (B i).conjTranspose := by
  ext a b
  simp only [Matrix.sum_apply, mul_apply, blockRow, conjTranspose_apply]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]

theorem compressed_block_energy {n N : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) (C : Density N) :
    blockRow (fun i => compressed C.val (A i)) *
      (blockRow (fun i => compressed C.val (A i))).conjTranspose = energy A C.val := by
  rw [blockRow_mul_adjoint, energy_eq_sum_sq A C.val C.property.1]
  apply Finset.sum_congr rfl
  intro i _
  have hb : (compressed C.val (A i)).IsHermitian := by
    simpa [compressed, (CFC.sqrt_nonneg C.val).posSemidef.isHermitian.eq] using
      isHermitian_conjTranspose_mul_mul (CFC.sqrt C.val) (hA i)
  rw [hb.eq, pow_two]

theorem compressed_block_traceNorm {n N : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) (C : Density N) :
    traceNorm (blockRow (fun i => compressed C.val (A i))) =
      (CFC.sqrt (energy A C.val)).trace.re := by
  rw [traceNorm, compressed_block_energy A hA C]

/-- The uniform, pointwise comparison bound, before the Wishart expectation
estimate. It uses precisely the variational `rhoPlus` of equation (2). -/
theorem pointwise_comparison_bound {n N M : ℕ} [NeZero N]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (C : Density N)
    (Γ : Fin n → Matrix (Fin N) (Fin M) ℂ) :
    (A₀ * C.val).trace.re + (2 / Real.sqrt M) *
      traceNorm (∑ i, compressed C.val (A i) * Γ i) ≤
      rhoPlus A₀ A + 2 * max (‖blockColumn Γ‖ / Real.sqrt M - 1) 0 *
        Real.sqrt ‖squareFunction A‖ := by
  let R := blockRow (fun i => compressed C.val (A i))
  let b := (CFC.sqrt (energy A C.val)).trace.re
  let α := ‖blockColumn Γ‖ / Real.sqrt M
  have hb0 : 0 ≤ b :=
    (Complex.nonneg_iff.mp (CFC.sqrt_nonneg _).posSemidef.trace_nonneg).1
  have hb := density_energy_bound A hA C
  have hρ := densityFunctional_le_rhoPlus A₀ A h₀ hA C
  have hi := traceNorm_mul_le R (blockColumn Γ)
  rw [compressed_block_traceNorm A hA C, blockRow_mul_blockColumn] at hi
  have hs : 0 ≤ 2 / Real.sqrt M := div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hi' := mul_le_mul_of_nonneg_left hi hs
  have ha1 : α - 1 ≤ max (α - 1) 0 := le_max_left _ _
  have ha0 : 0 ≤ max (α - 1) 0 := le_max_right _ _
  have hbb := mul_le_mul_of_nonneg_right ha1 hb0
  have hsb := mul_le_mul_of_nonneg_left hb ha0
  change (A₀ * C.val).trace.re + _ ≤ rhoPlus A₀ A + 2 * max (α - 1) 0 * _
  change (A₀ * C.val).trace.re + 2 * b ≤ rhoPlus A₀ A at hρ
  change b ≤ Real.sqrt ‖squareFunction A‖ at hb
  have hia : (2 / Real.sqrt M) * traceNorm (∑ i, compressed C.val (A i) * Γ i) ≤ 2 * α * b := by
    calc _ ≤ (2 / Real.sqrt M) * (‖blockColumn Γ‖ * b) := hi'
         _ = _ := by dsimp [α]; ring
  nlinarith

end LehnerEdges

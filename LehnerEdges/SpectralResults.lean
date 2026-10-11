import LehnerEdges.Theorem72

/-! Spectral edges and concentration for the actual Kronecker matrix. The
product index set is the tensor basis, so its real spectrum is used directly. -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace Kronecker MatrixOrder ComplexOrder Matrix.Norms.L2Operator Pointwise
namespace LehnerEdges

theorem matrixRayleigh_nonneg {κ : Type*} [Fintype κ] [DecidableEq κ]
    {B : Matrix κ κ ℂ} (hB : B.PosSemidef) (u : ComplexUnitSphere κ) :
    0 ≤ matrixRayleigh B u := by
  have h := (Complex.nonneg_iff.mp (hB.dotProduct_mulVec_nonneg u.val)).1
  change 0 ≤ (∑ x, star (u.val x) * (B *ᵥ u.val) x).re at h
  change 0 ≤ (∑ x, (B *ᵥ u.val) x * star (u.val x)).re
  simpa only [mul_comm] using h

theorem matrixRayleigh_one {κ : Type*} [Fintype κ] [DecidableEq κ]
    (u : ComplexUnitSphere κ) : matrixRayleigh (1 : Matrix κ κ ℂ) u = 1 := by
  simp only [matrixRayleigh, Matrix.one_mulVec]
  change (inner ℂ u.val u.val).re = 1
  rw [inner_self_eq_norm_sq_to_K, u.property]
  simp

theorem matrixRayleigh_neg {κ : Type*} [Fintype κ]
    (B : Matrix κ κ ℂ) (u : ComplexUnitSphere κ) :
    matrixRayleigh (-B) u = -matrixRayleigh B u := by
  simp only [matrixRayleigh, Matrix.neg_mulVec, map_neg, inner_neg_right, Complex.neg_re]

theorem matrixRayleigh_le_spectralSup {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {B : Matrix κ κ ℂ} (hB : B.IsHermitian) (u : ComplexUnitSphere κ) :
    matrixRayleigh B u ≤ sSup (spectrum ℝ B) := by
  have hb : B ≤ sSup (spectrum ℝ B) • (1 : Matrix κ κ ℂ) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    apply (le_algebraMap_iff_spectrum_le (show IsSelfAdjoint B from hB)).mpr
    exact fun r hr => le_csSup B.finite_real_spectrum.bddAbove hr
  have h := matrixRayleigh_nonneg (Matrix.le_iff.mp hb) u
  rw [sub_eq_add_neg, matrixRayleigh_add, matrixRayleigh_real_smul,
    matrixRayleigh_one, matrixRayleigh_neg, mul_one] at h
  linarith

theorem spectralSup_eq_rayleighSup {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {B : Matrix κ κ ℂ} (hB : B.IsHermitian) :
    sSup (spectrum ℝ B) = sSup (Set.range (matrixRayleigh B)) := by
  have hs : (spectrum ℝ B).Nonempty := ContinuousFunctionalCalculus.spectrum_nonempty B hB
  have hm := hs.csSup_mem B.finite_real_spectrum
  obtain ⟨i, hi⟩ := (Set.ext_iff.mp hB.spectrum_real_eq_range_eigenvalues _).mp hm
  have hbd : BddAbove (Set.range (matrixRayleigh B)) :=
    ⟨sSup (spectrum ℝ B), by rintro _ ⟨u, rfl⟩; exact matrixRayleigh_le_spectralSup hB u⟩
  apply le_antisymm
  · apply le_csSup hbd
    refine ⟨⟨hB.eigenvectorBasis i, hB.eigenvectorBasis.norm_eq_one i⟩, ?_⟩
    exact (eigenvector_matrixRayleigh hB i).trans hi
  · have hne : (Set.range (matrixRayleigh B)).Nonempty :=
      ⟨_, ⟨⟨hB.eigenvectorBasis i, hB.eigenvectorBasis.norm_eq_one i⟩, rfl⟩⟩
    apply csSup_le hne
    rintro _ ⟨u, rfl⟩
    exact matrixRayleigh_le_spectralSup hB u

theorem transposedGueMatrixModel_spectralSup {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (g : GaussianCoordinates n M M) :
    sSup (spectrum ℝ (transposedGueMatrixModel A₀ A g)) = quadraticGueSup A₀ A g := by
  rw [spectralSup_eq_rayleighSup (transposedGueMatrixModel_hermitian A₀ A h₀ hA g)]
  change sSup (Set.range (fun u : UnitPurification N M =>
    matrixRayleigh (transposedGueMatrixModel A₀ A g) u)) = _
  simp_rw [transposedGueMatrixModel_rayleigh A₀ A hA]
  rfl

theorem gueTransposeIsometry_involutive (n M : ℕ) :
    Function.Involutive (gueTransposeIsometry n M) := by
  intro g
  ext p
  rfl

theorem gueMatrixModel_eq_transposed {n N M : ℕ} (A₀ : Mat N) (A : Fin n → Mat N)
    (g : GaussianCoordinates n M M) :
    gueMatrixModel A₀ A g = transposedGueMatrixModel A₀ A (gueTransposeIsometry n M g) := by
  rw [← gueMatrixModel_transpose, gueTransposeIsometry_involutive]

theorem gueMatrixModel_spectralSup {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) (g : GaussianCoordinates n M M) :
    sSup (spectrum ℝ (gueMatrixModel A₀ A g)) =
      quadraticGueSup A₀ A (gueTransposeIsometry n M g) := by
  rw [gueMatrixModel_eq_transposed, transposedGueMatrixModel_spectralSup A₀ A h₀ hA]

theorem gueMatrixModel_spectralSup_lipschitz {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) :
    LipschitzWith (spectralScale A M)
      (fun g : GaussianCoordinates n M M => sSup (spectrum ℝ (gueMatrixModel A₀ A g))) := by
  have h := (quadraticGueSup_lipschitz A₀ A h₀ hA).comp (gueTransposeIsometry n M).lipschitz
  simpa only [mul_one, Function.comp_def, gueMatrixModel_spectralSup A₀ A h₀ hA] using h

theorem gueMatrixModel_norm_lipschitz {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) :
    LipschitzWith (spectralScale A M)
      (fun g : GaussianCoordinates n M M => ‖gueMatrixModel A₀ A g‖) := by
  have h := ((quadraticGueSup_lipschitz A₀ A h₀ hA).max
    (quadraticGueSup_neg_lipschitz (-A₀) A h₀.neg hA)).comp (gueTransposeIsometry n M).lipschitz
  simpa only [max_self, mul_one, Function.comp_def, gueMatrixModel_eq_transposed,
    transposedGueMatrixModel_norm_eq_max A₀ A h₀ hA] using h

theorem gueMatrixModel_norm_concentration {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian (GaussianCoordinates n M M)).real
      {g | t ≤ ‖gueMatrixModel A₀ A g‖ -
        ∫ h, ‖gueMatrixModel A₀ A h‖ ∂stdGaussian (GaussianCoordinates n M M)} ≤
      Real.exp (-t ^ 2 / (2 * (spectralScale A M : ℝ) ^ 2)) :=
  stdGaussian_measure_ge_le (gueMatrixModel_norm_lipschitz A₀ A h₀ hA) ht

theorem integral_gueMatrixModel_spectralSup {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) :
    (∫ g, sSup (spectrum ℝ (gueMatrixModel A₀ A g))
      ∂stdGaussian (GaussianCoordinates n M M)) =
      ∫ g, quadraticGueSup A₀ A g ∂stdGaussian (GaussianCoordinates n M M) := by
  simp_rw [gueMatrixModel_spectralSup A₀ A h₀ hA]
  conv_rhs => rw [← stdGaussian_map (gueTransposeIsometry n M)]
  symm
  exact integral_map (gueTransposeIsometry n M).continuous.measurable.aemeasurable
    (quadraticGueSup_lipschitz A₀ A h₀ hA).continuous.aestronglyMeasurable

/-- Proposition 5.3, in fact valid for every positive `M`, including the
empty coefficient family. The spectrum is that of the actual matrix. -/
theorem expected_gueMatrixModel_lambdaMax_le {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).PosSemidef) :
    (∫ g, sSup (spectrum ℝ (gueMatrixModel A₀ A g))
      ∂stdGaussian (GaussianCoordinates n M M)) ≤
      rhoPlus A₀ A + 6 * Real.sqrt ((n : ℝ) * N / M) * Real.sqrt ‖squareFunction A‖ := by
  have hpos {n : ℕ} [NeZero n] (B : Fin n → Mat N) (hB : ∀ i, (B i).PosSemidef) :
      (∫ g, sSup (spectrum ℝ (gueMatrixModel A₀ B g))
        ∂stdGaussian (GaussianCoordinates n M M)) ≤
        rhoPlus A₀ B + 6 * Real.sqrt ((n : ℝ) * N / M) * Real.sqrt ‖squareFunction B‖ := by
    rw [integral_gueMatrixModel_spectralSup A₀ B h₀ (fun i => (hB i).isHermitian)]
    exact gaussian_purification_edge_bound_six A₀ B h₀ hB
  by_cases hn : n = 0
  · subst n
    have h := hpos (fun _ : Fin 1 => (0 : Mat N)) (fun _ => Matrix.PosSemidef.zero)
    have hρ : rhoPlus A₀ (fun _ : Fin 1 => (0 : Mat N)) = rhoPlus A₀ A := by
      simp only [rhoPlus, lehnerMatrix, covariance, Finset.univ_unique,
        Finset.sum_singleton, Matrix.zero_mul, Matrix.mul_zero,
        Finset.univ_eq_empty, Finset.sum_empty]
    rw [hρ] at h
    simpa [gueMatrixModel, squareFunction] using h
  · letI : NeZero n := ⟨hn⟩
    exact hpos A hA

theorem gueMatrixModel_neg_input {n N M : ℕ} (A₀ : Mat N) (A : Fin n → Mat N)
    (g : GaussianCoordinates n M M) :
    gueMatrixModel (-A₀) A (-g) = -gueMatrixModel A₀ A g := by
  have hG (i : Fin n) : gueProjection (familyMatrices (-g) i) =
      -gueProjection (familyMatrices g i) := by
    change gueProjection (-familyMatrices g i) = _
    simp only [gueProjection, conjTranspose_neg, ← neg_add, smul_neg]
  have hL (B : Mat N) (C : Mat M) : (-B) ⊗ₖ C = -(B ⊗ₖ C) := by
    ext p q
    simp [Matrix.kroneckerMap]
  have hR (B : Mat N) (C : Mat M) : B ⊗ₖ (-C) = -(B ⊗ₖ C) := by
    ext p q
    simp [Matrix.kroneckerMap]
  simp only [gueMatrixModel, hG, hL, hR,
    Finset.sum_neg_distrib, smul_neg, neg_add_rev]
  exact add_comm _ _

theorem spectralInf_eq_neg_spectralSup_neg {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : Matrix κ κ ℂ) :
    sInf (spectrum ℝ B) = -sSup (spectrum ℝ (-B)) := by
  rw [← spectrum.neg_eq, Real.sSup_neg, neg_neg]

theorem integral_gueMatrixModel_spectralInf {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) :
    (∫ g, sInf (spectrum ℝ (gueMatrixModel A₀ A g))
      ∂stdGaussian (GaussianCoordinates n M M)) =
      -(∫ g, sSup (spectrum ℝ (gueMatrixModel (-A₀) A g))
        ∂stdGaussian (GaussianCoordinates n M M)) := by
  simp_rw [spectralInf_eq_neg_spectralSup_neg, ← gueMatrixModel_neg_input A₀ A]
  rw [integral_neg]
  congr 1
  conv_rhs => rw [← stdGaussian_map (LinearIsometryEquiv.neg ℝ (E := GaussianCoordinates n M M))]
  symm
  exact integral_map (LinearIsometryEquiv.neg ℝ).continuous.measurable.aemeasurable
    (gueMatrixModel_spectralSup_lipschitz (-A₀) A h₀.neg hA).continuous.aestronglyMeasurable

/-- Proposition 6.1, with constant six and the original variational lower
edge. As for the upper edge, `M ≥ N` is not needed by this proof. -/
theorem expected_gueMatrixModel_lambdaMin_ge {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).PosSemidef) :
    rhoMinus A₀ A - 6 * Real.sqrt ((n : ℝ) * N / M) * Real.sqrt ‖squareFunction A‖ ≤
      ∫ g, sInf (spectrum ℝ (gueMatrixModel A₀ A g))
        ∂stdGaussian (GaussianCoordinates n M M) := by
  have hHerm : ∀ i, (A i).IsHermitian := fun i => (hA i).isHermitian
  rw [integral_gueMatrixModel_spectralInf A₀ A h₀ hHerm,
    rhoMinus_eq_neg_rhoPlus A₀ A h₀ hHerm]
  have h := expected_gueMatrixModel_lambdaMax_le (M := M) (-A₀) A h₀.neg hA
  linarith

theorem gueMatrixModel_spectralSup_concentration {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian (GaussianCoordinates n M M)).real
      {g | t ≤ sSup (spectrum ℝ (gueMatrixModel A₀ A g)) -
        ∫ h, sSup (spectrum ℝ (gueMatrixModel A₀ A h))
          ∂stdGaussian (GaussianCoordinates n M M)} ≤
      Real.exp (-t ^ 2 / (2 * (spectralScale A M : ℝ) ^ 2)) :=
  stdGaussian_measure_ge_le (gueMatrixModel_spectralSup_lipschitz A₀ A h₀ hA) ht

theorem gueMatrixModel_negative_spectralSup_lipschitz {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) :
    LipschitzWith (spectralScale A M)
      (fun g : GaussianCoordinates n M M => sSup (spectrum ℝ (-gueMatrixModel A₀ A g))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [← gueMatrixModel_neg_input A₀ A]
  simpa only [dist_neg_neg] using
    (gueMatrixModel_spectralSup_lipschitz (-A₀) A h₀.neg hA).dist_le_mul (-x) (-y)

theorem gueMatrixModel_spectralInf_lipschitz {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).IsHermitian) :
    LipschitzWith (spectralScale A M)
      (fun g : GaussianCoordinates n M M => sInf (spectrum ℝ (gueMatrixModel A₀ A g))) := by
  simp_rw [spectralInf_eq_neg_spectralSup_neg]
  exact (gueMatrixModel_negative_spectralSup_lipschitz A₀ A h₀ hA).neg

end LehnerEdges

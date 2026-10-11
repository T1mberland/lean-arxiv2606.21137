import LehnerEdges

noncomputable section
open Matrix MeasureTheory ProbabilityTheory LehnerEdges
open scoped NNReal InnerProductSpace MatrixOrder Matrix.Norms.L2Operator ComplexOrder

-- Compile against the complete public import, with genuine matrix hypotheses.
example {N M : ℕ} (P Q : Mat N) (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (W V : Stiefel N M) :
    frobeniusSq (W.val.conjTranspose * P * W.val - V.val.conjTranspose * Q * V.val) ≤
      2 * frobeniusSq (P * W.val - Q * V.val) :=
  two_fiber_stiefel_increment hP hQ W V

example {N n : ℕ} [NeZero N] (A₀ : Mat N) (A : Fin n → Mat N)
    (h₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) (C : Density N) :
    densityFunctional A₀ A C ≤ rhoPlus A₀ A :=
  densityFunctional_le_rhoPlus A₀ A h₀ hA C

example {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {n N M : ℕ}
    (A : Fin n → Mat N) (hA : ∀ i, (A i).PosSemidef)
    (C : ι → Density N) (W : ι → Stiefel N M) (a : ι → ℝ) :
    (∫ x, vecMax (a + processMap (fun t => gueCoefficient A (C t) (W t)) x)
      ∂stdGaussian (GaussianCoordinates n M M)) ≤
    ∫ y, vecMax (a + processMap (fun t => complexCoefficient A (C t) (W t)) y)
      ∂stdGaussian (GaussianCoordinates n N M) :=
  finite_density_stiefel_comparison A hA C W a

example {N M : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian (EuclideanSpace ℂ (Fin N × Fin M))).real
      {g | t ≤ ‖complexGaussianMatrix g‖ - ∫ h, ‖complexGaussianMatrix h‖
        ∂stdGaussian (EuclideanSpace ℂ (Fin N × Fin M))} ≤ Real.exp (-t ^ 2) :=
  complex_gaussian_matrix_norm_concentration ht

example {N : ℕ} [NeZero N] (B : Mat N) (hB : B.IsHermitian) :
    ‖B‖ = max (lambdaMax B) (-lambdaMin B) := opNorm_eq_max_edges hB

example {N n : ℕ} [NeZero N] (A₀ : Mat N) (A : Fin n → Mat N)
    (h₀ : A₀.IsHermitian) (hA : ∀ i, (A i).IsHermitian) :
    rhoMinus A₀ A = -rhoPlus (-A₀) A :=
  rhoMinus_eq_neg_rhoPlus A₀ A h₀ hA

example {N : ℕ} (K : Mat N) (hK : K.IsHermitian) :
    (stdGaussian (EuclideanSpace ℂ (Fin N × Fin N))).map
      (fun g => frobeniusPair (gueProjection (matrixOfVector g)) K) =
      gaussianReal 0 (frobeniusSq K).toNNReal := gue_pair_law K hK

example {N M : ℕ} [NeZero N] [NeZero M] :
    (∫ x, ‖realMatrixOfVector x‖ ∂stdGaussian (EuclideanSpace ℝ (Fin N × Fin M))) ≤
      Real.sqrt N + Real.sqrt M := real_gaussian_matrix_norm_mean_le

example {N M : ℕ} [NeZero N] [NeZero M] :
    (∫ g, max (Real.sqrt ‖wishartMatrix (complexGaussianMatrix g)‖ - 1) 0
      ∂stdGaussian (EuclideanSpace ℂ (Fin N × Fin M))) ≤
      3 * Real.sqrt ((N : ℝ) / M) := gaussian_wishart_positive_excess_le_three

example {n N M : ℕ} [NeZero n] [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).PosSemidef) :
    (∫ x, linearSup (fun u : UnitPurification N M =>
        purificationGueCoefficient A (purificationMatrix u)) (purificationDrift A₀) x
      ∂stdGaussian (GaussianCoordinates n M M)) ≤
      rhoPlus A₀ A + 6 * Real.sqrt ((n : ℝ) * N / M) * Real.sqrt ‖squareFunction A‖ :=
  gaussian_purification_edge_bound_six A₀ A h₀ hA

example {N : ℕ} [NeZero N] {B : Mat N} (hB : B.IsHermitian) :
    ‖B‖ = sSup (Set.range (signedMatrixRayleigh B)) := opNorm_eq_signed_rayleigh_sup hB

example {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).PosSemidef) :
    (∫ x, linearSup (signedPurificationGueCoefficient (M := M) A)
        (signedPurificationDrift A₀) x ∂stdGaussian (GaussianCoordinates n M M)) ≤
    ∫ y, linearSup (signedPurificationComplexCoefficient (M := M) A)
        (signedPurificationDrift A₀) y
      ∂stdGaussian (EuclideanSpace ℂ (Bool × (Fin n × Fin N × Fin M))) :=
  full_signed_purification_comparison A₀ A h₀ hA

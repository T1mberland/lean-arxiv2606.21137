import LehnerEdges.PurificationComparison

/-! A simultaneous comparison for both spectral signs. The comparison uses
independent rectangular Gaussian blocks for the two signs. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace LehnerEdges

def signVector {E : Type*} [Neg E] (b : Bool) (v : E) : E := if b then v else -v

def signEmbed {ι : Type*} [Fintype ι] (b : Bool) (v : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (Bool × ι) :=
  WithLp.toLp 2 (fun j => if j.1 = b then v j.2 else 0)

theorem signEmbed_norm_sq {ι : Type*} [Fintype ι] (b : Bool) (v : EuclideanSpace ℂ ι) :
    ‖signEmbed b v‖ ^ 2 = ‖v‖ ^ 2 := by
  cases b <;> simp [EuclideanSpace.norm_sq_eq, signEmbed, Fintype.sum_prod_type]

theorem signEmbed_norm {ι : Type*} [Fintype ι] (b : Bool) (v : EuclideanSpace ℂ ι) :
    ‖signEmbed b v‖ = ‖v‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (signEmbed_norm_sq b v)

theorem signEmbed_sub_same {ι : Type*} [Fintype ι] (b : Bool)
    (v w : EuclideanSpace ℂ ι) : signEmbed b v - signEmbed b w = signEmbed b (v - w) := by
  ext j
  simp only [signEmbed, PiLp.sub_apply, PiLp.toLp_apply]
  split_ifs <;> simp

theorem signEmbed_sub_distinct {ι : Type*} [Fintype ι] (b c : Bool) (hbc : b ≠ c)
    (v w : EuclideanSpace ℂ ι) :
    ‖signEmbed b v - signEmbed c w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  cases b <;> cases c <;>
    simp_all [EuclideanSpace.norm_sq_eq, signEmbed, Fintype.sum_prod_type, add_comm]

theorem norm_add_sq_le_twice {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem signed_increment {E ι κ : Type*} [NormedAddCommGroup E] [Fintype κ]
    (v : ι → E) (w : ι → EuclideanSpace ℂ κ)
    (hinc : ∀ i j, ‖v i - v j‖ ^ 2 ≤ ‖w i - w j‖ ^ 2)
    (hnorm : ∀ i, ‖w i‖ ^ 2 = 2 * ‖v i‖ ^ 2)
    (p q : Bool × ι) :
    ‖signVector p.1 (v p.2) - signVector q.1 (v q.2)‖ ^ 2 ≤
      ‖signEmbed p.1 (w p.2) - signEmbed q.1 (w q.2)‖ ^ 2 := by
  by_cases hb : p.1 = q.1
  · rw [← hb, signEmbed_sub_same, signEmbed_norm_sq]
    cases hp : p.1 <;> simp only [signVector, hp, Bool.false_eq_true, ↓reduceIte,
      neg_sub_neg, norm_sub_rev] <;> exact hinc p.2 q.2
  · rw [signEmbed_sub_distinct _ _ hb, hnorm, hnorm]
    have h := norm_add_sq_le_twice (v p.2) (v q.2)
    have hn : -v p.2 - v q.2 = -(v p.2 + v q.2) := by abel
    cases hp : p.1 <;> cases hq : q.1
    · exact False.elim (hb (hp.trans hq.symm))
    · simp only [signVector, hp, hq, Bool.false_eq_true, ↓reduceIte, hn, norm_neg]
      linarith
    · simp only [signVector, hp, hq, Bool.false_eq_true, ↓reduceIte, sub_neg_eq_add]
      linarith
    · exact False.elim (hb (hp.trans hq.symm))

theorem purification_coefficient_norm_ratio {n N M : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).IsHermitian) (S : Matrix (Fin N) (Fin M) ℂ) :
    ‖purificationComplexCoefficient A S‖ ^ 2 = 2 * ‖purificationGueCoefficient A S‖ ^ 2 := by
  simp only [purificationComplexCoefficient, purificationGueCoefficient,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, familyVector_norm_sq,
    purification_rectangular_frobeniusSq, purification_frobeniusSq S (hA _),
    div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem signed_purification_increment {n N M : ℕ} (A : Fin n → Mat N)
    (hA : ∀ i, (A i).PosSemidef) (p q : Bool × UnitPurification N M) :
    ‖signVector p.1 (purificationGueCoefficient A (purificationMatrix p.2)) -
      signVector q.1 (purificationGueCoefficient A (purificationMatrix q.2))‖ ^ 2 ≤
    ‖signEmbed p.1 (purificationComplexCoefficient A (purificationMatrix p.2)) -
      signEmbed q.1 (purificationComplexCoefficient A (purificationMatrix q.2))‖ ^ 2 := by
  apply signed_increment
    (fun u : UnitPurification N M => purificationGueCoefficient A (purificationMatrix u))
    (fun u : UnitPurification N M => purificationComplexCoefficient A (purificationMatrix u))
  · exact fun u v => purification_coefficient_increment A hA _ _
  · exact fun u => purification_coefficient_norm_ratio A (fun i => (hA i).isHermitian) _

theorem continuous_signEmbed {ι : Type*} [Fintype ι] (b : Bool) :
    Continuous (signEmbed (ι := ι) b) := by
  unfold signEmbed
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  by_cases h : j.1 = b <;> simp only [h, ↓reduceIte] <;> fun_prop

def signedPurificationGueCoefficient {n N M : ℕ} (A : Fin n → Mat N)
    (p : Bool × UnitPurification N M) : GaussianCoordinates n M M :=
  signVector p.1 (purificationGueCoefficient A (purificationMatrix p.2))

def signedPurificationComplexCoefficient {n N M : ℕ} (A : Fin n → Mat N)
    (p : Bool × UnitPurification N M) :
    EuclideanSpace ℂ (Bool × (Fin n × Fin N × Fin M)) :=
  signEmbed p.1 (purificationComplexCoefficient A (purificationMatrix p.2))

def signedPurificationDrift {N M : ℕ} (A₀ : Mat N)
    (p : Bool × UnitPurification N M) : ℝ :=
  purificationDrift (if p.1 then A₀ else -A₀) p.2

/-- Compare both signs simultaneously to independent rectangular Gaussian
blocks. The left supremum is the absolute Rayleigh supremum once identified
with the matrix model. -/
theorem full_signed_purification_comparison {n N M : ℕ} [NeZero N] [NeZero M]
    (A₀ : Mat N) (A : Fin n → Mat N) (h₀ : A₀.IsHermitian)
    (hA : ∀ i, (A i).PosSemidef) :
    (∫ x, linearSup (signedPurificationGueCoefficient (M := M) A)
        (signedPurificationDrift A₀) x ∂stdGaussian (GaussianCoordinates n M M)) ≤
    ∫ y, linearSup (signedPurificationComplexCoefficient (M := M) A)
        (signedPurificationDrift A₀) y
      ∂stdGaussian (EuclideanSpace ℂ (Bool × (Fin n × Fin N × Fin M))) := by
  have hcoef := (continuous_purificationGueCoefficient (M := M) A).comp continuous_purificationMatrix
  have hrect := (continuous_purificationComplexCoefficient (M := M) A).comp continuous_purificationMatrix
  apply separable_linear_gaussian_comparison _ _ _
    ⟨Real.sqrt ‖squareFunction A‖ / Real.sqrt M,
      div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)⟩
    ⟨(Real.sqrt 2 / Real.sqrt M) * Real.sqrt ‖squareFunction A‖,
      mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)⟩
  · intro p
    change ‖signedPurificationGueCoefficient A p‖ ≤ Real.sqrt ‖squareFunction A‖ / Real.sqrt M
    have h := purificationGueCoefficient_norm_le A (fun i => (hA i).isHermitian)
      (purificationMatrix p.2) (purificationMatrix_frobeniusSq p.2)
    cases hb : p.1 <;> simpa [signedPurificationGueCoefficient, signVector, hb] using h
  · intro p
    rw [signedPurificationComplexCoefficient, signEmbed_norm]
    exact purificationComplexCoefficient_norm_le A (fun i => (hA i).isHermitian)
      (purificationMatrix p.2) (purificationMatrix_frobeniusSq p.2)
  · refine ⟨‖A₀‖, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hc := purificationMatrix_frobeniusSq p.2
    have htrace (B : Mat N) (hB : B.IsHermitian) : purificationDrift B p.2 ≤ ‖B‖ := by
      have h := density_trace_le_norm (purificationDensity (purificationMatrix p.2) hc) B hB
      change (B * (purificationMatrix p.2 * (purificationMatrix p.2).conjTranspose)).trace.re ≤ ‖B‖
      rw [Matrix.trace_mul_comm]
      exact h
    cases hb : p.1
    · simpa [signedPurificationDrift, hb] using htrace (-A₀) h₀.neg
    · simpa [signedPurificationDrift, hb] using htrace A₀ h₀
  · apply continuous_prod_of_discrete_left.mpr
    intro b
    cases b <;> simp only [signedPurificationGueCoefficient, signVector, ↓reduceIte]
    · exact hcoef.neg
    · exact hcoef
  · apply continuous_prod_of_discrete_left.mpr
    intro b
    exact (continuous_signEmbed b).comp hrect
  · apply continuous_prod_of_discrete_left.mpr
    intro b
    cases b <;> exact continuous_purificationDrift _
  · exact signed_purification_increment A hA

end LehnerEdges

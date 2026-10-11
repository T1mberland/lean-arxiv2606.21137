import LehnerEdges.CompactComparison
import LehnerEdges.GaussianMoments

/-! The elementary real Gaussian matrix comparison: the bilinear process on
two unit spheres is dominated by the sum of two independent linear processes.
All expectations use Mathlib's standard Gaussian measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
namespace LehnerEdges

abbrev RealUnitSphere (d : ℕ) := {x : EuclideanSpace ℝ (Fin d) // ‖x‖ = 1}

instance realUnitSphere_nonempty {d : ℕ} [NeZero d] : Nonempty (RealUnitSphere d) := by
  refine ⟨⟨EuclideanSpace.single 0 1, ?_⟩⟩
  simp

def realOuterVector {N M : ℕ} (u : EuclideanSpace ℝ (Fin N))
    (v : EuclideanSpace ℝ (Fin M)) : EuclideanSpace ℝ (Fin N × Fin M) :=
  WithLp.toLp 2 (fun ij => u ij.1 * v ij.2)

def realJoinVector {N M : ℕ} (u : EuclideanSpace ℝ (Fin N))
    (v : EuclideanSpace ℝ (Fin M)) : EuclideanSpace ℝ (Fin N ⊕ Fin M) :=
  WithLp.toLp 2 (Sum.elim u v)

theorem realOuterVector_inner {N M : ℕ} (u u' : EuclideanSpace ℝ (Fin N))
    (v v' : EuclideanSpace ℝ (Fin M)) :
    inner ℝ (realOuterVector u v) (realOuterVector u' v') =
      inner ℝ u u' * inner ℝ v v' := by
  simp only [realOuterVector, PiLp.inner_apply, Real.inner_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realJoinVector_inner {N M : ℕ} (u u' : EuclideanSpace ℝ (Fin N))
    (v v' : EuclideanSpace ℝ (Fin M)) :
    inner ℝ (realJoinVector u v) (realJoinVector u' v') =
      inner ℝ u u' + inner ℝ v v' := by
  simp [realJoinVector, PiLp.inner_apply, Fintype.sum_sum_type]

theorem realOuterVector_norm_sq {N M : ℕ} (u : EuclideanSpace ℝ (Fin N))
    (v : EuclideanSpace ℝ (Fin M)) :
    ‖realOuterVector u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, realOuterVector_inner,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

theorem realJoinVector_norm_sq {N M : ℕ} (u : EuclideanSpace ℝ (Fin N))
    (v : EuclideanSpace ℝ (Fin M)) :
    ‖realJoinVector u v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, realJoinVector_inner,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

theorem real_matrix_process_increment {N M : ℕ}
    (p q : RealUnitSphere N × RealUnitSphere M) :
    ‖realOuterVector p.1.val p.2.val - realOuterVector q.1.val q.2.val‖ ^ 2 ≤
      ‖realJoinVector p.1.val p.2.val - realJoinVector q.1.val q.2.val‖ ^ 2 := by
  have hu : inner ℝ p.1.val q.1.val ≤ 1 := by
    simpa only [p.1.property, q.1.property, mul_one] using real_inner_le_norm p.1.val q.1.val
  have hv : inner ℝ p.2.val q.2.val ≤ 1 := by
    simpa only [p.2.property, q.2.property, mul_one] using real_inner_le_norm p.2.val q.2.val
  rw [norm_sub_sq_real, norm_sub_sq_real, realOuterVector_inner, realJoinVector_inner,
    realOuterVector_norm_sq, realOuterVector_norm_sq,
    realJoinVector_norm_sq, realJoinVector_norm_sq]
  simp only [p.1.property, p.2.property, q.1.property, q.2.property, one_pow]
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)]

theorem real_matrix_gaussian_comparison {N M : ℕ} [NeZero N] [NeZero M] :
    (∫ x, linearSup (fun p : RealUnitSphere N × RealUnitSphere M =>
        realOuterVector p.1.val p.2.val) (fun _ => 0) x
      ∂stdGaussian (EuclideanSpace ℝ (Fin N × Fin M))) ≤
    ∫ y, linearSup (fun p : RealUnitSphere N × RealUnitSphere M =>
        realJoinVector p.1.val p.2.val) (fun _ => 0) y
      ∂stdGaussian (EuclideanSpace ℝ (Fin N ⊕ Fin M)) := by
  apply separable_linear_gaussian_comparison _ _ _ 1 2
  · intro p
    have h := realOuterVector_norm_sq p.1.val p.2.val
    simp only [p.1.property, p.2.property, one_pow, mul_one] at h
    norm_num only [NNReal.coe_one]
    nlinarith [norm_nonneg (realOuterVector p.1.val p.2.val)]
  · intro p
    have h := realJoinVector_norm_sq p.1.val p.2.val
    simp only [p.1.property, p.2.property, one_pow] at h
    norm_num only [NNReal.coe_ofNat]
    nlinarith [norm_nonneg (realJoinVector p.1.val p.2.val)]
  · exact ⟨0, by rintro _ ⟨p, rfl⟩; exact le_rfl⟩
  · unfold realOuterVector
    fun_prop
  · unfold realJoinVector
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    cases i <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop
  · exact continuous_const
  · exact real_matrix_process_increment

def realLeftProjection {N M : ℕ} :
    EuclideanSpace ℝ (Fin N ⊕ Fin M) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (show EuclideanSpace ℝ (Fin N ⊕ Fin M) →ₗ[ℝ] EuclideanSpace ℝ (Fin N) from
    { toFun := fun x => WithLp.toLp 2 (fun i => x (Sum.inl i))
      map_add' := by intro x y; ext i; rfl
      map_smul' := by intro c x; ext i; rfl }).toContinuousLinearMap

def realRightProjection {N M : ℕ} :
    EuclideanSpace ℝ (Fin N ⊕ Fin M) →L[ℝ] EuclideanSpace ℝ (Fin M) :=
  (show EuclideanSpace ℝ (Fin N ⊕ Fin M) →ₗ[ℝ] EuclideanSpace ℝ (Fin M) from
    { toFun := fun x => WithLp.toLp 2 (fun i => x (Sum.inr i))
      map_add' := by intro x y; ext i; rfl
      map_smul' := by intro c x; ext i; rfl }).toContinuousLinearMap

theorem realProjections_norm_sq {N M : ℕ} (x : EuclideanSpace ℝ (Fin N ⊕ Fin M)) :
    ‖realLeftProjection x‖ ^ 2 + ‖realRightProjection x‖ ^ 2 = ‖x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
  rfl

theorem realLeftProjection_norm_le {N M : ℕ} : ‖realLeftProjection (N := N) (M := M)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← realProjections_norm_sq x]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem realRightProjection_norm_le {N M : ℕ} : ‖realRightProjection (N := N) (M := M)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← realProjections_norm_sq x]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem realJoinVector_inner_split {N M : ℕ} (u : EuclideanSpace ℝ (Fin N))
    (v : EuclideanSpace ℝ (Fin M)) (x : EuclideanSpace ℝ (Fin N ⊕ Fin M)) :
    inner ℝ (realJoinVector u v) x =
      inner ℝ u (realLeftProjection x) + inner ℝ v (realRightProjection x) := by
  simp only [realJoinVector, PiLp.inner_apply, Fintype.sum_sum_type]
  rfl

theorem real_join_process_le {N M : ℕ} [NeZero N] [NeZero M]
    (x : EuclideanSpace ℝ (Fin N ⊕ Fin M)) :
    linearSup (fun p : RealUnitSphere N × RealUnitSphere M =>
      realJoinVector p.1.val p.2.val) (fun _ => 0) x ≤
      ‖realLeftProjection x‖ + ‖realRightProjection x‖ := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨p, rfl⟩
  change 0 + inner ℝ (realJoinVector p.1.val p.2.val) x ≤ _
  rw [zero_add, realJoinVector_inner_split]
  apply add_le_add
  · simpa only [p.1.property, one_mul] using real_inner_le_norm p.1.val (realLeftProjection x)
  · simpa only [p.2.property, one_mul] using real_inner_le_norm p.2.val (realRightProjection x)

/-- The real bilinear Gaussian process has expected supremum at most
`sqrt N + sqrt M`. This is the sharp dimension dependence used below. -/
theorem real_matrix_process_mean_le {N M : ℕ} [NeZero N] [NeZero M] :
    (∫ x, linearSup (fun p : RealUnitSphere N × RealUnitSphere M =>
        realOuterVector p.1.val p.2.val) (fun _ => 0) x
      ∂stdGaussian (EuclideanSpace ℝ (Fin N × Fin M))) ≤
      Real.sqrt N + Real.sqrt M := by
  apply (real_matrix_gaussian_comparison (N := N) (M := M)).trans
  have hL : Integrable (fun x : EuclideanSpace ℝ (Fin N ⊕ Fin M) => ‖realLeftProjection x‖)
      (stdGaussian _) :=
    ((IsGaussian.hasGaussianLaw_id (μ := stdGaussian _)).map realLeftProjection).integrable.norm
  have hR : Integrable (fun x : EuclideanSpace ℝ (Fin N ⊕ Fin M) => ‖realRightProjection x‖)
      (stdGaussian _) :=
    ((IsGaussian.hasGaussianLaw_id (μ := stdGaussian _)).map realRightProjection).integrable.norm
  have hsup := linearSup_integrable
    (fun p : RealUnitSphere N × RealUnitSphere M => realJoinVector p.1.val p.2.val)
    (fun _ => 0) 2 (fun p => by
      have h := realJoinVector_norm_sq p.1.val p.2.val
      simp only [p.1.property, p.2.property, one_pow] at h
      norm_num only [NNReal.coe_ofNat]
      nlinarith [norm_nonneg (realJoinVector p.1.val p.2.val)])
    ⟨0, by rintro _ ⟨p, rfl⟩; exact le_rfl⟩
  calc
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin N ⊕ Fin M),
        ‖realLeftProjection x‖ + ‖realRightProjection x‖ ∂stdGaussian _ :=
      integral_mono hsup (hL.add hR) real_join_process_le
    _ = _ := integral_add hL hR
    _ ≤ _ := add_le_add
      (by
        simpa using stdGaussian_integral_norm_contraction_le
          (realLeftProjection (N := N) (M := M)) realLeftProjection_norm_le)
      (by
        simpa using stdGaussian_integral_norm_contraction_le
          (realRightProjection (N := N) (M := M)) realRightProjection_norm_le)

end LehnerEdges

import Chapter12KernelForcingPath

open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable def hilbertKernelForcing {K J H E:Type*}
    [TopologicalSpace K] [CompactSpace K] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h:J → C(K,H)) (v:J → E) : H →L[ℝ] C(K,E) := by
  let R:H →ₗ[ℝ] C(K,E) :=
    { toFun := fun u => ∑j,⟨fun t => inner ℝ (h j t) u • v j,
        ((h j).continuous.inner continuous_const).smul continuous_const⟩
      map_add' := by intro u w;ext t;simp [inner_add_right,add_smul,Finset.sum_add_distrib]
      map_smul' := by intro a u;ext t;simp [inner_smul_right,Finset.smul_sum,smul_smul,mul_comm] }
  refine R.mkContinuous (∑j,‖h j‖*‖v j‖) ?_
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg u))).mpr
  intro t
  simp only [R,LinearMap.coe_mk,AddHom.coe_mk,ContinuousMap.sum_apply,ContinuousMap.coe_mk]
  calc
    _ ≤ ∑j,‖inner ℝ (h j t) u • v j‖ := norm_sum_le _ _
    _ ≤ ∑j,(‖h j‖*‖v j‖)*‖u‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul]
      calc
        _ ≤ (‖h j t‖*‖u‖)*‖v j‖ := mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
        _ ≤ (‖h j‖*‖u‖)*‖v j‖ := by gcongr;exact (h j).norm_coe_le_norm t
        _ = _ := by ring
    _ = _ := (Finset.sum_mul _ _ _).symm

@[simp] theorem hilbertKernelForcing_apply {K J H E:Type*}
    [TopologicalSpace K] [CompactSpace K] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h:J → C(K,H)) (v:J → E) (u:H) (t:K) :
    hilbertKernelForcing h v u t=∑j,inner ℝ (h j t) u • v j := by
  simp [hilbertKernelForcing]

theorem hilbertKernelForcing_difference_bound {K J H E:Type*}
    [TopologicalSpace K] [CompactSpace K] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h g:J → C(K,H)) (v:J → E) (C:ℝ) (hC:0≤C)
    (hbg:∀j t,‖h j t-g j t‖≤C) :
    ‖hilbertKernelForcing h v-hilbertKernelForcing g v‖≤C*(∑j,‖v j‖) := by
  have hc:0≤C*(∑j,‖v j‖) := mul_nonneg hC (Finset.sum_nonneg (fun j _ => norm_nonneg _))
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg hc (norm_nonneg u))).mpr
  intro t
  simp only [ContinuousLinearMap.sub_apply,ContinuousMap.sub_apply,hilbertKernelForcing_apply,
    ←Finset.sum_sub_distrib,←sub_smul,←inner_sub_left]
  calc
    _ ≤ ∑j,‖inner ℝ (h j t-g j t) u • v j‖ := norm_sum_le _ _
    _ ≤ ∑j,(C*‖u‖)*‖v j‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hbg j t) (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by rw [←Finset.mul_sum];ring
end Asakura.Chapter12
#print axioms Asakura.Chapter12.hilbertKernelForcing_difference_bound

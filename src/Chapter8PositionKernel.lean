import Chapter8DampedSemigroup

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter8
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The position kernel is uniformly bounded, independently of m>0. -/
theorem position_kernel_norm_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (Γ M : E →L[ℝ] E) (α m t : ℝ) (hα : 0≤α) (hm : 0<m) (ht : 0≤t)
    (hΓ : ∀ x,α*‖x‖^2≤⟪x,Γ x⟫) :
    ‖M.comp (NormedSpace.exp (t • (-m⁻¹ • Γ))-ContinuousLinearMap.id ℝ E)‖≤2*‖M‖ := by
  have he := damped_semigroup_norm_bound Γ α m hm hΓ t ht
  have he1 : ‖NormedSpace.exp (t • (-m⁻¹ • Γ))‖≤1 := he.trans (Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) ht) hm.le))
  have hk : ‖NormedSpace.exp (t • (-m⁻¹ • Γ))-ContinuousLinearMap.id ℝ E‖≤2 :=
    (norm_sub_le _ _).trans (by linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)])
  have hh := (ContinuousLinearMap.opNorm_comp_le M _).trans (mul_le_mul_of_nonneg_left hk (norm_nonneg _))
  simpa only [mul_comm] using hh

/-- Group the two drift integrals in the remainder representation into
the uniformly bounded position kernel. -/
theorem position_drift_kernel_identity {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (M : E →L[ℝ] E) (E0 : ℝ → E →L[ℝ] E) (hE : Continuous E0)
    (H : ℝ → E) (hH : Continuous H) (t : ℝ) :
    -M (∫ s in 0..t,H s)+M (∫ s in 0..t,E0 s (H s))=
      ∫ s in 0..t,M.comp (E0 s-ContinuousLinearMap.id ℝ E) (H s) := by
  have he : Continuous (fun s => E0 s (H s)) := hE.clm_apply hH
  have hid : IntervalIntegrable (fun s => E0 s (H s)-H s) volume 0 t := (he.sub hH).intervalIntegrable 0 t
  have hi := M.intervalIntegral_comp_comm hid
  have heq : (fun s => M.comp (E0 s-ContinuousLinearMap.id ℝ E) (H s))=(fun s => M (E0 s (H s)-H s)) := by rfl
  rw [heq,hi,intervalIntegral.integral_sub (he.intervalIntegrable 0 t) (hH.intervalIntegrable 0 t),map_sub]
  abel
end Asakura.Chapter8

import MVNKernelBounds

open MeasureTheory Set
namespace Asakura

lemma mvn_past_square_integrable (a t : ℝ) (ha0 : -1/2 < a) (ha1 : a < 1/2) (ht : 0 ≤ t) :
    IntegrableOn (fun s => (mvnPastKernel a t s)^2) (Ioi 0) := by
  by_cases ht0 : t = 0
  · subst t
    simpa [mvnPastKernel] using (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0:ℝ)) (Ioi 0))
  have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hmeas : AEStronglyMeasurable (fun s => (mvnPastKernel a t s)^2) (volume.restrict (Ioi 0)) := by
    unfold mvnPastKernel
    fun_prop
  have hnear₁ : IntegrableOn (fun s : ℝ => (t+s)^(2*a)) (Ioo 0 1) := by
    have hc : ContinuousOn (fun s : ℝ => (t+s)^(2*a)) (Icc 0 1) := by
      apply ContinuousOn.rpow_const (continuous_const.add continuous_id).continuousOn
      intro s hs
      apply Or.inl
      change t+s ≠ 0
      linarith [hs.1]
    exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnear₂ : IntegrableOn (fun s : ℝ => s^(2*a)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ)<1)).mpr (by linarith)
  have hnear : IntegrableOn (fun s => (mvnPastKernel a t s)^2) (Ioo 0 1) := by
    apply ((hnear₁.add hnear₂).const_mul 2).mono'
    · unfold mvnPastKernel
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mvn_past_square_bound a t s ht hs.1.le
  have htail : IntegrableOn (fun s => (mvnPastKernel a t s)^2) (Ioi 1) := by
    have hi : IntegrableOn (fun s : ℝ => s^(2*a-2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
    apply (hi.const_mul ((|a| *t)^2)).mono'
    · unfold mvnPastKernel
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mvn_past_tail_square_bound a t s (by linarith) ht (lt_trans (by norm_num) hs)
  have hnear' : IntegrableOn (fun s => (mvnPastKernel a t s)^2) (Ioc 0 1) :=
    hnear.congr_set_ae Ioo_ae_eq_Ioc.symm
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1)] using hnear'.union htail
end Asakura

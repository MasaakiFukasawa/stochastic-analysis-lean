import Chapter5FiniteTimeEnergy
import FullAuditJensenContraction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- A measurable process representing E[U|F_t] belongs to sample-time L²
on each finite interval. Use the Chapter 1 conditional Jensen proof,
then Fubini; pointwise L² alone is not silently substituted for this. -/
theorem conditional_process_sample_time_memLp_two
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0 ≤ R) (F : ℝ → MeasurableSpace Ω)
    (hle : ∀ t ∈ Icc 0 R,F t ≤ m)
    (U : Ω → ℝ) (hU : MemLp U 2 P)
    (M : Ω × ℝ → ℝ) (hM : Measurable M)
    (he : ∀ t ∈ Icc 0 R,(fun w => M (w,t)) =ᵐ[P] P[U|F t]) :
    MemLp M 2 (P.prod (volume.restrict (Ioc 0 R))) := by
  have hmoment t (ht : t ∈ Icc 0 R) :
      Integrable (fun w => M (w,t)^2) P ∧ (∫ w,M (w,t)^2 ∂P) ≤ ∫ w,U w^2 ∂P := by
    have hc := conditional_norm_power_written P (hle t ht) 2 (by norm_num) (by norm_num) U hU
    norm_num only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] at hc
    have hes : (fun w => M (w,t)^2) =ᵐ[P] (fun w => P[U|F t] w^2) := (he t ht).mono fun w hw => congrArg (fun x : ℝ => x^2) hw
    exact ⟨hc.1.congr hes.symm,(integral_congr_ae hes).le.trans hc.2⟩
  apply (memLp_two_iff_integrable_sq hM.aestronglyMeasurable).mpr
  apply (integrable_prod_iff' (hM.pow_const 2).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hmoment t ⟨ht.1.le,ht.2⟩).1
  · have hm := ((hM.pow_const 2).norm.stronglyMeasurable.integral_prod_left' (μ := P))
    apply (integrable_const (∫ w,U w^2 ∂P)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [Real.norm_eq_abs,abs_sq]
    have hn : 0 ≤ ∫ w,M (w,t)^2 ∂P := integral_nonneg (fun w => sq_nonneg (M (w,t)))
    rw [abs_of_nonneg hn]
    exact (hmoment t ⟨ht.1.le,ht.2⟩).2

end Asakura.Chapter5

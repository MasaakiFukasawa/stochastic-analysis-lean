import Chapter8L1Approximation
import FullAuditTimeProductIntegrability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- Fubini and stationarity give a uniform L1 estimate for time-integrated
observables, including the unbounded truncation errors in the MLE proof. -/
theorem stationary_integral_L1_bound {Ω I E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace I] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure I) [IsFiniteMeasure ν]
    (π : Measure E) (Y : Ω → I → E) (hY : Measurable (Function.uncurry Y))
    (hlaw : ∀ t, P.map (fun ω => Y ω t) = π)
    (f : E → ℝ) (hf : Measurable f) (hi : Integrable f π) :
    Integrable (fun ω => ∫ t,f (Y ω t) ∂ν) P ∧
    (∫ ω, |∫ t,f (Y ω t) ∂ν| ∂P) ≤ ν.real univ*(∫ x,|f x| ∂π) := by
  let K := fun p : Ω × I => f (Y p.1 p.2)
  have hm : Measurable K := hf.comp hY
  have hmt (t : I) : Measurable (fun ω => Y ω t) :=
    hY.comp (measurable_id.prodMk measurable_const)
  have hit (t : I) : Integrable (fun ω => K (ω,t)) P := by
    have hh : Integrable f (P.map (fun ω => Y ω t)) := by rwa [hlaw]
    exact hh.comp_aemeasurable (hmt t).aemeasurable
  have hnorm (t : I) : (∫ ω, ‖K (ω,t)‖ ∂P) = ∫ x, |f x| ∂π := by
    dsimp only [K]
    rw [← integral_map (μ := P) (φ := fun ω => Y ω t) (f := fun x => ‖f x‖)
      (hmt t).aemeasurable hf.norm.aestronglyMeasurable,hlaw]
    simp only [Real.norm_eq_abs]
  have hprod : Integrable K (P.prod ν) := by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hit,?_⟩
    simp_rw [hnorm]
    exact integrable_const _
  refine ⟨hprod.integral_prod_left,?_⟩
  have hb := integral_mono hprod.integral_prod_left.norm hprod.norm.integral_prod_left
    (fun ω => norm_integral_le_integral_norm (fun t => K (ω,t)))
  rw [integral_integral_swap hprod.norm] at hb
  simp_rw [hnorm] at hb
  rw [integral_const,smul_eq_mul] at hb
  simpa only [Real.norm_eq_abs] using hb

/-- In particular the expected absolute error of a stationary time average
is at most the L1 norm of the observable, independently of T. -/
theorem stationary_time_average_L1_bound {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Measure E)
    (Y : Ω → ℝ → E) (hY : Measurable (Function.uncurry Y))
    (hlaw : ∀ t, P.map (fun ω => Y ω t) = π)
    (f : E → ℝ) (hf : Measurable f) (hi : Integrable f π) (T : ℝ) (hT : 0 < T) :
    Integrable (fun ω => timeAverage (fun t => f (Y ω t)) T) P ∧
    (∫ ω, |timeAverage (fun t => f (Y ω t)) T| ∂P) ≤ ∫ x,|f x| ∂π := by
  let ν := volume.restrict (Ioc (0:ℝ) T)
  obtain ⟨havg,hb⟩ := stationary_integral_L1_bound P ν π Y hY hlaw f hf hi
  have hν : ν.real univ = T := by
    simp [ν,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal hT.le]
  rw [hν] at hb
  constructor
  · simpa only [timeAverage,intervalIntegral.integral_of_le hT.le] using havg.const_mul T⁻¹
  · simp only [timeAverage,intervalIntegral.integral_of_le hT.le,
      abs_mul,abs_of_pos (inv_pos.mpr hT)]
    rw [integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hT.le)
    simpa only [← mul_assoc,inv_mul_cancel₀ hT.ne',one_mul] using hh

end Asakura.Chapter8

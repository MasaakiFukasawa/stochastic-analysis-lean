import FullAuditCovarianceKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Connect centering, Fubini, the stationary covariance kernel, and the
 triangular integral. Joint product integrability and stationarity of the
 actual process remain explicit inputs rather than being silently presumed. -/
theorem stationary_time_average_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ → ℝ)
    (hcZ : ∀ ω, Continuous (Z ω))
    (hZ : ∀ t, MemLp (fun ω => Z ω t) 2 P)
    (hmean : ∀ t, (∫ ω, Z ω t ∂P) = 0)
    (c : ℝ → ℝ) (hc : Continuous c) (T : ℝ) (hT : 0 < T)
    (hcov : ∀ s ≥ 0, ∀ t ≥ 0,
      cov[fun ω => Z ω s,fun ω => Z ω t;P] = c |t-s|)
    (hprod : Integrable (fun p : Ω × (ℝ × ℝ) => Z p.1 p.2.1 * Z p.1 p.2.2)
      (P.prod ((volume.restrict (Ioc 0 T)).prod (volume.restrict (Ioc 0 T))))) :
    (∫ ω, (timeAverage (Z ω) T)^2 ∂P) =
      2/T^2*(∫ u in (0:ℝ)..T,(T-u)*c u) := by
  let ν := volume.restrict (Ioc (0:ℝ) T)
  have hsecond := second_moment_integral_covariance P ν Z
    (fun ω => (hcZ ω).integrableOn_Ioc) hZ hmean hprod
  have hk : Integrable (fun p : ℝ × ℝ => c |p.2-p.1|) (ν.prod ν) := by
    have hcont : Continuous (fun p : ℝ × ℝ => c |p.2-p.1|) := by fun_prop
    have hh : IntegrableOn (fun p : ℝ × ℝ => c |p.2-p.1|)
        ((Icc (0:ℝ) T) ×ˢ (Icc (0:ℝ) T)) (volume.prod volume) :=
      hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hh' := hh.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    simpa only [IntegrableOn,Measure.prod_restrict,ν] using hh'
  have hce : (fun p : ℝ × ℝ => cov[fun ω => Z ω p.1,fun ω => Z ω p.2;P]) =ᵐ[ν.prod ν]
      (fun p => c |p.2-p.1|) := by
    dsimp only [ν]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    exact hcov p.1 hp.1.1.le p.2 hp.2.1.le
  rw [integral_congr_ae hce,integral_prod _ hk] at hsecond
  have he : (∫ ω, (timeAverage (Z ω) T)^2 ∂P) =
      T⁻¹^2*(∫ ω, (∫ t, Z ω t ∂ν)^2 ∂P) := by
    simp only [timeAverage,intervalIntegral.integral_of_le hT.le,mul_pow]
    rw [integral_const_mul]
  rw [he,hsecond]
  have hkernel := covariance_kernel_square c hc T hT.le
  simp only [intervalIntegral.integral_of_le hT.le] at hkernel
  change T⁻¹^2*(∫ s, ∫ t, c |t-s| ∂ν ∂ν) = _
  rw [hkernel]
  rw [← intervalIntegral.integral_of_le hT.le]
  ring

end Asakura.FullAudit

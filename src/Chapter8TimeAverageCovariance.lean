import FullAuditTimeProductIntegrability
import Chapter8MarkovCovariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Directly integrate the covariance estimate. No continuity of the
covariance kernel, beyond that proved for the exponential majorant, is required. -/
theorem time_average_from_covariance_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ → ℝ)
    (hmZ : Measurable (Function.uncurry Z)) (hcZ : ∀ ω, Continuous (Z ω))
    (hZ : ∀ t, MemLp (fun ω => Z ω t) 2 P)
    (hmean : ∀ t, (∫ ω, Z ω t ∂P) = 0)
    (C κ T : ℝ) (hC : 0 ≤ C) (hκ : 0 < κ) (hT : 0 < T)
    (hsecond : ∀ t, (∫ ω, (Z ω t)^2 ∂P) ≤ C)
    (hcov : ∀ s ≥ 0, ∀ t ≥ 0,
      |cov[fun ω => Z ω s,fun ω => Z ω t;P]| ≤ C*Real.exp (-κ*|t-s|)) :
    (∫ ω, (timeAverage (Z ω) T)^2 ∂P) ≤ 2*C/(κ*T) := by
  let ν := volume.restrict (Ioc (0:ℝ) T)
  let K := fun p : ℝ × ℝ => cov[fun ω => Z ω p.1,fun ω => Z ω p.2;P]
  let c := fun t : ℝ => C*Real.exp (-κ*t)
  have hc : Continuous c := by fun_prop
  have hi := time_covariance_product_integrable P ν Z hmZ hZ C hC hsecond
  have hK : Integrable K (ν.prod ν) := by
    have he : K = fun p => ∫ ω, Z ω p.1 * Z ω p.2 ∂P := by
      funext p
      dsimp only [K]
      rw [covariance_eq_sub (hZ p.1) (hZ p.2),hmean,hmean]
      simp
    rw [he]
    exact hi.integral_prod_right
  have hmajor : Integrable (fun p : ℝ × ℝ => c |p.2-p.1|) (ν.prod ν) := by
    have hcont : Continuous (fun p : ℝ × ℝ => c |p.2-p.1|) := by fun_prop
    have hh : IntegrableOn (fun p : ℝ × ℝ => c |p.2-p.1|)
        ((Icc (0:ℝ) T) ×ˢ (Icc (0:ℝ) T)) (volume.prod volume) :=
      hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hh' := hh.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
    simpa only [IntegrableOn,Measure.prod_restrict,ν] using hh'
  have hb : (∫ p, K p ∂ν.prod ν) ≤ ∫ p : ℝ × ℝ, c |p.2-p.1| ∂ν.prod ν := by
    apply integral_mono_ae hK hmajor
    dsimp only [ν]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    exact (le_abs_self _).trans (hcov p.1 hp.1.1.le p.2 hp.2.1.le)
  have he : (∫ ω, (timeAverage (Z ω) T)^2 ∂P) =
      T⁻¹^2*(∫ p, K p ∂ν.prod ν) := by
    simp only [timeAverage,intervalIntegral.integral_of_le hT.le,mul_pow]
    rw [integral_const_mul]
    congr 1
    exact second_moment_integral_covariance P ν Z
      (fun ω => (hcZ ω).integrableOn_Ioc) hZ hmean hi
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg T⁻¹)
  rw [he]
  apply hm.trans
  rw [integral_prod _ hmajor]
  have hs := covariance_kernel_square c hc T hT.le
  simp only [intervalIntegral.integral_of_le hT.le] at hs
  change T⁻¹^2*(∫ s, ∫ t, c |t-s| ∂ν ∂ν) ≤ _
  rw [hs]
  have ha := integrated_covariance_bound c C κ T hC hκ hT
    (hc.intervalIntegrable 0 T) (fun u _ => by
      dsimp only [c]
      rw [abs_of_nonneg (by positivity)])
  rw [intervalIntegral.integral_of_le hT.le] at ha
  convert ha using 1 <;> ring

end Asakura.Chapter8

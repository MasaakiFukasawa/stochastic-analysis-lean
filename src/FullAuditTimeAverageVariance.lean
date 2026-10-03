import FullAuditCovarianceDecay
import FullAuditTimeAverageCoupling

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The covariance double integral in the time-average proof. The process is
 centered, and the product-integrability hypothesis explicitly records the
 Fubini justification still needed from stationarity and the moment bound. -/
theorem second_moment_integral_covariance {Ω I : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure I) [SFinite ν] (Z : Ω → I → ℝ)
    (hpath : ∀ ω, Integrable (Z ω) ν)
    (hZ : ∀ t, MemLp (fun ω => Z ω t) 2 P)
    (hmean : ∀ t, (∫ ω, Z ω t ∂P) = 0)
    (hprod : Integrable (fun p : Ω × (I × I) => Z p.1 p.2.1 * Z p.1 p.2.2)
      (P.prod (ν.prod ν))) :
    (∫ ω, (∫ t, Z ω t ∂ν)^2 ∂P) =
      ∫ p : I × I, cov[fun ω => Z ω p.1,fun ω => Z ω p.2;P] ∂ν.prod ν := by
  have hpoint (ω : Ω) : (∫ t, Z ω t ∂ν)^2 =
      ∫ p : I × I, Z ω p.1 * Z ω p.2 ∂ν.prod ν := by
    rw [integral_prod _ ((hpath ω).mul_prod (hpath ω))]
    simp_rw [integral_const_mul]
    rw [integral_mul_const]
    ring
  simp_rw [hpoint]
  rw [integral_integral_swap hprod]
  apply integral_congr_ae
  apply ae_of_all _
  intro p
  dsimp only
  rw [covariance_eq_sub (hZ p.1) (hZ p.2),hmean,hmean]
  simp

/-- The final elementary bound on the covariance integral. -/
theorem integrated_covariance_bound (c : ℝ → ℝ) (C κ T : ℝ)
    (hC : 0 ≤ C) (hκ : 0 < κ) (hT : 0 < T)
    (hi : IntervalIntegrable c volume 0 T)
    (hb : ∀ u ∈ Icc 0 T, |c u| ≤ C*Real.exp (-κ*u)) :
    2/T^2*(∫ u in (0:ℝ)..T,(T-u)*c u) ≤ 2*C/(κ*T) := by
  have hmul : IntervalIntegrable (fun u => (T-u)*c u) volume 0 T :=
    hi.continuousOn_mul (by fun_prop)
  have he : IntervalIntegrable (fun u => T*C*Real.exp (-κ*u)) volume 0 T :=
    (by fun_prop : Continuous (fun u : ℝ => T*C*Real.exp (-κ*u))).intervalIntegrable 0 T
  have hbound : (∫ u in (0:ℝ)..T,(T-u)*c u) ≤ T*C/κ := by
    have h := intervalIntegral.integral_mono_on hT.le hmul he (fun u hu => by
      have hc : c u ≤ C*Real.exp (-κ*u) := (le_abs_self _).trans (hb u hu)
      calc
        (T-u)*c u ≤ (T-u)*(C*Real.exp (-κ*u)) :=
          mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hu.2)
        _ ≤ T*(C*Real.exp (-κ*u)) :=
          mul_le_mul_of_nonneg_right (sub_le_self _ hu.1) (by positivity)
        _ = T*C*Real.exp (-κ*u) := by ring)
    rw [intervalIntegral.integral_const_mul,integrated_exponential_decay κ T hκ] at h
    apply h.trans
    have hn : T*C*(1-Real.exp (-κ*T)) ≤ T*C := by
      nlinarith [mul_nonneg (mul_nonneg hT.le hC) (Real.exp_pos (-κ*T)).le]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hn hκ.le
  have h := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 2/T^2)
  apply h.trans_eq
  field_simp

end Asakura.FullAudit

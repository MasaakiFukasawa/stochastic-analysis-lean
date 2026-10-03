import Chapter6BoundedVectorCovariance

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The drift in the Girsanov transform of an arbitrary square-integrable
Ito integrand: the cross bracket has density beta*Z. -/
theorem bounded_ito_cross_density {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (β Z : Ω × ℝ → ℝ) (hβm : Measurable β) (hZm : Measurable Z)
    (K : ℝ) (hβb : ∀ z,|β z|≤K)
    (N M : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hM : LocalMProcessWitness P B.F M)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) β N)
    (hMI : ItoCovarianceFormula P B.F (B.W 0) Z M)
    (hZsq : ∀ b : ℝ,0≤b → ∀ᵐ w ∂P,IntervalIntegrable (fun r => Z (w,r)^2) volume 0 b) :
    ∃ C,LocalCovarianceWitness P B.F N M C ∧
      ∀ b : ℝ,0≤b → C (realTimeClamp b)=ᵐ[P] fun w => ∫ r in 0..b,β (w,r)*Z (w,r) := by
  have hi w b hb := bounded_time_integrable _ (hβm.comp measurable_prodMk_left) K (fun r => hβb (w,r)) b hb
  obtain ⟨A,hA,hAe⟩ := measurable_ito_clock_cross P B.F (B.W 0) (B.W 0) N (B.C 0 0)
    (B.martingale 0) hN (B.cov 0 0) β hNI True (by intro w r hr; simpa using B.clock 0 0 w r hr) hi
  have he b (hb : 0≤b) : A (realTimeClamp b)=ᵐ[P] fun w => ∫ r in 0..b,β (w,r) := by
    simpa only [if_true] using hAe b hb
  have hAC := covariance_density_common_time P B.F N (B.W 0) A hN (B.martingale 0) hA β
    (fun b hb => ae_of_all _ (fun w => hi w b hb)) he
  have hp b (hb : 0≤b) : ∀ᵐ w ∂P,IntervalIntegrable (fun r => Z (w,r)*β (w,r)) volume 0 b := by
    filter_upwards [hZsq b hb] with w hw
    have hz2 : MemLp (fun r => Z (w,r)) 2 (volume.restrict (Ioc 0 b)) :=
      (memLp_two_iff_integrable_sq (hZm.comp measurable_prodMk_left).aestronglyMeasurable).mpr
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp hw)
    have hz1 := hz2.integrable (by norm_num)
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr
    apply (hz1.norm.const_mul K).mono'
      (((hZm.comp measurable_prodMk_left).mul (hβm.comp measurable_prodMk_left)).aestronglyMeasurable)
    apply ae_of_all
    intro r
    change ‖Z (w,r)*β (w,r)‖≤K*‖Z (w,r)‖
    simp only [Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ |Z (w,r)| * K := mul_le_mul_of_nonneg_left (hβb (w,r)) (abs_nonneg _)
      _ = _ := mul_comm _ _
  obtain ⟨C,hC,hCe⟩ := measurable_ito_covariance_density P B.F (B.W 0) N M A hN
    (hA.symm P B.F) Z β (fun w => hZm.comp measurable_prodMk_left) (fun w => hβm.comp measurable_prodMk_left)
    hMI (fun b hb => ae_of_all _ (fun w => hi w b hb)) hp hAC
  exact ⟨C,hC.symm P B.F,fun b hb => by simpa only [mul_comm] using hCe b hb⟩

end Asakura.Chapter6

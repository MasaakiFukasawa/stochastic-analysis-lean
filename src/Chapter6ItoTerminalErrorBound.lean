import Chapter4ProgressiveFiniteMoment
import Chapter4ClockRegularity
import Chapter4BrownianSystem

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem brownian_ito_terminal_square_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d) (j : Fin d)
    (N : HalfClosedTime → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hN : LocalMProcessWitness P B.F N) (hNI : ItoCovarianceFormula P B.F (B.W j) H N)
    (hHp : ∀ R : ℝ,0≤R → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val)))
    (hHi : ∀ R : ℝ,0≤R → ∀ᵐ w ∂P,Integrable (fun r => H (w,r)^2) (volume.restrict (Ioc 0 R)))
    (R : ℝ) (hR : 0≤R) (hH2 : MemLp H 2 (P.prod (volume.restrict (Ioc 0 R)))) :
    MemLp (N (realTimeClamp R)) 2 P ∧
      (∫ w,(N (realTimeClamp R) w)^2 ∂P)≤4*(∫ z,H z^2 ∂P.prod (volume.restrict (Ioc 0 R))) := by
  have hi := (memLp_two_iff_integrable_sq hH2.aestronglyMeasurable).1 hH2
  have he : Integrable (fun w => ∫ r in 0..R,H (w,r)^2) P := by
    simp_rw [intervalIntegral.integral_of_le hR]
    exact hi.integral_prod_left
  have hclock := fun w (r : ℝ) hr (_ : (r:EReal)<⊤) => B.diagonal_clock j w r hr
  obtain ⟨hCm,hCc⟩ := clock_regular_from_identity (B.C j j) hclock
  obtain ⟨hc,hM,hb⟩ := brownian_progressive_ito_finite_path_moment P (show (0:EReal)<⊤ by simp)
    B.F B.mono B.le B.null (B.W j) (B.C j j) N H (B.martingale j) (B.cov j j) hCm hCc hclock
    (fun R hR _ => hHp R hR) (fun R hR _ => hHi R hR) hN hNI R hR (EReal.coe_lt_top _) he
  let Z := finiteRealPath N R hc
  have hval w : |N (realTimeClamp R) w|≤‖Z w‖ := by
    simpa only [Z,finiteRealPath,ContinuousMap.coe_mk,Real.norm_eq_abs] using (Z w).norm_coe_le_norm ⟨R,⟨hR,le_rfl⟩⟩
  have hpoint : MemLp (N (realTimeClamp R)) 2 P := hM.mono
    ((hN.adapted P B.F _ (real_time_below _ hR (EReal.coe_lt_top _))).mono (B.le _) le_rfl).aestronglyMeasurable
    (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using hval w))
  refine ⟨hpoint,?_⟩
  have hpi := (memLp_two_iff_integrable_sq hpoint.aestronglyMeasurable).1 hpoint
  have hzi := hM.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hle : (∫ w,(N (realTimeClamp R) w)^2 ∂P)≤∫ w,‖Z w‖^2 ∂P := by
    apply integral_mono hpi hzi
    intro w
    nlinarith [hval w,le_abs_self (N (realTimeClamp R) w),neg_le_abs (N (realTimeClamp R) w),norm_nonneg (Z w)]
  apply hle.trans
  convert hb using 1
  simp_rw [intervalIntegral.integral_of_le hR]
  rw [integral_prod _ hi]

end Asakura.Chapter6

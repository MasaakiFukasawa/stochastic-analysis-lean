import Chapter5LocalPathBrownianIntegral
import Chapter5ProgressiveZeroExtension
import Chapter5ClippedDriftIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- A finite-interval Ito integrand extends to an actual local stochastic
integral on the ambient time domain by zero extension. Only pathwise
square integrability up to the finite endpoint is needed. -/
theorem finite_path_energy_integral_extension
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (R : ℝ) (hR : 0≤R) (G : Ω × ℝ → ℝ) (hGm : Measurable G)
    (hGp : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => G (z.1,z.2.val)))
    (hGi : ∀ᵐ w ∂P,IntervalIntegrable (fun r => G (w,r)^2) volume 0 R) :
    let H := fun z : Ω × ℝ => (Iic R).indicator (fun r => G (z.1,r)) z.2
    ∃ M : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F M ∧ ItoCovarianceFormula P F W H M ∧
      Measurable H ∧
      (∀ j,@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c j) => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) (c j) => H (z.1,z.2.val))) ∧
      (∀ j,∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)^2) volume 0 (c j)) ∧
      (∀ w r,r∈Icc 0 R → H (w,r)=G (w,r)) := by
  classical
  dsimp only
  let H := fun z : Ω × ℝ => (Iic R).indicator (fun r => G (z.1,r)) z.2
  have hHm : Measurable H := hGm.indicator (measurableSet_Iic.preimage measurable_snd)
  have hHp j := progressive_finite_zero_extension (fun r => F (realTimeClamp r))
    (fun s t hst => hF (real_time_clamp_mono hst)) R hR G hGp (c j)
  have hHi : ∀ j,∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)^2) volume 0 (c j) := by
    intro j
    filter_upwards [hGi] with w hw
    have hh := clipped_driver_interval_integrable (fun r => G (w,r)^2) R (c j) hR (hc j).le
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp hw)
    convert hh using 1
    funext r
    by_cases hr : r≤R <;> simp only [H,Set.indicator,mem_Iic,hr,ite_true,ite_false,zero_pow (by decide : 2≠0)]
  obtain ⟨M,hM,hMI⟩ := brownian_local_path_energy_integral_constructed P hT F hF hle hnull W A hW hA
    c hc hcm hcT hct hcut hcc hclock H hHm hHp hHi
  refine ⟨M,hM,hMI,hHm,hHp,hHi,?_⟩
  intro w r hr
  simp only [H,Set.indicator,mem_Iic,hr.2,ite_true]

end Asakura.Chapter5

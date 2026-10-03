import Chapter4FiniteStepDomain
import Chapter4VectorFiniteLift

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma continuous_minus_step_domain
    {Ω : Type*} {m : MeasurableSpace Ω} {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (H : ClosedTime T → Ω → ℝ)
    (ha : ∀ t,Measurable[F t] (H t)) (hc : ∀ w,Continuous (fun t => H t w))
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (G : ι → Ω → ℝ)
    (hG : ∀ i∈s,Measurable[F (realTimeClamp (a i))] (G i)) :
    let D := fun z : Ω × ℝ => H (realTimeClamp z.2) z.1-
      ∑ i∈s,(Ioc (a i) (b i)).indicator (fun _ => G i z.1) z.2
    (∀ R : ℝ,0≤R → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => D (z.1,z.2.val))) ∧
    (∀ w R,0≤R → Integrable (fun r => D (w,r)^2) (volume.restrict (Ioc 0 R))) := by
  classical
  dsimp only
  obtain ⟨hSm,hSp,hSi⟩ := finite_step_integrand_domain F hF hle s a b G hG
  have hHc w : Continuous (fun r => H (realTimeClamp r) w) := (hc w).comp real_time_clamp_continuous
  constructor
  · intro R hR
    exact (continuous_adapted_real_progressive F hF (fun z => H (realTimeClamp z.2) z.1) R hR
      (fun r _ => ha _) (fun w => (hHc w).continuousOn)).sub (hSp R)
  · intro w R hR
    have hhi : MemLp (fun r => H (realTimeClamp r) w) 2 (volume.restrict (Ioc 0 R)) :=
      (memLp_two_iff_integrable_sq (hHc w).measurable.aestronglyMeasurable).mpr
        (((hHc w).pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    have hsi : MemLp (fun r => ∑ i∈s,(Ioc (a i) (b i)).indicator (fun _ => G i w) r) 2
        (volume.restrict (Ioc 0 R)) := memLp_finsetSum s
          (fun i _ => (memLp_const (G i w)).indicator measurableSet_Ioc)
    exact (memLp_two_iff_integrable_sq (hhi.sub hsi).aestronglyMeasurable).mp (hhi.sub hsi)

end Asakura.Chapter4

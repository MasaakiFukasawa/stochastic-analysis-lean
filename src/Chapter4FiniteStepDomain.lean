import Chapter2ProgressiveElementary
import Chapter4EulerIntegralEquation

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

lemma progressive_real_Ioc_step
    {Ω : Type*} {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (a b R : ℝ) (G : Ω → ℝ) (hG : Measurable[F (realTimeClamp a)] G) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => (Ioc a b).indicator (fun _ => G z.1) z.2.val) := by
  apply (measurable_progressive_iff _ _).2
  intro u
  letI : MeasurableSpace Ω := F (realTimeClamp u.val)
  have htime : Measurable (fun z : Ω × Iic u => z.2.val.val) :=
    measurable_subtype_coe.comp (measurable_subtype_coe.comp measurable_snd)
  by_cases hau : a≤u.val
  · have hGu : Measurable G := hG.mono (hF (real_time_clamp_mono hau)) le_rfl
    have he : (fun z : Ω × Iic u => (Ioc a b).indicator (fun _ => G z.1) z.2.val.val)=
        ((fun z : Ω × Iic u => z.2.val.val) ⁻¹' Ioc a b).indicator (fun z => G z.1) := by
      funext z
      by_cases hz : z.2.val.val∈Ioc a b <;> simp [indicator,hz]
    rw [he]
    exact (hGu.comp measurable_fst).indicator (measurableSet_Ioc.preimage htime)
  · have he : (fun z : Ω × Iic u => (Ioc a b).indicator (fun _ => G z.1) z.2.val.val)=fun _ => (0:ℝ) := by
      funext z
      apply indicator_of_notMem
      intro hz
      exact hau (hz.1.le.trans z.2.property)
    rw [he]
    exact measurable_const

/-- Finite adapted step coefficients are in the actual progressive Ito
domain on every finite horizon; their values need not be bounded in omega. -/
theorem finite_step_integrand_domain
    {Ω : Type*} {m : MeasurableSpace Ω} {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (G : ι → Ω → ℝ)
    (hG : ∀ i∈s,Measurable[F (realTimeClamp (a i))] (G i)) :
    let H := fun z : Ω × ℝ => ∑ i∈s,(Ioc (a i) (b i)).indicator (fun _ => G i z.1) z.2
    Measurable[m.prod inferInstance] H ∧
    (∀ R : ℝ,@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) R => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) R => H (z.1,z.2.val))) ∧
    (∀ w R,0≤R → IntervalIntegrable (fun r => H (w,r)^2) volume 0 R) := by
  classical
  dsimp only
  constructor
  · apply Finset.measurable_sum
    intro i hi
    have he : (fun z : Ω × ℝ => (Ioc (a i) (b i)).indicator (fun _ => G i z.1) z.2)=
        (Prod.snd ⁻¹' Ioc (a i) (b i)).indicator (fun z => G i z.1) := by
      funext z
      by_cases hz : z.2∈Ioc (a i) (b i) <;> simp [indicator,hz]
    rw [he]
    exact (((hG i hi).mono (hle _) le_rfl).comp measurable_fst).indicator
      (measurableSet_Ioc.preimage measurable_snd)
  constructor
  · intro R
    exact Finset.measurable_sum _ fun i hi => progressive_real_Ioc_step F hF (a i) (b i) R (G i) (hG i hi)
  · intro w R hR
    have hm : MemLp (fun r => ∑ i∈s,(Ioc (a i) (b i)).indicator (fun _ => G i w) r) 2
        (volume.restrict (Ioc 0 R)) :=
      memLp_finsetSum s (fun i _ => (memLp_const (G i w)).indicator measurableSet_Ioc)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
      ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).1 hm)

end Asakura.Chapter4

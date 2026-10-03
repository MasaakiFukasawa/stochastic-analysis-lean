import Chapter2ContinuousIntegrand
import Chapter2CumulativeAdapted
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Bounded continuous adapted integrands restricted to a finite interval
belong to the actual global time-probability L² space. -/
theorem bounded_continuous_interval_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t≤m)
    (H : Ω × ℝ → ℝ) (a S C : ℝ) (ha : 0≤a) (haS : a≤S)
    (hHa : ∀ r∈Icc 0 S,Measurable[F (realTimeClamp r)] (fun w => H (w,r)))
    (hHc : ∀ w,ContinuousOn (fun r => H (w,r)) (Icc 0 S))
    (hbound : ∀ w r,r∈Icc 0 S → |H (w,r)|≤C) :
    let J := fun z : Ω × ℝ => (Ioc a S).indicator (fun r => H (z.1,r)) z.2
    Measurable J ∧ MemLp J 2 (P.prod (volume.restrict (Ioi 0))) := by
  classical
  dsimp only
  have hS : 0≤S := ha.trans haS
  have hp := continuous_adapted_real_progressive F hF H S hS hHa hHc
  have hm := progressive_clamped_measurable 0 S hS
    (fun t : Icc (0:ℝ) S => F (realTimeClamp t.val))
    (fun z : Ω × Icc (0:ℝ) S => H (z.1,z.2.val)) hp ⟨S,right_mem_Icc.mpr hS⟩
  let K := fun z : Ω × ℝ => H (z.1,(projIcc 0 S hS (intervalClamp 0 S hS z.2)).val)
  have hfst : @Measurable (Ω × ℝ) Ω inferInstance (F (realTimeClamp S)) Prod.fst :=
    measurable_fst.mono le_rfl (hle _)
  have hK : Measurable K := hm.comp (hfst.prodMk measurable_snd)
  let s : Set (Ω × ℝ) := {z | z.2∈Ioc a S}
  have hs : MeasurableSet s := measurable_snd measurableSet_Ioc
  have he : (fun z : Ω × ℝ => (Ioc a S).indicator (fun r => H (z.1,r)) z.2)=s.indicator K := by
    funext z
    by_cases hz : z.2∈Ioc a S
    · have hz0 : z.2∈Icc 0 S := ⟨ha.trans hz.1.le,hz.2⟩
      simp only [indicator_of_mem hz,indicator_of_mem (show z∈s from hz),K]
      rw [intervalClamp_eq 0 S hS hz0,projIcc_of_mem hS hz0]
    · simp only [indicator_of_notMem hz,indicator_of_notMem (show z∉s from hz)]
  rw [he]
  have hμs : (P.prod volume) s≠∞ := by
    have hset : s=(univ : Set Ω) ×ˢ Ioc a S := by ext z; simp [s]
    rw [hset,Measure.prod_prod]
    simp
  have hdom := memLp_indicator_const (μ := P.prod volume) 2 hs C (Or.inr hμs)
  have hi : MemLp (s.indicator K) 2 (P.prod volume) := by
    apply hdom.mono' (hK.indicator hs).aestronglyMeasurable
    apply ae_of_all
    intro z
    by_cases hz : z∈s
    · have hz0 : z.2∈Icc 0 S := ⟨ha.trans hz.1.le,hz.2⟩
      simp only [indicator_of_mem hz]
      dsimp only [K]
      rw [intervalClamp_eq 0 S hS hz0,projIcc_of_mem hS hz0]
      exact hbound z.1 z.2 hz0
    · simp only [indicator_of_notMem hz,norm_zero,le_refl]
  exact ⟨hK.indicator hs,hi.mono_measure
    (Measure.prod_mono (le_refl P) (Measure.restrict_le_self : volume.restrict (Ioi (0:ℝ))≤volume))⟩

end Asakura.Chapter5

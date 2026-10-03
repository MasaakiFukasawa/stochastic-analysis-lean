import Chapter6LinearBSDEDriver
import Chapter7FiniteDriftExtension

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter7
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Constant extension of a coefficient off [0,R] supplies joint and
progressive measurability from the manuscript's continuous adapted paths. -/
lemma finite_coefficient_regularity {Ω : Type*} {m : MeasurableSpace Ω}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (H : ℝ → Ω → ℝ) (R : ℝ) (hR : 0≤R)
    (ha : ∀ r∈Icc 0 R,Measurable[F (realTimeClamp r)] (H r))
    (hc : ∀ w,ContinuousOn (fun r => H r w) (Icc 0 R)) :
    let G := fun z : Ω × ℝ => finiteDriftExtension H R z.2 z.1
    Measurable G ∧
    (∀ t : Icc (0:ℝ) R,@Measurable _ _ ((F (realTimeClamp t.val)).prod inferInstance) inferInstance
      (fun p : Ω × Iic t => G (p.1,p.2.val.val))) := by
  let G := fun z : Ω × ℝ => finiteDriftExtension H R z.2 z.1
  have he := finite_drift_extension H R hR hc
  have hm r : Measurable (finiteDriftExtension H R r) :=
    (ha _ ⟨le_max_left _ _,max_le hR (min_le_left _ _)⟩).mono (hle _) le_rfl
  have hj := measurable_uncurry_of_continuous_of_measurable he.1 hm
  refine ⟨?_,?_⟩
  · simpa only [Function.comp_def,Function.uncurry_def,Prod.swap] using hj.comp measurable_swap
  · have hp := continuous_adapted_real_progressive F hF G R hR
      (fun r hr => by simpa only [G,he.2 r hr] using ha r hr)
      (fun w => (he.1 w).continuousOn)
    exact (measurable_progressive_iff _ _).mp hp

end Asakura.Chapter6

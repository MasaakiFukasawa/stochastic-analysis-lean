import Chapter5ForwardUnitBSDE

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

/-- Both printed applications of Feynman--Kac for the explicit formulas,
with the C² neighborhood and PDE at the endpoint derived from f. -/
theorem constructed_burgers_two_BSDEs
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c)
    (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → C (realTimeClamp r) w = r)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (B : ℕ → ℝ)
    (hb : ∀ n x,‖iteratedDeriv n f x‖≤B n) (a : ℝ) (ha : a≠0) :
    ∃ w v : ℝ × ℝ → ℝ,
      (∀ t x,0≤t → w (t,x)=logHeat a (fun y => Real.exp (a*f y)) x t) ∧
      (∀ t x,0≤t → v (t,x)=heatRatio a (fun y => Real.exp (a*f y))
        (fun y => a*deriv f y*Real.exp (a*f y)) x t) ∧
      (∀ x,w (0,x)=f x ∧ v (0,x)=deriv f x) ∧
      ForwardUnitBSDE P F X R hR w (fun _ z => a/2*z^2) ∧
      ForwardUnitBSDE P F X R hR v (fun y z => a*y*z) := by
  obtain ⟨O,w,v,hO,hs,hw,hv,hew,hev,hwx,hinit,hpw,hpv⟩ :=
    bounded_smooth_burgers_closed_data f hf B hb a ha
  refine ⟨w,v,hew,hev,hinit,?_,?_⟩
  · apply forward_unit_PDE_to_BSDE P hT F hF hle hnull X C hX hC R hR hRT
      w O hO hs (hw.of_le (by norm_num)) (fun _ z => a/2*z^2) ?_ c hc hcm hcT hcc hclock
    intro t x ht
    simpa only [hwx t x ht] using hpw t x ht
  · exact forward_unit_PDE_to_BSDE P hT F hF hle hnull X C hX hC R hR hRT
      v O hO hs hv (fun y z => a*y*z) hpv c hc hcm hcT hcc hclock

end Asakura.Chapter5

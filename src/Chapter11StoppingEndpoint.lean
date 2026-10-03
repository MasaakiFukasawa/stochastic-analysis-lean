import Chapter11BarrierGradient

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter7
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Including or excluding the single stopping time makes no difference
to time integration. This applies even when the stopping time is infinite. -/
theorem stopping_endpoint_time_ae (τ : HalfClosedTime) (T : ℝ) (g : ℝ → ℝ) :
    (fun t => if realTimeClamp (T:=(⊤:EReal)) t<τ then g t else 0)=ᵐ[volume.restrict (Ioo 0 T)]
      fun t => (Ioc (⊥ : HalfClosedTime) τ).indicator (fun _ => g t) (realTimeClamp t) := by
  classical
  have hne : ∀ᵐ t : ℝ ∂volume,t≠(halfTimeReal τ : ℝ) := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_of_ae hne,ae_restrict_mem measurableSet_Ioo] with t ht htT
  have he : realTimeClamp (T:=(⊤:EReal)) t≠τ := by
    intro h
    have hh := congrArg (fun q : HalfClosedTime => (halfTimeReal q : ℝ)) h
    rw [changed_time_real t htT.1.le] at hh
    exact ht hh
  have ht0 : (⊥ : HalfClosedTime)<realTimeClamp (T:=(⊤:EReal)) t := by
    change (0:EReal)<(realTimeClamp (T:=(⊤:EReal)) t:EReal)
    rw [real_time_clamp_eq t htT.1.le le_top]
    exact_mod_cast htT.1
  have hiff : realTimeClamp (T:=(⊤:EReal)) t<τ ↔ realTimeClamp (T:=(⊤:EReal)) t≤τ := lt_iff_le_and_ne.trans (and_iff_left he)
  simp only [Set.indicator_apply,mem_Ioc,ht0,true_and,hiff]

end Asakura.Chapter11

import Chapter4ContinuousGluing

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000

/-- Simultaneous gluing of finitely many continuous adapted coordinates. -/
theorem continuous_adapted_pieces_glue
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0≤T)] {dim : ℕ} (F : ClosedTime T → MeasurableSpace Ω)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (τ : ℕ → Ω → ClosedTime T) (hm : ∀ w,Monotone (fun n => τ n w))
    (ht : ∀ n w,τ n w<⊤) (hco : ∀ w t,t<⊤ → ∃ n,t<τ n w)
    (A : ℕ → ClosedTime T → Ω → Fin dim → ℝ)
    (ha : ∀ n t,Measurable[F t] (A n t)) (hc : ∀ n w,Continuous (fun t => A n t w))
    (he : ∀ᵐ w ∂P,∀ n k,n≤k → ∀ t,A k (min (τ n w) t) w=A n t w) :
    ∃ X : ClosedTime T → Ω → Fin dim → ℝ,
      (∀ t,t<⊤ → Measurable[F t] (X t)) ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t) ∧
      (∀ᵐ w ∂P,∀ n t,X (min (τ n w) t) w=A n t w) := by
  have hh i := Asakura.Chapter4.continuous_adapted_pieces_glue P F hnull τ hm ht hco
    (fun n t w => A n t w i) (fun n t => (measurable_pi_apply i).comp (ha n t))
    (fun n w => (continuous_apply i).comp (hc n w))
    (he.mono (fun w hw n k hnk t => congrFun (hw n k hnk t) i))
  choose G hgm hgc hge hgl hgs hgt using hh
  refine ⟨fun t w i => G i t w,?_,?_,?_⟩
  · intro t h
    letI : MeasurableSpace Ω := F t
    exact measurable_pi_iff.mpr (fun i => hgm i t h)
  · intro w t h
    exact continuousAt_pi.mpr (fun i => hgc i w t h)
  · filter_upwards [ae_all_iff.mpr hge] with w hw
    intro n t
    funext i
    exact hw i n t

end Asakura.Chapter4.Vector

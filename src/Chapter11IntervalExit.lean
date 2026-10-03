import Chapter11BarrierExitLimit

open Set Filter MeasureTheory
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2400000

noncomputable def intervalExit (X : HalfClosedTime → ℝ) (l u : ℝ) : HalfClosedTime :=
  sInf {t | t=⊤ ∨ X t≤l ∨ u≤X t}

theorem interval_exit_stopping {Ω : Type*}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (X : HalfClosedTime → Ω → ℝ)
    (hm : ∀ t,t<⊤ → Measurable[F t] (X t))
    (hc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (l u : ℝ) (R : HalfClosedTime) :
    ∀ t,MeasurableSet[F t] {w | min (intervalExit (fun s => X s w) l u) R≤t} := by
  have hhit := open_continuous_hitting_stopping F hF X hm hc (Iic l∪Ici u)
    (isClosed_Iic.union isClosed_Ici)
  intro t
  have he : {w | min (intervalExit (fun s => X s w) l u) R≤t}=
      {w | intervalExit (fun s => X s w) l u≤t}∪{_w : Ω | R≤t} := by
    ext w
    simp only [mem_setOf_eq,mem_union,min_le_iff]
  rw [he]
  apply MeasurableSet.union
  · simpa only [intervalExit,mem_union,mem_Iic,mem_Ici] using hhit t
  · by_cases h : R≤t <;> simp [h]

theorem before_interval_exit_bounds
    (X : HalfClosedTime → ℝ) (hc : ∀ t,t<⊤ → ContinuousAt X t)
    (l u : ℝ) (h0 : l<X ⊥ ∧ X ⊥<u)
    (r : ℝ) (hr : 0≤r) (hτ : realTimeClamp r≤ intervalExit X l u) :
    X (realTimeClamp r)∈Icc l u := by
  have hu : intervalExit X l u≤upperBarrierHit (fun t => X t-u) := by
    apply sInf_le_sInf
    intro t ht
    rcases ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr (Or.inr (by linarith))
  have hl : intervalExit X l u≤upperBarrierHit (fun t => l-X t) := by
    apply sInf_le_sInf
    intro t ht
    rcases ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr (Or.inl (by linarith))
  have hupper := before_upper_hit_nonpos (fun t => X t-u)
    (fun t ht => (hc t ht).sub continuousAt_const) (by linarith [h0.2]) r hr (hτ.trans hu)
  have hlower := before_upper_hit_nonpos (fun t => l-X t)
    (fun t ht => continuousAt_const.sub (hc t ht)) (by linarith [h0.1]) r hr (hτ.trans hl)
  exact ⟨by linarith,by linarith⟩

end Asakura.Chapter11

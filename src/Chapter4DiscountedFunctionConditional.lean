import Chapter4DiscountedConditional

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Apply discounting to continuous time-space functions of an actual
adapted continuous state process. -/
theorem discounted_function_conditional
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X : ClosedTime T → Ω → Fin d → ℝ)
    (hXa : ∀ t,t<⊤ → Measurable[F t] (X t))
    (hXc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (f k g : ℝ × (Fin d → ℝ) → ℝ) (hf : Continuous f) (hk : Continuous k) (hg : Continuous g)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hkpos : ∀ r∈Icc 0 R,∀ x,0≤k (r,x))
    (B : Ω → ℝ) (hB : MemLp B 2 P)
    (hb : ∀ᵐ w ∂P,∀ r∈Icc 0 R,|f (r,X (realTimeClamp r) w)|≤B w ∧ |g (r,X (realTimeClamp r) w)|≤B w)
    (N : ClosedTime T → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (he : ∀ r∈Icc 0 R,(fun w => f (r,X (realTimeClamp r) w))=ᵐ[P]
      fun w => f (0,X ⊥ w)+N (realTimeClamp r) w+
        ∫ a in 0..r,k (a,X (realTimeClamp a) w)*f (a,X (realTimeClamp a) w)-g (a,X (realTimeClamp a) w))
    (s : ℝ) (hs : s∈Icc 0 R) :
    let V := fun r w => f (r,X (realTimeClamp r) w)*discountFactor (fun a => k (a,X (realTimeClamp a) w)) r+
      ∫ a in 0..r,g (a,X (realTimeClamp a) w)*discountFactor (fun b => k (b,X (realTimeClamp b) w)) a
    P[V R | F (realTimeClamp s)]=ᵐ[P] V s := by
  dsimp only
  let c := fun t : ClosedTime T => (finitePrefixTime R hR t).val
  let Y := fun t w => (c t,X t w)
  have hYa t ht : Measurable[F t] (Y t) := measurable_const.prodMk (hXa t ht)
  have hYc w t ht : ContinuousAt (fun a => Y a w) t :=
    ((continuous_subtype_val.comp (finite_prefix_time_continuous R hR)).continuousAt).prodMk (hXc w t ht)
  have hc r (hr : r∈Icc 0 R) : c (realTimeClamp r)=r := finite_prefix_time_of_real R r hR hr hRT.le
  have hc0 : c ⊥=0 := by
    change (min (0:EReal) (R:EReal)).toReal=0
    rw [min_eq_left (by exact_mod_cast hR),EReal.toReal_zero]
  have he' r (hr : r∈Icc 0 R) : (fun w => f (Y (realTimeClamp r) w))=ᵐ[P]
      fun w => f (Y ⊥ w)+N (realTimeClamp r) w+
        ∫ a in 0..r,k (Y (realTimeClamp a) w)*f (Y (realTimeClamp a) w)-g (Y (realTimeClamp a) w) := by
    filter_upwards [he r hr] with w hw
    dsimp only [Y]
    rw [hc r hr,hc0,hw]
    congr 1
    apply intervalIntegral.integral_congr
    intro a ha
    dsimp only
    rw [hc a (Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using ha))]
  have hbe : ∀ᵐ w ∂P,∀ r∈Icc 0 R,|f (Y (realTimeClamp r) w)|≤B w ∧ |g (Y (realTimeClamp r) w)|≤B w := by
    filter_upwards [hb] with w hw
    intro r hr
    simpa only [Y,hc r hr] using hw r hr
  have hh := discounted_drift_conditional P hT F hF hle hnull
    (fun t w => f (Y t w)) N (fun t w => k (Y t w)) (fun t w => g (Y t w)) hN
    (fun t ht => hf.measurable.comp (hYa t ht)) (fun w t ht => hf.continuousAt.comp (hYc w t ht))
    (fun t ht => hk.measurable.comp (hYa t ht)) (fun w t ht => hk.continuousAt.comp (hYc w t ht))
    (fun t ht => hg.measurable.comp (hYa t ht)) (fun w t ht => hg.continuousAt.comp (hYc w t ht))
    R hR hRT (fun w r hr => by simpa only [Y,hc r hr] using hkpos r hr (X (realTimeClamp r) w))
    B hB hbe he' s hs
  have hd w a (ha : a∈Icc 0 R) :
      discountFactor (fun b => k (Y (realTimeClamp b) w)) a=
        discountFactor (fun b => k (b,X (realTimeClamp b) w)) a := by
    dsimp only [discountFactor]
    congr 2
    apply intervalIntegral.integral_congr
    intro b hb
    dsimp only [Y]
    rw [hc b (Icc_subset_Icc_right ha.2 (by simpa only [uIcc_of_le ha.1] using hb))]
  have hV r (hr : r∈Icc 0 R) :
      (fun w => f (Y (realTimeClamp r) w)*discountFactor (fun a => k (Y (realTimeClamp a) w)) r+
        ∫ a in 0..r,g (Y (realTimeClamp a) w)*discountFactor (fun b => k (Y (realTimeClamp b) w)) a)=
      (fun w => f (r,X (realTimeClamp r) w)*discountFactor (fun a => k (a,X (realTimeClamp a) w)) r+
        ∫ a in 0..r,g (a,X (realTimeClamp a) w)*discountFactor (fun b => k (b,X (realTimeClamp b) w)) a) := by
    funext w
    rw [hd w r hr]
    dsimp only [Y]
    rw [hc r hr]
    congr 1
    apply intervalIntegral.integral_congr
    intro a ha
    have ha' : a∈Icc 0 R := Icc_subset_Icc_right hr.2 (by simpa only [uIcc_of_le hr.1] using ha)
    dsimp only
    rw [hc a ha',hd w a ha']
  dsimp only at hh
  rwa [hV R ⟨hR,le_rfl⟩,hV s hs] at hh

end Asakura.Chapter4

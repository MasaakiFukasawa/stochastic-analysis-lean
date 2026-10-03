import Chapter7OpenClosedHitting
import Chapter11StoppedHarmonic
import Mathlib.Topology.Order.IntermediateValue

open Set Filter MeasureTheory
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

noncomputable def upperBarrierHit (X : HalfClosedTime → ℝ) : HalfClosedTime :=
  sInf {s | s=⊤ ∨ 0≤X s}

/-- A continuous path cannot be strictly above the barrier at or before
its first hitting time. This includes the value at the hitting time. -/
theorem before_upper_hit_nonpos (X : HalfClosedTime → ℝ)
    (hc : ∀ t,t<⊤ → ContinuousAt X t) (h0 : X ⊥<0)
    (r : ℝ) (hr : 0≤r) (hτ : realTimeClamp r≤upperBarrierHit X) :
    X (realTimeClamp r)≤0 := by
  by_contra hn
  have hp : 0<X (realTimeClamp r) := lt_of_not_ge hn
  have hz : realTimeClamp (T:=(⊤:EReal)) 0=⊥ := by
    apply Subtype.ext
    simpa using real_time_clamp_eq (T:=(⊤:EReal)) 0 le_rfl le_top
  have hcont : ContinuousOn (fun s : ℝ => X (realTimeClamp s)) (Icc 0 r) := by
    intro s hs
    exact ((hc _ (real_time_below s hs.1 (EReal.coe_lt_top s))).comp real_time_clamp_continuous.continuousAt).continuousWithinAt
  obtain ⟨q,hq,he⟩ := intermediate_value_Icc hr hcont (show (0:ℝ)∈Icc (X (realTimeClamp 0)) (X (realTimeClamp r)) by rw [hz];exact ⟨h0.le,hp.le⟩)
  have hqr : q<r := lt_of_le_of_ne hq.2 (by intro h;rw [h] at he;linarith)
  have hqτ : upperBarrierHit X≤realTimeClamp q := sInf_le (show realTimeClamp q∈{s : HalfClosedTime | s=⊤ ∨ 0≤X s} from Or.inr he.ge)
  have hstrict : realTimeClamp (T:=(⊤:EReal)) q<realTimeClamp r := by
    change (realTimeClamp q:EReal)<(realTimeClamp r:EReal)
    rw [real_time_clamp_eq q hq.1 le_top,real_time_clamp_eq r hr le_top]
    exact EReal.coe_lt_coe_iff.mpr hqr
  exact (not_lt_of_ge (hτ.trans hqτ)) hstrict

theorem at_upper_hit_zero (X : HalfClosedTime → ℝ)
    (hc : ∀ t,t<⊤ → ContinuousAt X t) (h0 : X ⊥<0)
    (hτ : upperBarrierHit X<⊤) : X (upperBarrierHit X)=0 := by
  have hm := (open_hitting_set_closed X hc (Ici 0) isClosed_Ici).sInf_mem
    (show {s : HalfClosedTime | s=⊤ ∨ X s∈Ici 0}.Nonempty from ⟨⊤,Or.inl rfl⟩)
  have hnon : 0≤X (upperBarrierHit X) := hm.resolve_left (ne_of_lt hτ)
  obtain ⟨r,hr,hrT,he⟩ := finite_closed_time_real (upperBarrierHit X) hτ
  have hle := before_upper_hit_nonpos X hc h0 r hr he.le
  rw [he] at hle
  exact le_antisymm hle hnon

/-- Construct the finite capped hitting time, including its stopping-time
property and the closed-region bound required by the pricing proof. -/
theorem upper_hit_finite_cap {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (X : HalfClosedTime → Ω → ℝ)
    (hm : ∀ t,t<⊤ → Measurable[F t] (X t))
    (hc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (h0 : ∀ᵐ w ∂P,X ⊥ w<0) (R : ℝ) (hR : 0≤R) :
    ∃ τ : Ω → Icc (0:ℝ) R,
      (∀ w,realTimeClamp (τ w).val=min (upperBarrierHit (fun s => X s w)) (realTimeClamp R)) ∧
      (∀ t,MeasurableSet[F t] {w | realTimeClamp (τ w).val≤t}) ∧
      (∀ᵐ w ∂P,∀ t∈Icc 0 R,X (realTimeClamp (min (τ w).val t)) w≤0) := by
  have hstop := open_continuous_hitting_stopping F hF X hm hc (Ici 0) isClosed_Ici
  have hf w : min (upperBarrierHit (fun s => X s w)) (realTimeClamp R)<⊤ :=
    (min_le_right _ _).trans_lt (real_time_below R hR (EReal.coe_lt_top R))
  choose q hq hqt hqe using fun w => finite_closed_time_real _ (hf w)
  have hqR w : q w≤R := by
    have hh : realTimeClamp (T:=(⊤:EReal)) (q w)≤realTimeClamp R := hqe w ▸ min_le_right _ _
    change (realTimeClamp (q w):EReal)≤(realTimeClamp R:EReal) at hh
    rw [real_time_clamp_eq _ (hq w) le_top,real_time_clamp_eq R hR le_top] at hh
    exact EReal.coe_le_coe_iff.mp hh
  let τ := fun w => (⟨q w,hq w,hqR w⟩ : Icc (0:ℝ) R)
  refine ⟨τ,hqe,?_,?_⟩
  · intro t
    have he : {w | realTimeClamp (τ w).val≤t}=
        {w | upperBarrierHit (fun s => X s w)≤t}∪{w : Ω | realTimeClamp (T:=(⊤:EReal)) R≤t} := by
      ext w
      simp only [mem_setOf_eq,mem_union,show (τ w).val=q w from rfl,hqe,min_le_iff]
    rw [he]
    apply (hstop t).union
    by_cases ht : realTimeClamp (T:=(⊤:EReal)) R≤t <;> simp [ht]
  · filter_upwards [h0] with w hw
    intro t ht
    apply before_upper_hit_nonpos (fun s => X s w) (hc w) hw _ (le_min (hq w) ht.1)
    rw [real_time_clamp_mono.map_min]
    exact (min_le_left _ _).trans ((hqe w).le.trans (min_le_left _ _))

end Asakura.Chapter11

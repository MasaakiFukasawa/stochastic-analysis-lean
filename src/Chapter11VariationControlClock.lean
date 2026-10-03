import Chapter2ContinuousVariationIntegral
import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The control clock needed for mixed step approximation is the actual
 path total variation. Its continuity and adaptedness are consequences of
 the manuscript's A_loc assumption, not extra hypotheses on the market. -/
theorem variation_control_clock {Ω : Type*} {m : MeasurableSpace Ω}
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t≤m)
    (A : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hAc : ∀ w t,t<⊤ → ContinuousAt (fun s => A s w) t)
    (d : ℝ) (hd : 0≤d) (hdT : (d:EReal)<T) :
    let V := fun t w => pathVariation (fun s => A s w) t
    let B := fun w r => V (realTimeClamp (intervalClamp 0 d hd r)) w
    (∀ w,Monotone (B w)) ∧ (∀ w,Continuous (B w)) ∧
    (∀ r,Measurable (fun w => B w r)) ∧
    (∀ r : Icc (0:ℝ) d,Measurable[F (realTimeClamp r.val)] (fun w => B w r.val)) ∧
    (∀ w r,r∈Icc 0 d → B w r=V (realTimeClamp r) w) := by
  intro V B
  obtain ⟨hV,_,_,τ,hs,hm,ht,hco,hmon⟩ := adapted_local_total_variation hA hF
  have hbelow r := real_time_below (T:=T) (intervalClamp 0 d hd r)
    (intervalClamp_mem 0 d hd r).1 ((EReal.coe_le_coe (intervalClamp_mem 0 d hd r).2).trans_lt hdT)
  have hvm w : MonotoneOn (fun t => V t w) (Iio ⊤) := by
    intro s hs t ht hst
    obtain ⟨n,hn⟩ := hco w t ht
    have hh := (hmon n w).1 hst
    simpa only [min_eq_right hn.le,min_eq_right (hst.trans hn.le)] using hh
  have he w r (hr : r∈Icc 0 d) : B w r=V (realTimeClamp r) w := by
    dsimp only [B];rw [intervalClamp_eq 0 d hd hr]
  refine ⟨?_,?_,?_,?_,he⟩
  · intro w s t hst
    exact hvm w (hbelow s) (hbelow t) (real_time_clamp_mono (intervalClamp_mono 0 d hd hst))
  · intro w
    apply continuous_iff_continuousAt.mpr
    intro r
    have hh := ((local_path_variation_continuous hA hAc w _ (hbelow r)).comp real_time_clamp_continuous.continuousAt).comp (intervalClamp_continuous 0 d hd).continuousAt
    simpa only [Function.comp_def] using hh
  · intro r
    exact (hV.adapted _ (hbelow r)).mono (hle _) le_rfl
  · intro r
    have hh := hV.adapted (realTimeClamp r.val) (real_time_below r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt hdT))
    simpa only [he _ r.val r.property] using hh

/-- The measure constructed from the Jordan parts is precisely the
 Stieltjes measure of the variation clock. -/
theorem variation_control_measure_unique (κ : Measure ℝ) [IsFiniteMeasure κ]
    (d : ℝ) (hd : 0≤d) (B : ℝ → ℝ) (hB : MonotoneOn B (Icc 0 d))
    (hBc : ContinuousOn B (Icc 0 d))
    (hκ : ∀ s t,s≤t → κ.real (Ioc s t)=B (intervalClamp 0 d hd t)-B (intervalClamp 0 d hd s)) :
    κ=(intervalStieltjes 0 d hd B hB (fun r hr => (hBc r hr).mono inter_subset_left)).measure := by
  letI : IsFiniteMeasure (intervalStieltjes 0 d hd B hB (fun r hr => (hBc r hr).mono inter_subset_left)).measure := intervalStieltjes_finite _ _ _ _ _ _
  apply Measure.ext_of_Ioc
  intro s t hst
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  change κ.real (Ioc s t)=_
  rw [hκ s t hst.le,←intervalStieltjes_Ioc_real 0 d hd B hB _ s t hst.le]
  rfl

end Asakura.Chapter11

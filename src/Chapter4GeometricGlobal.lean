import Chapter4GeometricConstructed
import Chapter4ItoPrefixCongruence
import Chapter4ClockRegularity
import Chapter2CommonTimeEquality

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- The geometric example, with one constructed global Ito integral and
one exceptional set valid at every finite time. -/
theorem geometric_sde_global
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hC : LocalCovarianceWitness P F W W C)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → C (realTimeClamp r) w=r)
    (y a b : ℝ) :
    ∃ N : ClosedTime T → Ω → ℝ,LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W
        (fun z => b*geometricFlow y a b ![C (realTimeClamp z.2) z.1,W (realTimeClamp z.2) z.1]) N ∧
      ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T →
        geometricFlow y a b ![r,W (realTimeClamp r) w]=
          y+a*(∫ s in 0..r,geometricFlow y a b ![s,W (realTimeClamp s) w])+N (realTimeClamp r) w := by
  classical
  letI : MeasurableSpace Ω := m
  have hCv := covariance_adapted_variation P F hF hle hW hW hC
  obtain ⟨hCm,hCc⟩ := clock_regular_from_identity C hclock
  let H := fun t w => b*geometricFlow y a b ![C t w,W t w]
  have hf := (geometricFlow_smooth y a b).continuous
  have hHa t (ht : t<⊤) : Measurable[F t] (H t) := by
    letI : MeasurableSpace Ω := F t
    apply Measurable.const_mul _ b
    exact hf.measurable.comp (measurable_pi_iff.mpr (by intro i; fin_cases i; exact hCv.adapted t ht; exact hW.adapted P F t ht))
  have hHc w t (ht : t<⊤) : ContinuousAt (fun s => H s w) t := by
    apply ContinuousAt.const_mul _ b
    apply hf.continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact hCc w t ht
    · exact hW.path P F w t ht
  have hreg := open_process_real_regularity F H hHa hHc
  obtain ⟨N,hN,hNI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull W hW
    (fun z => H (realTimeClamp z.2) z.1) hreg.1 hreg.2
  have hfinite (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) :
      ∀ᵐ w ∂P,∀ r∈Icc 0 R,geometricFlow y a b ![r,W (realTimeClamp r) w]=
        y+a*(∫ s in 0..r,geometricFlow y a b ![s,W (realTimeClamp s) w])+N (realTimeClamp r) w := by
    obtain ⟨Z,hZ,hZI,he⟩ := geometric_sde_constructed P hT F hF hle hnull W C hW hC hclock R hR hRT y a b
    let K := fun t w => b*geometricFlow y a b ![(finitePrefixTime (T := T) R hR t).val,W t w]
    have hKa t (ht : t<⊤) : Measurable[F t] (K t) := by
      letI : MeasurableSpace Ω := F t
      apply Measurable.const_mul _ b
      exact hf.measurable.comp (measurable_pi_iff.mpr (by intro i; fin_cases i; exact measurable_const; exact hW.adapted P F t ht))
    have hKc w t (ht : t<⊤) : ContinuousAt (fun s => K s w) t := by
      apply ContinuousAt.const_mul _ b
      apply hf.continuousAt.comp
      apply continuousAt_pi.mpr
      intro i
      fin_cases i
      · exact (continuous_subtype_val.comp (finite_prefix_time_continuous R hR)).continuousAt
      · exact hW.path P F w t ht
    have hsame := brownian_ito_prefix_congr P hT F hF hle hnull W C hW hC hclock
      H K N Z hHa hKa hHc hKc hN hZ hNI hZI R hR hRT
      (.of_forall (fun w r hr => by
        dsimp only [H,K]
        rw [hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hRT),finite_prefix_time_of_real R r hR hr hRT.le]))
    let G := fun w s => geometricFlow y a b ![s,W (min (realTimeClamp R) (realTimeClamp s)) w]
    have hGc w : Continuous (G w) := by
      apply hf.comp
      apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_id
      · exact (open_path_stopped_continuous W (hW.path P F) R hR hRT w).comp real_time_clamp_continuous
    have hG w r (hr : r≤R) : G w r=geometricFlow y a b ![r,W (realTimeClamp r) w] := by
      dsimp only [G]
      rw [min_eq_right (real_time_clamp_mono hr)]
    have hint w r (hr : r∈Icc 0 R) : (∫ s in 0..r,G w s)=∫ s in 0..r,geometricFlow y a b ![s,W (realTimeClamp s) w] := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact hG w s ((by simpa [uIcc_of_le hr.1] using hs : s∈Icc 0 r).2.trans hr.2)
    letI : Nonempty (Icc (0:ℝ) R) := ⟨⟨0,le_rfl,hR⟩⟩
    have hc := continuous_process_common_time_equality P
      (fun r : Icc (0:ℝ) R => fun w => G w r.val)
      (fun r : Icc (0:ℝ) R => fun w => y+a*(∫ s in 0..r.val,G w s)+N (realTimeClamp r.val) w)
      (fun w => (hGc w).comp continuous_subtype_val)
      (fun w => (continuous_const.add (continuous_const.mul
        ((intervalIntegral.differentiable_integral_of_continuous (hGc w)).continuous.comp continuous_subtype_val))).add
        (by
          have hh := (open_path_stopped_continuous N (hN.path P F) R hR hRT w).comp
            (real_time_clamp_continuous.comp (continuous_subtype_val : Continuous (Subtype.val : Icc (0:ℝ) R → ℝ)))
          convert hh using 1
          funext r
          dsimp only [Function.comp_def]
          rw [min_eq_right (real_time_clamp_mono r.property.2)]))
      (fun r => by
        filter_upwards [he r.val r.property,hsame] with w hw hn
        rw [hG w r.val r.property.2,hint w r.val r.property,hn r.val r.property]
        exact hw)
    filter_upwards [hc] with w hw
    intro r hr
    simpa only [hG w r hr.2,hint w r hr] using hw ⟨r,hr⟩
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  refine ⟨N,hN,hNI,?_⟩
  filter_upwards [ae_all_iff.mpr (fun n => hfinite (c n) (hc n).le (hcT n))] with w hw
  intro r hr hrT
  obtain ⟨n,hn⟩ := hcc (realTimeClamp r) (real_time_below r hr hrT)
  have hrc : r≤c n := by
    change (realTimeClamp r:EReal)<(realTimeClamp (c n):EReal) at hn
    rw [real_time_clamp_eq r hr hrT.le,real_time_clamp_eq (c n) (hc n).le (hcT n).le] at hn
    exact EReal.coe_le_coe_iff.mp hn.le
  exact hw n r ⟨hr,hrc⟩

end Asakura.Chapter4

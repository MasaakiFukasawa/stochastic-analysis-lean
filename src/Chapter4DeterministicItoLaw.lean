import Chapter4DeterministicBracketLaw
import Chapter5BrownianBracketCommon

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The Gaussian law of the actual deterministic Brownian integral. -/
theorem deterministic_brownian_integral_law
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A N : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A) (hN : LocalMProcessWitness P F N)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hNI : ItoCovarianceFormula P F W (fun z => g z.2) N)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) :
    HasLaw (N (realTimeClamp R))
      (gaussianReal 0 ⟨∫ r in 0..R,g r^2,intervalIntegral.integral_nonneg_of_forall hR (fun _ => sq_nonneg _)⟩) P := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hgp n := continuous_adapted_real_progressive F hF (fun z : Ω × ℝ => g z.2) (c n) (hc n).le
    (fun r _ => (show Measurable[F (realTimeClamp r)] (fun _ : Ω => g r) from measurable_const)) (fun _ => hg.continuousOn)
  have hi n : ∀ᵐ w ∂P,IntervalIntegrable (fun r => g r^2) volume 0 (c n) :=
    ae_of_all _ fun _ => (hg.pow 2).intervalIntegrable 0 (c n)
  obtain ⟨C,hC,_,hCG⟩ := clock_ito_integral_bracket_common P hT F hF hle hnull W A N hW hA hN
    c hc hcm hcT hct hcut hcc
    (fun n w r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) _ hgp hi hNI
  let q := fun t : ClosedTime T => ∫ r in 0..(finitePrefixTime R hR t).val,g r^2
  have hRt := real_time_below R hR hRT
  have hqr : q (realTimeClamp R)=∫ r in 0..R,g r^2 := by
    dsimp only [q]
    rw [finite_prefix_time_of_real R R hR ⟨hR,le_rfl⟩ hRT.le]
  have hq0 : q ⊥=0 := by
    have hz : (finitePrefixTime (T := T) R hR ⊥).val=0 := by
      change (min (0:EReal) (R:EReal)).toReal=0
      rw [min_eq_left (by exact_mod_cast hR),EReal.toReal_zero]
    dsimp only [q]
    rw [hz,intervalIntegral.integral_same]
  have hqm : MonotoneOn q (Iic (realTimeClamp R)) := by
    intro s hs t ht hst
    let a := (finitePrefixTime R hR s).val
    let b := (finitePrefixTime R hR t).val
    have hab : a≤b := finite_prefix_time_mono R hR hst
    have ha : 0≤a := (finitePrefixTime R hR s).property.1
    have hb := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab (fun r => sq_nonneg (g r))
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((hg.pow 2).intervalIntegrable 0 a) ((hg.pow 2).intervalIntegrable a b)
    change (∫ r in 0..a,g r^2)≤∫ r in 0..b,g r^2
    simp only [Pi.pow_apply] at he
    linarith
  obtain ⟨j,hj⟩ := hcc _ hRt
  have hRj : R≤c j := by
    change (realTimeClamp R:EReal)<(realTimeClamp (c j):EReal) at hj
    rw [real_time_clamp_eq R hR hRT.le,real_time_clamp_eq (c j) (hc j).le (hcT j).le] at hj
    exact (EReal.coe_lt_coe_iff.mp hj).le
  have hq : ∀ᵐ w ∂P,∀ t,t≤realTimeClamp R → C t w=q t := by
    filter_upwards [hCG j] with w hw
    intro t ht
    obtain ⟨r,hr,hrT,rfl⟩ := finite_closed_time_real t (ht.trans_lt hRt)
    have hrR : r≤R := by
      change (realTimeClamp r:EReal)≤(realTimeClamp R:EReal) at ht
      rw [real_time_clamp_eq r hr hrT.le,real_time_clamp_eq R hR hRT.le] at ht
      exact EReal.coe_le_coe_iff.mp ht
    dsimp only [q]
    rw [finite_prefix_time_of_real R r hR ⟨hr,hrR⟩ hRT.le]
    exact hw r ⟨hr,hrR.trans hRj⟩
  have hl := (deterministic_bracket_gaussian_increment P hT F hF hle hnull N C hN hC
    q (realTimeClamp R) ⊥ hRt bot_le hqm hq).1
  have he : N (realTimeClamp R)=ᵐ[P] fun w => N (realTimeClamp R) w-N ⊥ w := by
    filter_upwards [hN.initial P F] with w hw
    simp only [hw,Pi.zero_apply,sub_zero]
  have hh := hl.congr he
  convert hh using 1
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_mk,hqr,hq0,sub_zero]

end Asakura.Chapter4

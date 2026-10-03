import Chapter4UnboundedElementaryM2
import Chapter4PredictableBrownianIncrement
import Chapter2StoppedM2Equivalence

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

lemma clock_stopped_m2
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hclock : ∀ w,A (realTimeClamp R) w=R) :
    ContinuousM2Witness P F (fun t w => W (min (realTimeClamp R) t) w) := by
  have hs (t) : MeasurableSet[F t] {w : Ω | realTimeClamp (T:=T) R≤t} := by
    by_cases hh : realTimeClamp (T:=T) R≤t <;> simp [hh]
  have he := stopped_local_M2_equivalences P F hF hle hnull W A hW hA
    (fun _ => realTimeClamp R) hs (fun _ => real_time_below R hR hRT)
  apply he.2.mp
  apply he.1.mp
  simpa only [hclock] using (integrable_const R : Integrable (fun _ : Ω => R) P)

/-- Elementary Brownian integration with an unbounded L2 predictable weight
is an actual continuous square-integrable martingale. -/
theorem brownian_elementary_m2
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (s : ℝ) (hs : s∈Icc 0 R)
    (G : Ω → ℝ) (hGa : Measurable[F (realTimeClamp s)] G) (hG : MemLp G 2 P) :
    ContinuousM2Witness P F (fun t w => G w*(W (min (realTimeClamp R) t) w-W (min (realTimeClamp s) t) w)) := by
  let a := realTimeClamp (T:=T) s
  let b := realTimeClamp (T:=T) R
  have hab : a≤b := real_time_clamp_mono hs.2
  have hsT : (s:EReal)<T := (EReal.coe_le_coe hs.2).trans_lt hRT
  have hWa := clock_stopped_m2 P F hF hle hnull W A hW hA s hs.1 hsT (fun w => hclock w s hs.1 hsT)
  have hWb := clock_stopped_m2 P F hF hle hnull W A hW hA R hR hRT (fun w => hclock w R hR hRT)
  let Z := fun t w => W (min b t) w-W (min a t) w
  have hZ : ContinuousM2Witness P F Z := by
    convert hWb.add P F (hWa.smul P F (-1)) using 1
    funext t w
    dsimp only [Z,a,b,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  apply predictable_scalar_delayed_martingale_of_product_moment P F hF hle Z hZ a
    (fun t ht => by funext w;dsimp only [Z];simp only [min_eq_right ht,min_eq_right (ht.trans hab),sub_self,Pi.zero_apply])
    G hGa
  intro t
  by_cases hat : a≤t
  · let r := (finitePrefixTime (T:=T) R hR t).val
    have hr : r∈Icc 0 R := (finitePrefixTime R hR t).property
    have hrt : realTimeClamp (T:=T) r=min b t := finite_prefix_time_clamp R hR hRT.le t
    have hsr : s≤r := by
      have hle' : realTimeClamp (T:=T) s≤realTimeClamp r := by rw [hrt];exact le_min hab hat
      change (realTimeClamp s:EReal)≤(realTimeClamp r:EReal) at hle'
      rw [real_time_clamp_eq s hs.1 hsT.le,real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hRT.le)] at hle'
      exact EReal.coe_le_coe_iff.mp hle'
    have hm := (predictable_brownian_increment_square_moment P hT F hF hle hnull W A hW hA hclock
      r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hRT) s ⟨hs.1,hsr⟩ G hGa hG).1
    simpa only [hrt,Z,min_eq_left hat,a] using hm
  · have hta := (le_of_not_ge hat)
    have he : (fun w => G w*Z t w)=fun _ => (0:ℝ) := by
      funext w
      dsimp only [Z]
      rw [min_eq_right hta,min_eq_right (hta.trans hab),sub_self,mul_zero]
    rw [he]
    exact memLp_const 0

end Asakura.Chapter4

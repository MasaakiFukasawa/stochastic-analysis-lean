import Chapter5StoppedIntegralFormula
import Chapter5BSDEDifference

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- An interval increment is the actual integral with support in (a,b].
Both the local martingale and the covariance formula are constructed. -/
theorem interval_supported_ito_formula
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X Y : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (H : Ω × ℝ → ℝ) (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hI : ItoCovarianceFormula P F X H Y) (a b : ℝ) (ha : 0≤a) (hab : a≤b) :
    let Z := fun t w => Y (min (realTimeClamp b) t) w-Y (min (realTimeClamp a) t) w
    LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F X (fun z => (Ioc a b).indicator (fun r => H (z.1,r)) z.2) Z := by
  dsimp only
  have hstop (r : ℝ) : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) r≤t} := by
    intro t
    by_cases h : realTimeClamp (T := T) r≤t <;> simp [h]
  have hYa := hY.stopped P F hF hle (fun _ => realTimeClamp a) (hstop a)
  have hYb := hY.stopped P F hF hle (fun _ => realTimeClamp b) (hstop b)
  have hIa := stopped_ito_covariance_formula P hT F hF hle hnull X Y H hX hY hHm hI a ha
  have hIb := stopped_ito_covariance_formula P hT F hF hle hnull X Y H hX hY hHm hI b (ha.trans hab)
  refine ⟨?_,?_⟩
  · simpa only [neg_one_mul,sub_eq_add_neg] using hYb.add P F hF hle (hYa.smul P F (-1))
  · have hh := bsde_difference_integral P F hF hle X _ _ _ _ hIb hIa
    have he : (fun z : Ω × ℝ => (Ioc 0 b).indicator (fun r => H (z.1,r)) z.2-
        (Ioc 0 a).indicator (fun r => H (z.1,r)) z.2)=
        (fun z => (Ioc a b).indicator (fun r => H (z.1,r)) z.2) := by
      funext z
      by_cases h0 : 0<z.2
      · by_cases ha' : z.2≤a
        · have hb' := ha'.trans hab
          simp [indicator,h0,ha',hb',not_lt_of_ge ha']
        · have har := lt_of_not_ge ha'
          by_cases hb' : z.2≤b <;> simp [indicator,h0,ha',har,hb']
      · have ha' : ¬a<z.2 := fun h => h0 (ha.trans_lt h)
        simp [indicator,h0,ha']
    rw [he] at hh
    exact hh

end Asakura.Chapter5

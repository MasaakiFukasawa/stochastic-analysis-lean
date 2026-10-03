import Chapter5IntervalIntegralFormula
import Chapter5BoundedBrownianIntegralM2
import Chapter3IncrementEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Each bounded Brownian interval increment is an actual M² integral,
so that its zero expectation is derived from the martingale property. -/
theorem bounded_brownian_interval_M2
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (W A Y : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hA : LocalCovarianceWitness P F W W A)
    (hY : LocalMProcessWitness P F Y)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (G : Ω × ℝ → ℝ) (hGm : ∀ w,Measurable (fun r => G (w,r)))
    (hGa : ∀ r : ℝ,0≤r → (r:EReal)<T → Measurable[F (realTimeClamp r)] (fun w => G (w,r)))
    (hGc : ∀ b : ℝ,0≤b → (b:EReal)<T → ∀ w,ContinuousOn (fun r => G (w,r)) (Icc 0 b))
    (hI : ItoCovarianceFormula P F W G Y)
    (a S C : ℝ) (ha : 0≤a) (haS : a≤S) (hST : (S:EReal)<T) (hC : 0≤C)
    (hbound : ∀ w r,r∈Icc 0 S → |G (w,r)|≤C) :
    let Z := fun t w => Y (min (realTimeClamp S) t) w-Y (min (realTimeClamp a) t) w
    ContinuousM2Witness P F Z ∧
      ItoCovarianceFormula P F W (fun z => (Ioc a S).indicator (fun r => G (z.1,r)) z.2) Z ∧
      (∫ w,Z ⊤ w ∂P)=0 := by
  dsimp only
  have hS := bounded_brownian_integral_stopped_M2 P hT F hF hle hnull W A Y hW hA hY
    hclock G hGa hGc hI S C (ha.trans haS) hST hC hbound
  have hRa := bounded_brownian_integral_stopped_M2 P hT F hF hle hnull W A Y hW hA hY
    hclock G hGa hGc hI a C ha ((EReal.coe_le_coe haS).trans_lt hST) hC
    (fun w r hr => hbound w r ⟨hr.1,hr.2.trans haS⟩)
  have hZ : ContinuousM2Witness P F
      (fun t w => Y (min (realTimeClamp S) t) w-Y (min (realTimeClamp a) t) w) := by
    convert hS.add P F (hRa.smul P F (-1)) using 1
    funext t w
    simp [sub_eq_add_neg]
  exact ⟨hZ,(interval_supported_ito_formula P hT F hF hle hnull W Y hW hY G hGm hI a S ha haS).2,
    Asakura.Chapter3Complete.m2_mean_zero P F hle _ hZ ⊤⟩

end Asakura.Chapter5

import Chapter12AsianCallDeltaExchange
import Chapter12AsianCallVegaExchange

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem asian_delta_exchange_on_trim {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0 < T)
    (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable[mT] X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x r σ K : ℝ) (hx : 0 < x) (hσ : 0 < σ) :
    HasDerivAt (fun a => ∫ w,max (asianPathAverage a r T T.property σ (X w)-K) 0 ∂P.trim hle)
      (∫ w,(if K < asianPathAverage x r T T.property σ (X w) then 1 else 0)*
        (asianPathAverage x r T T.property σ (X w)/x) ∂P.trim hle) x := by
  letI : MeasurableSpace Ω := m
  have hd := asian_call_delta_expectation_exchange P B hB hm hc T hT X (hXm.mono hle le_rfl) he x r σ K hx hσ
  have hAm (a : ℝ) : Measurable[mT] (fun w => asianPathAverage a r T T.property σ (X w)) := by
    letI : MeasurableSpace Ω := mT
    exact (asian_path_average_measurable a r T T.property σ).comp hXm
  have hf : (fun a => ∫ w,max (asianPathAverage a r T T.property σ (X w)-K) 0 ∂P) =
      (fun a => ∫ w,max (asianPathAverage a r T T.property σ (X w)-K) 0 ∂P.trim hle) := by
    funext a
    apply integral_trim hle
    letI : MeasurableSpace Ω := mT
    exact (((hAm a).sub_const K).max measurable_const).stronglyMeasurable
  have hv : (∫ w,(if K < asianPathAverage x r T T.property σ (X w) then 1 else 0)*
      (asianPathAverage x r T T.property σ (X w)/x) ∂P) =
      ∫ w,(if K < asianPathAverage x r T T.property σ (X w) then 1 else 0)*
      (asianPathAverage x r T T.property σ (X w)/x) ∂P.trim hle := by
    apply integral_trim hle
    letI : MeasurableSpace Ω := mT
    exact ((Measurable.ite (measurableSet_lt measurable_const (hAm x)) measurable_const measurable_const).mul
      ((hAm x).div_const x)).stronglyMeasurable
  rwa [hf,hv] at hd

theorem asian_vega_exchange_on_trim {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0 < T)
    (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable[mT] X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x r σ K : ℝ) (hx : 0 < x) (hσ : 0 < σ) :
    HasDerivAt (fun a => ∫ w,max (asianPathAverage x r T T.property a (X w)-K) 0 ∂P.trim hle)
      (∫ w,(if K < asianPathAverage x r T T.property σ (X w) then 1 else 0)*
        asianPathVega x r T T.property σ (X w) ∂P.trim hle) σ := by
  letI : MeasurableSpace Ω := m
  have hd := asian_call_vega_expectation_exchange P B hB hm hc T hT X (hXm.mono hle le_rfl) he x r σ K hx hσ
  have hAm (a : ℝ) : Measurable[mT] (fun w => asianPathAverage x r T T.property a (X w)) := by
    letI : MeasurableSpace Ω := mT
    exact (asian_path_average_measurable x r T T.property a).comp hXm
  have hf : (fun a => ∫ w,max (asianPathAverage x r T T.property a (X w)-K) 0 ∂P) =
      (fun a => ∫ w,max (asianPathAverage x r T T.property a (X w)-K) 0 ∂P.trim hle) := by
    funext a
    apply integral_trim hle
    letI : MeasurableSpace Ω := mT
    exact (((hAm a).sub_const K).max measurable_const).stronglyMeasurable
  have hv : (∫ w,(if K < asianPathAverage x r T T.property σ (X w) then 1 else 0)*
      asianPathVega x r T T.property σ (X w) ∂P) =
      ∫ w,(if K < asianPathAverage x r T T.property σ (X w) then 1 else 0)*
      asianPathVega x r T T.property σ (X w) ∂P.trim hle := by
    apply integral_trim hle
    letI : MeasurableSpace Ω := mT
    exact ((Measurable.ite (measurableSet_lt measurable_const (hAm σ)) measurable_const measurable_const).mul
      ((asian_path_vega_measurable x r T T.property σ).comp hXm)).stronglyMeasurable
  rwa [hf,hv] at hd

end Asakura.Chapter12

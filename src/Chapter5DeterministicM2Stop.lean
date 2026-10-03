import Chapter5RepresentationEndpoints
import Chapter5IntervalIntegralFormula

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Deterministic stopping preserves the actual M² process conditions. -/
theorem deterministic_stopped_M2
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t≤m)
    (M : ClosedTime T → Ω → ℝ) (hM : ContinuousM2Witness P F M) (a : ClosedTime T) :
    ContinuousM2Witness P F (fun t w => M (min a t) w) := by
  refine ⟨(fun t => (hM.adapted _).mono (hF (min_le_right _ _)) le_rfl),
    (fun t => hM.moment _),(fun w => (hM.path w).comp (continuous_const.min continuous_id)),?_,?_⟩
  · intro s t hst
    by_cases has : a≤s
    · rw [min_eq_left has,min_eq_left (has.trans hst)]
      rw [condExp_of_stronglyMeasurable (hle s) ((hM.adapted a).mono (hF has) le_rfl).stronglyMeasurable
        ((hM.moment a).integrable (by norm_num))]
    · have hsa := le_of_not_ge has
      rw [min_eq_right hsa]
      exact hM.martingale s (min a t) (le_min hsa hst)
  · simpa only [min_eq_right bot_le] using hM.initial

/-- An M² terminal representation is restricted to its actual interval;
the resulting stopped difference is still M² and has the same terminal payoff. -/
theorem represented_M2_interval_restriction
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (W M : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hM : ContinuousM2Witness P F M) (hMl : LocalMProcessWitness P F M)
    (H : Ω × ℝ → ℝ) (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hMI : ItoCovarianceFormula P F W H M)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) (ξ : Ω → ℝ)
    (hMa : M (realTimeClamp a) =ᵐ[P] 0) (hMb : M (realTimeClamp b) =ᵐ[P] ξ) :
    ∃ Z : ClosedTime T → Ω → ℝ,
      ContinuousM2Witness P F Z ∧ LocalMProcessWitness P F Z ∧
      ItoCovarianceFormula P F W (fun z => (Ioc a b).indicator (fun r => H (z.1,r)) z.2) Z ∧
      Z ⊤ =ᵐ[P] ξ := by
  let Z := fun t w => M (min (realTimeClamp b) t) w-M (min (realTimeClamp a) t) w
  have hZ : ContinuousM2Witness P F Z := by
    convert (deterministic_stopped_M2 P F hF hle M hM (realTimeClamp b)).add P F
      ((deterministic_stopped_M2 P F hF hle M hM (realTimeClamp a)).smul P F (-1)) using 1
    funext t w
    simp [Z,sub_eq_add_neg]
  have hz := interval_supported_ito_formula P hT F hF hle hnull W M hW hMl H hHm hMI a b ha hab
  refine ⟨Z,hZ,hz.1,hz.2,?_⟩
  filter_upwards [hMa,hMb] with w hwa hwb
  simp only [Z,min_eq_left le_top,hwa,hwb,Pi.zero_apply,sub_zero]

end Asakura.Chapter5

import Chapter8CLTConsistency
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

open MeasureTheory Filter
open scoped Topology
namespace Asakura.Chapter8
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- Positive diverging observation sequences suffice for a real-time
limit at infinity; no restriction to integer observation times is made. -/
theorem probability_limit_from_observation_sequences {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoEMetricSpace E] (P : Measure Ω) (X : ℝ → Ω → E) (Z : Ω → E)
    (hseq : ∀ (T : ℕ → ℝ),(∀ n,0<T n) → Tendsto T atTop atTop →
      TendstoInMeasure P (fun n => X (T n)) atTop Z) :
    TendstoInMeasure P X atTop Z := by
  intro ε hε
  apply Filter.tendsto_of_seq_tendsto
  intro u hu
  let T := fun n => max (u n) 1
  have hT n : 0<T n := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  have hTlim : Tendsto T atTop atTop := tendsto_atTop_mono (fun n => le_max_left _ _) hu
  have hh := hseq T hT hTlim ε hε
  apply hh.congr'
  filter_upwards [hu.eventually (eventually_ge_atTop (1:ℝ))] with n hn
  simp only [T,max_eq_left hn,Function.comp_def]

theorem distribution_limit_from_observation_sequences {Ω Γ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ → Ω → E) (Z : Γ → E)
    (hm : ∀ t,AEMeasurable (X t) P) (hmZ : AEMeasurable Z Q)
    (hseq : ∀ (T : ℕ → ℝ),(∀ n,0<T n) → Tendsto T atTop atTop →
      TendstoInDistribution (fun n => X (T n)) atTop Z (fun _ => P) Q) :
    TendstoInDistribution X atTop Z (fun _ => P) Q := by
  refine ⟨hm,hmZ,?_⟩
  apply Filter.tendsto_of_seq_tendsto
  intro u hu
  let T := fun n => max (u n) 1
  have hT n : 0<T n := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  have hTlim : Tendsto T atTop atTop := tendsto_atTop_mono (fun n => le_max_left _ _) hu
  apply (hseq T hT hTlim).tendsto.congr'
  filter_upwards [hu.eventually (eventually_ge_atTop (1:ℝ))] with n hn
  apply Subtype.ext
  change P.map (X (T n))=P.map (X (u n))
  rw [show T n=u n from max_eq_left hn]

end Asakura.Chapter8

import Chapter2LocalProcess
import FullAuditVariationStopping

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Pathwise finite variation of a continuous adapted process implies
membership in the manuscript's A: the two increasing parts are adapted,
not merely arbitrary pathwise choices. They are constructed from total variation. -/
theorem adapted_continuous_jordan_decomposition
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → ℝ)
    (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω))
    (hb : ∀ ω, BoundedVariationOn (fun t => X t ω) univ) :
    ∃ U V : ClosedTime T → Ω → ℝ,
      (∀ t, Measurable[F t] (U t)) ∧ (∀ t, Measurable[F t] (V t)) ∧
      (∀ ω, Continuous (fun t => U t ω)) ∧ (∀ ω, Continuous (fun t => V t ω)) ∧
      (∀ ω, Monotone (fun t => U t ω)) ∧ (∀ ω, Monotone (fun t => V t ω)) ∧
      ∀ t ω, X t ω = U t ω - V t ω := by
  let A := fun t ω => pathVariation (fun s => X s ω) t
  have hAm (t) : Measurable[F t] (A t) := variation_process_adapted F hF X hm hc t
  have hAc (ω) : Continuous (fun t => A t ω) := variation_process_continuous _ (hb ω) (hc ω)
  have he (ω t) : variationOnFromTo (fun s => X s ω) univ ⊥ t = A t ω := by
    rw [variationOnFromTo.eq_of_le _ _ bot_le,univ_inter,Icc_bot]
    rfl
  refine ⟨fun t ω => (A t ω+X t ω)/2,fun t ω => (A t ω-X t ω)/2,
    fun t => ((hAm t).add (hm t)).div_const 2,
    fun t => ((hAm t).sub (hm t)).div_const 2,
    fun ω => ((hAc ω).add (hc ω)).div_const 2,
    fun ω => ((hAc ω).sub (hc ω)).div_const 2,?_,?_,?_⟩
  · intro ω s t hst
    have h := variationOnFromTo.add_self_monotoneOn (hb ω).locallyBoundedVariationOn
      (mem_univ (⊥ : ClosedTime T)) (mem_univ s) (mem_univ t) hst
    simp only [Pi.add_apply,he] at h
    exact div_le_div_of_nonneg_right h (by norm_num)
  · intro ω s t hst
    have h := variationOnFromTo.sub_self_monotoneOn (hb ω).locallyBoundedVariationOn
      (mem_univ (⊥ : ClosedTime T)) (mem_univ s) (mem_univ t) hst
    simp only [Pi.sub_apply,he] at h
    exact div_le_div_of_nonneg_right h (by norm_num)
  · intro t ω
    ring

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.adapted_continuous_jordan_decomposition

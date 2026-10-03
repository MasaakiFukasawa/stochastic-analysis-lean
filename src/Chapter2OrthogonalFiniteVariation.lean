import Chapter2CumulativeIntegral
import FullAuditMartingaleHilbert

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- The stochastic step in the H2 orthogonal-complement proof: testing
against all bounded F_a variables makes the cumulative finite-variation
process a martingale, and A intersect M2 = 0 then forces it to vanish.
Construction of this process from G dA is handled separately. -/
theorem finite_variation_zero_of_orthogonal_past_tests
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (N : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (N t))
    (h2 : ∀ t, MemLp (N t) 2 P) (hc : ∀ ω, Continuous (fun t => N t ω))
    (hBV : ∀ ω, ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧ ∀ t, N t ω = U t-V t)
    (hz : N ⊥ =ᵐ[P] 0)
    (horth : ∀ s t, s ≤ t → ∀ Z : Ω → ℝ,
      Measurable[F s] Z → MemLp Z ∞ P → (∫ ω, Z ω * (N t ω-N s ω) ∂P) = 0) :
    ∀ᵐ ω ∂P, ∀ t, N t ω = 0 := by
  classical
  apply A_inter_M2_zero_written P F hF hle N hm h2 hc hBV ?_ hz
  intro s t hst
  apply Filter.EventuallyEq.symm
  have hi (t) := (h2 t).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  apply ae_eq_condExp_of_forall_setIntegral_eq (hle s) (hi t)
    (fun _ _ _ => (hi s).integrableOn) _ (hm s).stronglyMeasurable.aestronglyMeasurable
  intro E hE _
  let Z := E.indicator (fun _ : Ω => (1:ℝ))
  have hZm : Measurable[F s] Z := measurable_const.indicator hE
  have hZinf : MemLp Z ∞ P := by
    apply memLp_top_of_bound (hZm.mono (hle s) le_rfl).aestronglyMeasurable 1
    exact .of_forall fun ω => by by_cases h : ω ∈ E <;> simp [Z,Set.indicator,h]
  have h := horth s t hst Z hZm hZinf
  have he : (fun ω => Z ω * (N t ω-N s ω)) = E.indicator (N t-N s) := by
    funext ω
    by_cases h : ω ∈ E <;> simp [Z,Set.indicator,h]
  rw [he,integral_indicator (hle s _ hE)] at h
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hi t).integrableOn (hi s).integrableOn] at h
  linarith

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_variation_zero_of_orthogonal_past_tests

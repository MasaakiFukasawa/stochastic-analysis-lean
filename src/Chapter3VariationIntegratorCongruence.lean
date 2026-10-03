import Chapter3VariationIntegrandCongruence

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The variation integral depends only on the increments of the integrator. -/
theorem variation_integral_integrator_increments_congr
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (A B I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hI : VariationIntegralFormula P c hc A H I)
    (he : ∀ᵐ ω ∂P, ∀ s t, s < ⊤ → t < ⊤ → A t ω-A s ω = B t ω-B s ω) :
    VariationIntegralFormula P c hc B H I := by
  intro n
  obtain ⟨ν,hs,hν,hi,hform⟩ := hI n
  refine ⟨ν,hs,?_,hi,hform⟩
  filter_upwards [hν,he] with ω hνω heω
  have hrt (r : ℝ) : realTimeClamp (T := T) (intervalClamp 0 (c n) (hc n) r) < ⊤ := by
    have hr := intervalClamp_mem 0 (c n) (hc n) r
    change (realTimeClamp _ : EReal) < T
    rw [real_time_clamp_eq _ hr.1 ((EReal.coe_le_coe hr.2).trans (hcT n).le)]
    exact (EReal.coe_le_coe hr.2).trans_lt (hcT n)
  intro s t hst
  exact (hνω s t hst).trans (heω _ _ (hrt s) (hrt t))

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.variation_integral_integrator_increments_congr

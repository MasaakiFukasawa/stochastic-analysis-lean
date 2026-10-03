import Chapter2VariationStoppedInterval
import Chapter2ItoCovarianceCharacterization

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The finite-variation part of rep263 in the manuscript's actual time
coordinates. Measurability of the stopping times is needed separately for
membership of the stopped processes, not for this pathwise formula. -/
theorem VariationIntegralFormula.stochastic_interval
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hcT : ∀ n, (c n:EReal) < T)
    (A I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hI : VariationIntegralFormula P c hc A H I)
    (σ τ : Ω → ClosedTime T) (hσT : ∀ ω, σ ω < ⊤) (hτT : ∀ ω, τ ω < ⊤)
    (hστ : ∀ ω, σ ω ≤ τ ω) :
    VariationIntegralFormula P c hc A
      (fun z => (Ioc (σ z.1) (τ z.1)).indicator (fun _ => H z) (realTimeClamp z.2))
      (fun t ω => I (min (τ ω) t) ω-I (min (σ ω) t) ω) := by
  choose s hs0 hsT hse using fun ω => finite_closed_time_real (σ ω) (hσT ω)
  choose v hv0 hvT hve using fun ω => finite_closed_time_real (τ ω) (hτT ω)
  have hsv ω : s ω ≤ v ω := by
    have hh := hστ ω
    rw [← hse ω,← hve ω] at hh
    change (realTimeClamp (s ω):EReal) ≤ (realTimeClamp (v ω):EReal) at hh
    rw [real_time_clamp_eq _ (hs0 ω) (hsT ω).le,real_time_clamp_eq _ (hv0 ω) (hvT ω).le] at hh
    exact EReal.coe_le_coe_iff.mp hh
  have hreal := hI.stochastic_interval_real P c hc A I H s v hs0 hv0
    (fun ω => (hsT ω).le) (fun ω => (hvT ω).le) hsv
  simp only [hse,hve] at hreal
  apply hreal.congr_on_time_domain P c hc hcT A _ _ _
  intro ω r hr hrT
  have hmem : r ∈ Ioc (s ω) (v ω) ↔ realTimeClamp r ∈ Ioc (σ ω) (τ ω) := by
    rw [← hse ω,← hve ω]
    change (s ω < r ∧ r ≤ v ω) ↔
      ((realTimeClamp (s ω):EReal) < (realTimeClamp r:EReal) ∧
        (realTimeClamp r:EReal) ≤ (realTimeClamp (v ω):EReal))
    rw [real_time_clamp_eq _ (hs0 ω) (hsT ω).le,real_time_clamp_eq _ hr hrT.le,
      real_time_clamp_eq _ (hv0 ω) (hvT ω).le]
    simp only [EReal.coe_lt_coe_iff,EReal.coe_le_coe_iff]
  by_cases hh : r ∈ Ioc (s ω) (v ω)
  · simp only [indicator_of_mem hh,indicator_of_mem (hmem.mp hh)]
  · simp only [indicator_of_notMem hh,indicator_of_notMem (fun hm => hh (hmem.mpr hm))]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.VariationIntegralFormula.stochastic_interval

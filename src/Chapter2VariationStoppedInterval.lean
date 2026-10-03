import Chapter2VariationIntegralFormula
import Chapter2StochasticIntervalIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem finite_prefix_time_real_stop
    {T : EReal} [Fact (0 ≤ T)] (d a : ℝ) (hd : 0 ≤ d)
    (ha : 0 ≤ a) (haT : (a:EReal) ≤ T) (t : ClosedTime T) :
    (finitePrefixTime d hd (min (realTimeClamp a) t)).val =
      min a (finitePrefixTime d hd t).val := by
  have he : (finitePrefixTime d hd (realTimeClamp (T := T) a)).val = min a d := by
    change (min (realTimeClamp a : EReal) (d:EReal)).toReal = min a d
    rw [real_time_clamp_eq a ha haT]
    by_cases had : a ≤ d
    · rw [min_eq_left (EReal.coe_le_coe had),min_eq_left had,EReal.toReal_coe]
    · rw [min_eq_right (EReal.coe_le_coe (le_of_not_ge had)),min_eq_right (le_of_not_ge had),EReal.toReal_coe]
  have hmin' : finitePrefixTime d hd (min (realTimeClamp a) t) =
      min (finitePrefixTime d hd (realTimeClamp a)) (finitePrefixTime d hd t) :=
    (finite_prefix_time_mono (T := T) d hd).map_min
  have hmin := congrArg Subtype.val hmin'
  change (finitePrefixTime d hd (min (realTimeClamp a) t)).val =
    min (finitePrefixTime d hd (realTimeClamp a)).val (finitePrefixTime d hd t).val at hmin
  rw [hmin,he,min_assoc,min_eq_right (finitePrefixTime d hd t).property.2]

theorem VariationIntegralFormula.stochastic_interval_real
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (A I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hI : VariationIntegralFormula P c hc A H I)
    (σ τ : Ω → ℝ) (hσ : ∀ ω, 0 ≤ σ ω) (hτ : ∀ ω, 0 ≤ τ ω)
    (hσT : ∀ ω, (σ ω:EReal) ≤ T) (hτT : ∀ ω, (τ ω:EReal) ≤ T)
    (hστ : ∀ ω, σ ω ≤ τ ω) :
    VariationIntegralFormula P c hc A
      (fun z => (Ioc (σ z.1) (τ z.1)).indicator (fun r => H (z.1,r)) z.2)
      (fun t ω => I (min (realTimeClamp (τ ω)) t) ω-I (min (realTimeClamp (σ ω)) t) ω) := by
  intro n
  obtain ⟨ξ,hs,hξ,hi,he⟩ := hI n
  refine ⟨ξ,hs,hξ,?_,?_⟩
  · filter_upwards [hi] with ω hω
    exact hω.indicator (s := Ioc (σ ω) (τ ω)) measurableSet_Ioc
  · filter_upwards [hi,he] with ω hiω heω
    intro t
    change I (min (realTimeClamp (τ ω)) (min (realTimeClamp (c n)) t)) ω-
      I (min (realTimeClamp (σ ω)) (min (realTimeClamp (c n)) t)) ω = _
    rw [min_left_comm (realTimeClamp (τ ω)) (realTimeClamp (c n)) t,
      min_left_comm (realTimeClamp (σ ω)) (realTimeClamp (c n)) t,heω,heω,
      finite_prefix_time_real_stop (c n) (τ ω) (hc n) (hτ ω) (hτT ω),
      finite_prefix_time_real_stop (c n) (σ ω) (hc n) (hσ ω) (hσT ω)]
    exact (signed_cumulative_stochastic_interval (ξ ω) _ hiω (σ ω) (τ ω) _ (hστ ω)).symm

theorem VariationIntegralFormula.congr_on_time_domain
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hcT : ∀ n, (c n:EReal) < T)
    (A I : ClosedTime T → Ω → ℝ) (H G : Ω × ℝ → ℝ)
    (hI : VariationIntegralFormula P c hc A H I)
    (he : ∀ ω (r : ℝ), 0 ≤ r → (r:EReal) < T → H (ω,r) = G (ω,r)) :
    VariationIntegralFormula P c hc A G I := by
  intro n
  obtain ⟨ξ,hs,hξ,hi,hform⟩ := hI n
  have hEq : ∀ᵐ ω ∂P, (fun r => H (ω,r)) =ᵐ[(ξ ω).totalVariation] (fun r => G (ω,r)) := by
    filter_upwards [hs] with ω hω
    filter_upwards [hω] with r hr
    exact he ω r hr.1.le ((EReal.coe_le_coe hr.2).trans_lt (hcT n))
  refine ⟨ξ,hs,hξ,?_,?_⟩
  · filter_upwards [hi,hEq] with ω hiω heω
    exact hiω.congr heω
  · filter_upwards [hform,hEq] with ω hfω heω
    intro t
    rw [hfω t]
    apply signed_integral_congr_of_absolute_continuity (ξ ω).totalVariation (ξ ω) (by rfl)
    filter_upwards [heω] with r hr
    by_cases hs : r ∈ Iic (finitePrefixTime (c n) (hc n) t).val <;> simp [signedCumulative,hs,hr]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.VariationIntegralFormula.stochastic_interval_real
#print axioms Asakura.Chapter2Complete.VariationIntegralFormula.congr_on_time_domain

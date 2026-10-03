import Chapter2OriginalVariationIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The actual signed Stieltjes integral, characterized on a cofinal
family of finite prefixes. Measures are specified by all their increments. -/
def VariationIntegralFormula
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (A : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ) (I : ClosedTime T → Ω → ℝ) : Prop :=
  ∀ n, ∃ ξ : Ω → SignedMeasure ℝ,
    (∀ᵐ ω ∂P, ∀ᵐ r ∂(ξ ω).totalVariation, r ∈ Ioc 0 (c n)) ∧
    (∀ᵐ ω ∂P, ∀ s t, s ≤ t → ξ ω (Ioc s t) =
      A (realTimeClamp (intervalClamp 0 (c n) (hc n) t)) ω-
      A (realTimeClamp (intervalClamp 0 (c n) (hc n) s)) ω) ∧
    (∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (ξ ω).totalVariation) ∧
    (∀ᵐ ω ∂P, ∀ t, I (min (realTimeClamp (c n)) t) ω =
      signedCumulative (ξ ω) (fun r => H (ω,r)) (finitePrefixTime (c n) (hc n) t).val)

theorem VariationIntegralFormula.unique
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (A I J : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hI : VariationIntegralFormula P c hc A H I) (hJ : VariationIntegralFormula P c hc A H J) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → I t ω = J t ω := by
  have he n : ∀ᵐ ω ∂P, ∀ t, I (min (realTimeClamp (c n)) t) ω = J (min (realTimeClamp (c n)) t) ω := by
    obtain ⟨ξ,_,hξ,_,heI⟩ := hI n
    obtain ⟨η,_,hη,_,heJ⟩ := hJ n
    filter_upwards [hξ,hη,heI,heJ] with ω hξω hηω hIω hJω
    have heq : ξ ω = η ω := signed_measure_ext_Ioc _ _
      (fun a b hab => (hξω a b hab.le).trans (hηω a b hab.le).symm)
    intro t
    rw [hIω t,hJω t,heq]
  filter_upwards [ae_all_iff.mpr he] with ω hω
  intro t ht
  obtain ⟨n,hn⟩ := hcc t ht
  simpa only [min_eq_right hn.le] using hω n t

theorem VariationIntegralFormula.congr_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hcT : ∀ n, (c n:EReal) < T)
    (A I J : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hI : VariationIntegralFormula P c hc A H I)
    (he : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → I t ω = J t ω) :
    VariationIntegralFormula P c hc A H J := by
  intro n
  obtain ⟨ξ,hs,hξ,hi,hform⟩ := hI n
  refine ⟨ξ,hs,hξ,hi,?_⟩
  filter_upwards [he,hform] with ω heω hfω
  intro t
  have hdt : realTimeClamp (T := T) (c n) < ⊤ := by
    change (realTimeClamp (c n) : EReal) < T
    rw [real_time_clamp_eq (c n) (hc n) (hcT n).le]; exact hcT n
  rw [← heω _ ((min_le_left _ _).trans_lt hdt)]
  exact hfω t

theorem variation_integral_formula_of_construction
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (A I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (κ : ℕ → Ω → Measure ℝ) (ξ : ℕ → Ω → SignedMeasure ℝ)
    (hsupport : ∀ n ω, ∀ᵐ r ∂κ n ω, r ∈ Ioc 0 (c n))
    (hξ : ∀ n ω s t, s ≤ t → ξ n ω (Ioc s t) =
      A (realTimeClamp (intervalClamp 0 (c n) (hc n) t)) ω-
      A (realTimeClamp (intervalClamp 0 (c n) (hc n) s)) ω)
    (hdom : ∀ n ω, (ξ n ω).totalVariation ≤ κ n ω)
    (hi : ∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (κ n ω))
    (he : ∀ᵐ ω ∂P, ∀ n t, I (min (realTimeClamp (c n)) t) ω =
      signedCumulative (ξ n ω) (fun r => H (ω,r)) (finitePrefixTime (c n) (hc n) t).val) :
    VariationIntegralFormula P c hc A H I := by
  intro n
  exact ⟨ξ n,.of_forall (fun ω => ae_mono (hdom n ω) (hsupport n ω)),.of_forall (hξ n),(hi n).mono (fun ω hω => hω.mono_measure (hdom n ω)),
    he.mono (fun ω hω => hω n)⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.VariationIntegralFormula.unique
#print axioms Asakura.Chapter2Complete.variation_integral_formula_of_construction

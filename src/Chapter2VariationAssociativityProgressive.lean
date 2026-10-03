import Chapter2VariationAssociativity
import Chapter2ProgressivePathEncoding

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem VariationIntegralFormula.congr_on_prefixes
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (A I : ClosedTime T → Ω → ℝ) (H G : Ω × ℝ → ℝ)
    (hI : VariationIntegralFormula P c hc A H I)
    (he : ∀ n ω r, r ∈ Icc 0 (c n) → H (ω,r) = G (ω,r)) :
    VariationIntegralFormula P c hc A G I := by
  intro n
  obtain ⟨ξ,hs,hξ,hi,hform⟩ := hI n
  have hEq : ∀ᵐ ω ∂P, (fun r => H (ω,r)) =ᵐ[(ξ ω).totalVariation] (fun r => G (ω,r)) := by
    filter_upwards [hs] with ω hω
    exact hω.mono (fun r hr => he n ω r ⟨hr.1.le,hr.2⟩)
  refine ⟨ξ,hs,hξ,?_,?_⟩
  · filter_upwards [hi,hEq] with ω hiω heω
    exact hiω.congr heω
  · filter_upwards [hform,hEq] with ω hfω heω
    intro t
    rw [hfω t]
    apply signed_integral_congr_of_absolute_continuity (ξ ω).totalVariation (ξ ω) (by rfl)
    filter_upwards [heω] with r hr
    by_cases hs : r ∈ Iic (finitePrefixTime (c n) (hc n) t).val <;> simp [hs,hr]

/-- No extra measurability beyond the original time domain is needed in
finite-variation associativity. Measurable real extensions are constructed
and eliminated using the support of each finite-horizon measure. -/
theorem variation_integral_associativity_progressive
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (A J K L : ClosedTime T → Ω → ℝ) (H G : Ω × ℝ → ℝ)
    (hH : ∀ n, @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)))
    (hG : ∀ n, @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hJ : VariationIntegralFormula P c hc A G J)
    (hK : VariationIntegralFormula P c hc J H K)
    (hL : VariationIntegralFormula P c hc A (fun z => H z*G z) L) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → K t ω = L t ω := by
  obtain ⟨H',hHm,hHe⟩ := progressive_paths_measurable_encoding F c hc H hH
  obtain ⟨G',hGm,hGe⟩ := progressive_paths_measurable_encoding F c hc G hG
  apply variation_integral_associativity P c hc hcT hcc A J K L H' G' hHm hGm
  · exact hJ.congr_on_prefixes P c hc A J G G' (fun n ω r hr => (hGe n ω r hr).symm)
  · exact hK.congr_on_prefixes P c hc J K H H' (fun n ω r hr => (hHe n ω r hr).symm)
  · apply hL.congr_on_prefixes P c hc A L _ _
    intro n ω r hr
    rw [hHe n ω r hr,hGe n ω r hr]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.variation_integral_associativity_progressive

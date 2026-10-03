import Chapter6ConditionalYoungBound

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
namespace Asakura.Chapter6
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Conditional Schwarz in the form needed for the bridge: the increment
second moment carries the vanishing factor delta. -/
theorem conditional_bridge_growth_bound {Ω E : Type*} {m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (b X : Ω → E)
    (hb : MemLp b 2 P) (hX : MemLp X 2 P) (G : MeasurableSpace Ω)
    (A D δ : ℝ) (hδ : 0<δ) (F : Ω → ℝ)
    (hbb : ∀ᵐ w ∂P,P[(fun w => ‖b w‖^2)|G] w≤A*F w)
    (hxb : ∀ᵐ w ∂P,P[(fun w => ‖X w‖^2)|G] w≤D*F w*δ) :
    ∀ᵐ w ∂P,|P[(fun w => ⟪b w,X w⟫_ℝ)|G] w|≤((A+D)/2)*F w*Real.sqrt δ := by
  letI : MeasurableSpace Ω := m
  have hq : 0<Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hi := conditional_inner_young_bound P b X hb hX (Real.sqrt δ) hq G
  filter_upwards [hi,hbb,hxb] with w hi hbb hxb
  have h1 := mul_le_mul_of_nonneg_left hbb (show 0≤Real.sqrt δ/2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hxb (show 0≤1/(2*Real.sqrt δ) by positivity)
  have he : (Real.sqrt δ/2)*(A*F w)+(1/(2*Real.sqrt δ))*(D*F w*δ)=((A+D)/2)*F w*Real.sqrt δ := by
    have hs := Real.sq_sqrt hδ.le
    field_simp
    nlinarith [congrArg (fun z : ℝ => D*F w*z) hs,congrArg (fun z : ℝ => A*F w*z) hs]
  linarith

end Asakura.Chapter6

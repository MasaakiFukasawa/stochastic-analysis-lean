import Chapter10ConditionalDriftCancellation

open MeasureTheory
namespace Asakura.Chapter10
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Apply conditional expectation to the actual product increment after
conditional Fubini has removed the two drift terms. -/
theorem conditional_product_increment {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : MeasurableSpace Ω) (hH : H≤m)
    (U D E Z : Ω → ℝ) (c : ℝ) (hD : Integrable D P) (hE : Integrable E P)
    (hZ : Integrable Z P) (he : U=ᵐ[P] fun w => D w+E w+c+Z w)
    (hcD : P[D|H]=ᵐ[P] 0) (hcE : P[E|H]=ᵐ[P] 0) (hcZ : P[Z|H]=ᵐ[P] 0) :
    P[U|H]=ᵐ[P] (fun _ => c) := by
  have h1 := condExp_add hD hE H
  have h2 := condExp_add (hD.add hE) (integrable_const c) H
  have h3 := condExp_add ((hD.add hE).add (integrable_const c)) hZ H
  have hc : P[(fun _ : Ω => c)|H]=(fun _ => c) :=
    condExp_of_stronglyMeasurable hH stronglyMeasurable_const (integrable_const c)
  have he' : U=ᵐ[P] ((D+E)+(fun _ => c))+Z := he
  filter_upwards [condExp_congr_ae (m := H) he',h1,h2,h3,hcD,hcE,hcZ] with w hw h1 h2 h3 hD hE hZ
  simp only [Pi.add_apply,hc,hD,hE,hZ,Pi.zero_apply,zero_add,add_zero] at h1 h2 h3
  rw [hw,h3,h2,h1]
  simp

end Asakura.Chapter10

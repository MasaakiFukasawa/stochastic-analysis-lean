import Chapter10LinearStateWitness

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false

lemma LinearStateWitness.real_equation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (G : Fin d → Fin n → ℝ → ℝ) (ξ : Ω → Fin d → ℝ)
    (T : ℝ) (hT : 0≤T) (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X)
    (w : Ω) (t : Icc (0:ℝ) T) (i : Fin d) :
    X w t i=ξ w i+(∫ s in 0..t.val,(A s (X w (projIcc 0 T hT s))) i)+
      ∑ j,N i j (realTimeClamp t.val) w := by
  have hh := (h.decomposition i).decomposition (realTimeClamp t.val) (half_real_time_finite t.val) w
  have hp : finitePrefixTime T hT (realTimeClamp t.val)=t :=
    Subtype.ext (finite_prefix_time_of_real T t.val hT t.property le_top)
  simpa only [hp,min_eq_right (real_time_clamp_mono t.property.2)] using hh

end Asakura.Chapter10

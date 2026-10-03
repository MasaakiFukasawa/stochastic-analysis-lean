import Chapter4MarkovLipschitz
import Chapter8BrownianForcingPath

open MeasureTheory Set
open scoped NNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The conditional expectation used by the time-average argument follows
from the actual SDE Markov theorem, with no separate Markov hypothesis. -/
theorem sde_markov_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (L : ℝ) (hL : 0≤L)
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(b i x-b i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (ξ : Ω → Fin d → ℝ) (hξ : MemLp ξ 2 P)
    (X : HalfClosedTime → Ω → Fin d → ℝ) (hX : VectorSDESolution P B.F B.W b σ ξ X)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W b σ (fun _ => x) (Z x))
    (f : (Fin d → ℝ) → ℝ) (hf : Measurable f) (K : ℝ) (hK : ∀ x,‖f x‖≤K)
    (s t : ℝ) (hs : 0≤s) (hst : s≤t) :
    P[(fun w => f (X (realTimeClamp t) w)) | B.F (realTimeClamp s)]=ᵐ[P]
      fun w => ∫ y,f (Z (X (realTimeClamp s) w) (realTimeClamp (t-s)) y) ∂P := by
  have h := (markov_from_lipschitz_coefficients P B L hL b σ hLip ξ hξ X hX Z hZ
    s (t-s) hs (sub_nonneg.mpr hst)).2 f hf K hK
  have he x : (∫ y,f y ∂P.map (Z x (realTimeClamp (t-s))))=
      ∫ w,f (Z x (realTimeClamp (t-s)) w) ∂P := by
    apply integral_map
    · exact ((hZ x).adapted _ (half_real_time_finite _)).mono (B.le _) le_rfl |>.aemeasurable
    · exact hf.aestronglyMeasurable
  simpa only [add_sub_cancel,he] using h

end Asakura.Chapter8

import Chapter10FiniteIntegralLinearityAE

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Uniqueness of the actual deterministic-coefficient integral, allowing
different semimartingale decompositions of the same integrator. -/
theorem deterministic_integral_congr_ae {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X Y A M D N U Z : HalfClosedTime → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hX' : SemimartingaleDecomposition P F Y D N)
    (he : ∀ᵐ w ∂P,∀ t,t<⊤ → Y t w=X t w)
    (H : HalfClosedTime → ℝ) (hH : ∀ t,t<⊤ → ContinuousAt H t)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hU : SemimartingaleIntegralFormula P F c hc A M (fun z => H (realTimeClamp z.2)) U)
    (hZ : SemimartingaleIntegralFormula P F c hc D N (fun z => H (realTimeClamp z.2)) Z) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → Z t w=U t w := by
  have he := finite_deterministic_integral_linearity_ae (ι := Unit) P F hF hle hnull
    (fun _ => X) (fun _ => A) (fun _ => M) (fun _ => U) Y D N Z
    (fun _ => hX) hX' (fun _ => H) H (fun _ => hH) hH c hc hcT hcc
    (fun _ => hU) hZ (by
      filter_upwards [he] with w hw
      intro s t hs ht
      rw [hw s hs,hw t ht]
      simp)
  simpa only [Fintype.sum_unique] using he

end Asakura.Chapter10

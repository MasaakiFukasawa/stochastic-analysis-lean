import Chapter10LinearStateWitness

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The finite-horizon state witness only depends on the drift coefficient
on that horizon. It therefore transfers from a bounded extension. -/
theorem LinearStateWitness.congr_drift {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A A' : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (G : Fin d → Fin n → ℝ → ℝ)
    (ξ : Ω → Fin d → ℝ) (T : ℝ) (hT : 0≤T)
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X)
    (he : ∀ s∈Icc 0 T,A' s=A s) : LinearStateWitness P B A' G ξ T hT N X := by
  refine ⟨h.noise,h.ito,h.measurable,h.moment,?_⟩
  intro i
  have hv : (fun (t : HalfClosedTime) w => ξ w i+∫ s in 0..(finitePrefixTime T hT t).val,
      (A' s (X w (projIcc 0 T hT s))) i)=
      (fun t w => ξ w i+∫ s in 0..(finitePrefixTime T hT t).val,(A s (X w (projIcc 0 T hT s))) i) := by
    funext t w
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (finitePrefixTime T hT t).property.1] at hs
    dsimp only
    rw [he s ⟨hs.1,hs.2.trans (finitePrefixTime T hT t).property.2⟩]
  rw [hv]
  exact h.decomposition i

end Asakura.Chapter10

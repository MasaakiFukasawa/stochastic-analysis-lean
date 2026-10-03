import Chapter10LinearStateSemimartingale

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4

/-- The constructed state retains its actual driving Ito integrals and drift
 decomposition, so its moment equations can be used for this very SDE. -/
structure LinearStateWitness {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (G : Fin d → Fin n → ℝ → ℝ)
    (ξ : Ω → Fin d → ℝ) (T : ℝ) (hT : 0≤T)
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)) : Prop where
  noise : ∀ i j,LocalMProcessWitness P B.F (N i j)
  ito : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j)
  measurable : Measurable X
  moment : MemLp X 2 P
  decomposition : ∀ i,SemimartingaleDecomposition P B.F
    (fun t w => X w (finitePrefixTime T hT t) i)
    (fun t w => ξ w i+∫ s in 0..(finitePrefixTime T hT t).val,(A s (X w (projIcc 0 T hT s))) i)
    (fun t w => ∑ j,N i j (min (realTimeClamp T) t) w)

end Asakura.Chapter10

import Chapter4DeterministicSDEFamily
import Chapter4ClassicalSolutionData

open MeasureTheory
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4

/-- Existence packaged as the actual SDE interface, with a random square-
integrable initial value. -/
theorem random_sde_exists {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (L : ℝ) (hL : 0≤L)
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (hLip : ∀ x y,(∑i,(b i x-b i y)^2)+(∑i,∑j,(σ i j x-σ i j y)^2)≤L*∑i,(x i-y i)^2)
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξ2 : MemLp ξ 2 P) :
    ∃X : HalfClosedTime → Ω → Fin d → ℝ,VectorSDESolution P B.F B.W b σ ξ X := by
  obtain ⟨X,N,ha,hc,hN,hI,_,he⟩ := Vector.sde_exists_from_manuscript_hypotheses
    P (EReal.coe_lt_top 0) B.F B.mono B.le B.null B.W (fun j => B.C j j)
    B.martingale (fun j => B.cov j j) (fun j w r hr _ => B.diagonal_clock j w r hr)
    L hL b σ hLip ξ hξ hξ2
  exact ⟨X,hξ,ha,hc,N,hN,hI,he⟩

#print axioms random_sde_exists
end Asakura.EndToEnd

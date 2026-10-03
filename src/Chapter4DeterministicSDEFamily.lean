import Chapter4MarkovLipschitz
import Chapter4VectorManuscriptExistence

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The reference family of transition laws is obtained from the already
proved SDE existence theorem, for every deterministic initial point. -/
theorem deterministic_sde_family_exists
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] {dim noise : ℕ}
    (B : BrownianSystem P noise) (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(μ i x-μ i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2) :
    ∃ Z : (Fin dim → ℝ) → HalfClosedTime → Ω → Fin dim → ℝ,
      ∀ x,VectorSDESolution P B.F B.W μ σ (fun _ => x) (Z x) := by
  have hex (x : Fin dim → ℝ) : ∃ X : HalfClosedTime → Ω → Fin dim → ℝ,
      VectorSDESolution P B.F B.W μ σ (fun _ => x) X := by
    obtain ⟨X,N,ha,hc,hN,hI,_,he⟩ := Vector.sde_exists_from_manuscript_hypotheses
      P (EReal.coe_lt_top 0) B.F B.mono B.le B.null B.W (fun j => B.C j j)
      B.martingale (fun j => B.cov j j) (fun j w r hr _ => B.diagonal_clock j w r hr)
      L hL μ σ hLip (fun _ => x) measurable_const (memLp_const x)
    exact ⟨X,measurable_const,ha,hc,N,hN,hI,he⟩
  choose Z hZ using hex
  exact ⟨Z,hZ⟩

end Asakura.Chapter4

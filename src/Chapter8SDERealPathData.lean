import Chapter8BrownianForcingPath
import Chapter4SDEInitialConditionalLaw

open MeasureTheory Set
open scoped NNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Measurability, continuity and second moments for the real-time extension
of the actual SDE solution, including the frozen extension before time zero. -/
theorem sde_real_path_data {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (L : ℝ) (hL : 0≤L)
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(b i x-b i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (ξ : Ω → Fin d → ℝ) (hξ : MemLp ξ 2 P)
    (X : HalfClosedTime → Ω → Fin d → ℝ) (hX : VectorSDESolution P B.F B.W b σ ξ X) :
    let Y := fun t w => X (realTimeClamp (max 0 t)) w
    (∀ w,Continuous (fun t => Y t w)) ∧
      Measurable (fun z : Ω × ℝ => Y z.2 z.1) ∧
      (∀ t,MemLp (Y t) 2 P) ∧
      (∀ t,Measurable[B.F (realTimeClamp (max 0 t))] (Y t)) := by
  dsimp only
  have hm t : Measurable[B.F (realTimeClamp (max 0 t))] (X (realTimeClamp (max 0 t))) :=
    hX.adapted _ (half_real_time_finite _)
  have hc w : Continuous (fun t => X (realTimeClamp (max 0 t)) w) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hX.path w _ (half_real_time_finite _)).comp real_time_clamp_continuous.continuousAt).comp
      (continuous_const.max continuous_id).continuousAt
  refine ⟨hc,?_,?_,hm⟩
  · exact (measurable_uncurry_of_continuous_of_measurable hc
      (fun t => (hm t).mono (B.le _) le_rfl)).comp measurable_swap
  · intro t
    exact (sde_finite_path_memLp P (EReal.coe_lt_top 0) rfl B.F B.mono B.le B.null
      B.W (fun j => B.C j j) B.martingale (fun j => B.cov j j)
      (fun j w r hr _ => B.diagonal_clock j w r hr) L hL b σ hLip ξ hξ X hX
      (max 0 t) (le_max_left _ _) (EReal.coe_lt_top _)).2.2

end Asakura.Chapter8

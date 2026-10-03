import Chapter4SDEInitialConditionalLaw
import Chapter4SmoothMeasureDetermination
import Chapter8BrownianForcingPath

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Start an actual Lipschitz SDE from an invariant law. The law at every
later time is derived from the proved conditional transition formula,
rather than assumed as a property of a stationary process. -/
theorem sde_stationary_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (L : ℝ) (hL : 0≤L)
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(b i x-b i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π]
    (ξ : Ω → Fin d → ℝ) (hξ : MemLp ξ 2 P) (hξlaw : P.map ξ=π)
    (X : HalfClosedTime → Ω → Fin d → ℝ) (hX : VectorSDESolution P B.F B.W b σ ξ X)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W b σ (fun _ => x) (Z x))
    (hinv : ∀ t : ℝ,0≤t → ∀ f : (Fin d → ℝ) → ℝ,
      ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      (∫ x,(∫ w,f (Z x (realTimeClamp t) w) ∂P) ∂π)=∫ x,f x ∂π)
    (t : ℝ) (ht : 0≤t) : P.map (X (realTimeClamp t))=π := by
  have hmξ : Measurable ξ := hX.initial_adapted.mono (B.le _) le_rfl
  have hmX : Measurable (X (realTimeClamp t)) :=
    (hX.adapted _ (half_real_time_finite t)).mono (B.le _) le_rfl
  haveI : IsProbabilityMeasure (P.map (X (realTimeClamp t))) :=
    (Measure.isProbabilityMeasure_map_iff hmX.aemeasurable).mpr inferInstance
  apply measure_eq_of_smooth_compact_tests
  intro f hf hs
  obtain ⟨K,hK⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨Lf,hLf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hf (by simp)
  obtain ⟨hqm,hqb,hCE⟩ := sde_initial_conditional_transition P B B L hL b σ hLip
    ξ hξ X hX Z hZ t ht f Lf hLf K hK
  rw [integral_map hmX.aemeasurable hf.continuous.aestronglyMeasurable]
  have hI := integral_condExp (B.le ⊥) (f := fun w => f (X (realTimeClamp t) w)) (μ := P)
  rw [integral_congr_ae hCE] at hI
  rw [←hI]
  have he := integral_map (μ := P) hmξ.aemeasurable hqm.aestronglyMeasurable
  rw [hξlaw] at he
  rw [←he]
  exact hinv t ht f hf hs

end Asakura.Chapter8

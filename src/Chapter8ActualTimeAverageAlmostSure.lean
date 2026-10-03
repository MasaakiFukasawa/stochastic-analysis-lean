import Chapter8ActualStationaryTimeAverage
import FullAuditTimeAverageCoupling

open MeasureTheory Set Filter
open scoped NNReal BigOperators Topology
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The continuous-time almost-sure conclusion for the actual stationary
SDE follows through the proved Borel-Cantelli and intervening-time argument. -/
theorem actual_stationary_time_average_ae {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E)
    (L : ℝ) (hL : 0≤L)
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(b i x-b i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π]
    (hπ : MemLp (fun x : Fin d → ℝ => x) 2 π)
    (ξ : Ω → Fin d → ℝ) (hξ : MemLp ξ 2 P) (hξlaw : P.map ξ=π)
    (X : HalfClosedTime → Ω → Fin d → ℝ) (hX : VectorSDESolution P B.F B.W b σ ξ X)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W b σ (fun _ => x) (Z x))
    (hinv : ∀ t : ℝ,0≤t → ∀ f : (Fin d → ℝ) → ℝ,
      ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      (∫ x,(∫ w,f (Z x (realTimeClamp t) w) ∂P) ∂π)=∫ x,f x ∂π)
    (κ : ℝ) (hκ : 0<κ)
    (hCon : ∀ t≥0,∀ x y,∀ᵐ w ∂P,
      ‖e (Z x (realTimeClamp t) w)-e (Z y (realTimeClamp t) w)‖≤
        Real.exp (-κ*t)*‖e x-e y‖)
    (f : E → ℝ) (Lf : ℝ≥0) (hf : LipschitzWith Lf f)
    (K : ℝ) (hK : ∀ x,‖f x‖≤K) :
    ∀ᵐ w ∂P,Tendsto (timeAverage (fun t => f (e (X (realTimeClamp (max 0 t)) w))))
      atTop (nhds (∫ x,f (e x) ∂π)) := by
  obtain ⟨hc,hm,_,_⟩ := sde_real_path_data P B L hL b σ hLip ξ hξ X hX
  apply bounded_time_average_ae_from_variance P
    (fun w t => f (e (X (realTimeClamp (max 0 t)) w)))
    (hf.continuous.measurable.comp (e.continuous.measurable.comp hm))
    (fun w => hf.continuous.comp (e.continuous.comp (hc w))) K
    (2*(Lf:ℝ)^2*(∫ x,‖e x‖^2 ∂π)/κ) (∫ x,f (e x) ∂π)
    ((norm_nonneg (f 0)).trans (hK 0))
    (fun w t => by simpa only [Real.norm_eq_abs] using hK (e (X (realTimeClamp (max 0 t)) w)))
  intro T hT
  have hh := actual_stationary_time_average P B e L hL b σ hLip π hπ ξ hξ hξlaw
    X hX Z hZ hinv κ T hκ hT hCon f Lf hf
  simpa only [div_mul_eq_div_div] using hh

end Asakura.Chapter8

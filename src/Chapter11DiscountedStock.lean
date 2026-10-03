import Chapter11WealthMoments
import Chapter4BrownianSystem
import Chapter4FinitePathLift

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter6
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The risk-neutral discounted stock is a true martingale, directly from
the actual Brownian bracket and the previously proved Novikov theorem. -/
theorem discounted_stock_true_martingale {Ω : Type*} [m : MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (B : BrownianSystem Q 1)
    (σ R : ℝ) (hR : 0≤R) :
    let E := fun t w => Real.exp (σ*B.W 0 (min (realTimeClamp R) t) w-
      σ^2*B.C 0 0 (min (realTimeClamp R) t) w/2)
    (∀ t,Integrable (E t) Q) ∧
    (∀ s t,s≤t → Q[E t|B.F s]=ᵐ[Q] E s) ∧
    (∫ w,E ⊤ w ∂Q)=1 ∧
    ((fun w => E ⊤ w)=(fun w => Real.exp (σ*B.W 0 (realTimeClamp R) w-σ^2*R/2))) := by
  have hτ t : MeasurableSet[B.F t] {w : Ω | realTimeClamp (T:=(⊤:EReal)) R≤t} := by
    by_cases h : realTimeClamp (T:=(⊤:EReal)) R≤t <;> simp [h]
  have hi : Integrable (fun w => Real.exp (1*(σ^2*B.C 0 0 (realTimeClamp R) w))) Q := by
    have he : (fun w => Real.exp (1*(σ^2*B.C 0 0 (realTimeClamp R) w)))=(fun _ => Real.exp (σ^2*R)) := by
      funext w
      simp only [B.clock 0 0 w R hR,ite_true,one_mul]
    rw [he]
    exact integrable_const _
  obtain ⟨hi,hm,he,_⟩ := novikov_written Q (by simp) B.F B.mono B.le B.null
    (fun t w => σ*B.W 0 t w) (fun t w => σ^2*B.C 0 0 t w) ((B.martingale 0).smul Q B.F σ)
    (scaled_self_covariance Q B.F (B.W 0) (B.C 0 0) (B.cov 0 0) σ)
    (fun _ => realTimeClamp R) hτ (fun _ => real_time_below R hR (EReal.coe_lt_top R)) 1 (by norm_num) hi
  refine ⟨hi,hm,he,?_⟩
  funext w
  simp only [min_top_right,B.clock 0 0 w R hR,ite_true]

end Asakura.Chapter11

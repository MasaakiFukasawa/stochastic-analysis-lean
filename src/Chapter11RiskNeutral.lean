import Chapter6BoundedGirsanov
import Chapter4BlackScholesConstructed

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Construct the risk-neutral measure from the actual Brownian motion.
Stopping the deterministic drift after maturity gives a Brownian driver on
the original half-line without imposing any market assumptions after T. -/
theorem black_scholes_risk_neutral_driver {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (μ r σ T : ℝ) (hT : 0≤T) :
    ∃ (Q : Measure Ω) (hQ : IsProbabilityMeasure Q),
      (∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w) ∧
      ∃ BQ : BrownianSystem Q 1,BQ.F=B.F ∧
        ∀ t,0≤t → BQ.W 0 (realTimeClamp t)=ᵐ[Q]
          fun w => B.W 0 (realTimeClamp t) w+((μ-r)/σ)*min T t := by
  let θ := (μ-r)/σ
  obtain ⟨Q,hQ,ha,BQ,hF,he⟩ := bounded_progressive_girsanov P B
    (fun _ _ => -θ) (fun _ => measurable_const) (fun _ _ _ => measurable_const)
    |θ| (abs_nonneg θ) (fun _ _ => by simp only [abs_neg];exact le_rfl) T hT
  refine ⟨Q,hQ,ha,BQ,hF,?_⟩
  intro t ht
  filter_upwards [he 0 t ht] with w hw
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_neg,sub_neg_eq_add,mul_comm] using hw

/-- The same explicit stock path has drift r in the changed Brownian
coordinate. In particular its discounted path is the standard exponential. -/
theorem black_scholes_discounted_path (s μ r σ t w : ℝ) (hσ : σ≠0) :
    (s*Real.exp ((μ-σ^2/2)*t+σ*w))/Real.exp (r*t)=
      s*Real.exp (σ*(w+((μ-r)/σ)*t)-σ^2*t/2) := by
  rw [mul_div_assoc,←Real.exp_sub]
  congr 2
  field_simp
  ring

end Asakura.Chapter11

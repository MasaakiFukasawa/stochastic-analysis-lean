import Chapter11Forward
import Chapter11ConstantIntegral
import Chapter4BrownianSystem

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The forward exercise is connected to the constructed stock SDE.
The bank-account holding is the constant -K exp(-r T); both drift terms
and the actual stock Ito integral are present in the wealth identity. -/
theorem forward_strategy_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (s μ σ r K T : ℝ) :
    ∃ N : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => σ*geometricFlow s μ σ ![B.C 0 0 (realTimeClamp z.2) z.1,B.W 0 (realTimeClamp z.2) z.1]) N ∧
      ∀ᵐ w ∂P,∀ t : ℝ,0≤t →
        geometricFlow s μ σ ![t,B.W 0 (realTimeClamp t) w]-K*Real.exp (-r*(T-t))=
          (s-K*Real.exp (-r*T))+
            (∫ u in 0..t,μ*geometricFlow s μ σ ![u,B.W 0 (realTimeClamp u) w])+N (realTimeClamp t) w+
            (∫ u in 0..t,(-K*Real.exp (-r*T))*r*Real.exp (r*u)) := by
  obtain ⟨N,hN,hNI,hS⟩ := geometric_sde_global P (T:=(⊤:EReal)) (by simp)
    B.F B.mono B.le B.null (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0)
    (fun w t ht _ => B.diagonal_clock 0 w t ht) s μ σ
  refine ⟨N,hN,hNI,?_⟩
  filter_upwards [hS] with w hw
  intro t ht
  have hsde := hw t ht (EReal.coe_lt_top t)
  have hf := forward_wealth_identity (fun u => geometricFlow s μ σ ![u,B.W 0 (realTimeClamp u) w])
    (fun u => N (realTimeClamp u) w) s μ r K T t hsde
  dsimp only at hf
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hb := exponential_weight_integral r t
  rw [hf]
  congr 1
  rw [show Real.exp (r*t)-1=r*(∫ u in 0..t,Real.exp (r*u)) by linarith]
  ring

/-- The discounted forward wealth has a deterministic lower bound,
so its potentially negative payoff causes no admissibility problem. -/
theorem forward_discounted_lower_bound (S r K T : ℝ) (hS : 0≤S) :
    -|K*Real.exp (-r*T)| ≤ S-K*Real.exp (-r*T) := by
  have hh := le_abs_self (K*Real.exp (-r*T))
  linarith

/-- Positivity needed above holds for the actual geometric stock path. -/
theorem forward_stock_positive (s μ σ t w : ℝ) (hs : 0<s) :
    0<geometricFlow s μ σ ![t,w] := by
  dsimp only [geometricFlow,Matrix.cons_val_zero,Matrix.cons_val_one]
  positivity

end Asakura.Chapter11

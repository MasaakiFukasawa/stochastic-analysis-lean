import Chapter4ExponentialWeight
import Chapter4GeometricGlobal

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.Chapter4
set_option maxHeartbeats 1400000

/-- The forward hedge uses one share and a constant number of bank-account
units; the displayed bank balance is consequently time dependent. -/
theorem forward_wealth_identity (S N : ℝ → ℝ) (s μ r K T t : ℝ)
    (hS : S t=s+μ*(∫ u in 0..t,S u)+N t) :
    let η := -K*Real.exp (-r*T)
    S t-K*Real.exp (-r*(T-t))=
      (s-K*Real.exp (-r*T))+μ*(∫ u in 0..t,S u)+N t+
        η*(Real.exp (r*t)-1) := by
  dsimp only
  have he : Real.exp (-r*(T-t))=Real.exp (-r*T)*Real.exp (r*t) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he,hS]
  ring

theorem forward_terminal_payoff (s K r T : ℝ) : s-K*Real.exp (-r*(T-T))=s-K := by simp

theorem forward_zero_initial (s K r T : ℝ) :
    s-K*Real.exp (-r*T)=0 ↔ K=s*Real.exp (r*T) := by
  have he : Real.exp (-r*T)*Real.exp (r*T)=1 := by
    rw [←Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  constructor
  · intro h
    have hh := congrArg (fun z => z*Real.exp (r*T)) h
    linear_combination -hh-K*he
  · intro h
    rw [h]
    linear_combination -s*he

end Asakura.Chapter11

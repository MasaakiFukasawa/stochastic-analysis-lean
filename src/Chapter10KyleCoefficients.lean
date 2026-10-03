import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace Asakura.Chapter10

/-- All coefficient identities used in the equilibrium construction, including
strict positivity before maturity and the unconditional expected profit. -/
theorem kyle_equilibrium_coefficients (S σ T t : ℝ)
    (hS : 0<S) (hσ : 0<σ) (hT : 0<T) (ht : t<T) :
    let l := Real.sqrt S / (σ * Real.sqrt T)
    let v := S*(T-t)/T
    let b := 1/(l*(T-t))
    0<l ∧ 0<v ∧ 0<b ∧ b*v=l*σ^2 ∧
      l^2*σ^2*T=S ∧ S/(2*l)+l*σ^2*T/2=σ*Real.sqrt (S*T) ∧
      b*v=S/(l*T) := by
  dsimp only
  have hs : 0<Real.sqrt S := Real.sqrt_pos.mpr hS
  have hrt : 0<Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsqS := Real.sq_sqrt hS.le
  have hsqT := Real.sq_sqrt hT.le
  have hl : 0<Real.sqrt S/(σ*Real.sqrt T) := div_pos hs (mul_pos hσ hrt)
  refine ⟨hl, div_pos (mul_pos hS (sub_pos.mpr ht)) hT,
    one_div_pos.mpr (mul_pos hl (sub_pos.mpr ht)), ?_, ?_, ?_, ?_⟩
  · field_simp [hs.ne', hrt.ne', hσ.ne', hT.ne', (sub_pos.mpr ht).ne']
    nlinarith [hsqS,hsqT]
  · field_simp [hs.ne', hrt.ne', hσ.ne', hT.ne', (sub_pos.mpr ht).ne']
    nlinarith [hsqS,hsqT]
  · rw [Real.sqrt_mul hS.le]
    field_simp [hs.ne', hrt.ne', hσ.ne', hT.ne', (sub_pos.mpr ht).ne']
    nlinarith [hsqS,hsqT]
  · field_simp [hs.ne', hrt.ne', hσ.ne', hT.ne', (sub_pos.mpr ht).ne']

/-- For a varying asset value the Riccati identity reduces to the stated
balance of incoming variance and variance removed by observation. -/
theorem kyle_varying_variance (b v l σ γ : ℝ) (hσ : σ≠0)
    (hgain : b*v=l*σ^2) :
    γ^2-b^2*v^2/σ^2=γ^2-l^2*σ^2 := by
  have hsq := congrArg (fun x : ℝ => x^2) hgain
  field_simp
  nlinarith [hsq]

end Asakura.Chapter10

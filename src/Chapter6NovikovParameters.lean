import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Asakura.Chapter6

/-- The two Holder/Doob exponents used in the printed Novikov proof exist
for every strict exponential-moment margin gamma > 1/2. -/
theorem novikov_exponents (γ : ℝ) (hγ : 1/2 < γ) :
    ∃ α p : ℝ,1 < α ∧ α/2 < γ ∧ 1 < p ∧
      γ = p*((α*p-1)/(α-1))*(α/2) := by
  let α := γ+1/2
  have ha : 1 < α := by dsimp [α]; linarith
  have hag : α/2 < γ := by dsimp [α]; linarith
  let d := Real.sqrt (1+8*γ*(α-1))
  have hg : 0 < γ := by linarith
  have hrad : 0 ≤ 1+8*γ*(α-1) := by positivity
  have hd : d^2 = 1+8*γ*(α-1) := Real.sq_sqrt hrad
  have hdpos : 0 ≤ d := Real.sqrt_nonneg _
  have hgap : 0 < (2*γ-α)*(α-1) := mul_pos (by linarith) (by linarith)
  have hdl : 2*α-1 < d := by nlinarith
  let p := (1+d)/(2*α)
  have hp : 1 < p := by
    dsimp [p]
    apply (lt_div_iff₀ (by linarith : 0 < 2*α)).mpr
    linarith
  refine ⟨α,p,ha,hag,hp,?_⟩
  dsimp [p]
  field_simp [ne_of_gt (show 0 < α by linarith),ne_of_gt (show 0 < α-1 by linarith)]
  nlinarith

/-- The precise factorization to which Holder is applied; all coefficients
are checked before the probabilistic estimates. -/
theorem novikov_exponent_split (α p z c : ℝ) (ha : α ≠ 0)
    (hα : α ≠ 1) (γ : ℝ) (hg : γ = p*((α*p-1)/(α-1))*(α/2)) :
    p*(z-c/2) = (α*p*z-(α*p)^2*c/2)/α + γ*c*((α-1)/α) := by
  rw [hg]
  field_simp [ha,sub_ne_zero.mpr hα]
  ring

end Asakura.Chapter6

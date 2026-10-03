import Chapter3WrittenObstructions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Written

/-- The singular bracket energy in the p<2 argument IS integrable: its
exponent is greater than -1. This does not itself construct the stochastic integral. -/
theorem singular_energy_integrable {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun s : ℝ => s ^ ((p-2)/2)) (Ioo 0 q) := by
  apply (intervalIntegral.integrableOn_Ioo_rpow_iff hq).mpr
  linarith

/-- The energy identity after adding epsilon to the bracket. This is an
ordinary integral in the bracket variable; the Stieltjes substitution is a
separate manuscript step. -/
theorem regularized_energy {p ε q : ℝ} (hp : 0 < p) :
    (∫ s in ε..(ε+q), s ^ (p/2-1)) =
      (2/p)*((ε+q)^(p/2)-ε^(p/2)) := by
  rw [integral_rpow (Or.inl (by linarith : -1 < p/2-1))]
  have he : p/2-1+1 = p/2 := by ring
  rw [he]
  ring

/-- Regularization repairs the inverse-weight cancellation everywhere,
including times when the original bracket is zero. -/
theorem regularized_inverse_weights {ε q p : ℝ} (hε : 0 < ε) (hq : 0 ≤ q) :
    (ε+q)^((2-p)/4) * (ε+q)^((p-2)/4) = 1 := by
  rw [← Real.rpow_add (by linarith : 0 < ε+q)]
  have he : (2-p)/4+(p-2)/4 = 0 := by ring
  rw [he, Real.rpow_zero]

/-- Exact lower-endpoint term in the second p<2 estimate, which the
manuscript omitted while printing an equality. A and B denote the endpoint powers. -/
theorem bdg_endpoint_identity {p A B : ℝ} (hp : 0 < p) :
    B + (1-p/2)*(2/p)*(B-A) = (2/p)*B - (2/p-1)*A := by
  field_simp
  ring

/-- The inequality needed by the proof survives the omitted endpoint term. -/
theorem bdg_endpoint_upper_bound {p A B : ℝ} (hp : 0 < p) (hp2 : p < 2)
    (hA : 0 ≤ A) : B + (1-p/2)*(2/p)*(B-A) ≤ (2/p)*B := by
  rw [bdg_endpoint_identity hp]
  have hc : 0 ≤ 2/p-1 := by
    have : 1 ≤ 2/p := (le_div_iff₀ hp).mpr (by linarith)
    linarith
  nlinarith [mul_nonneg hc hA]

/-- Ordinary integration by parts yields the factor 2 in both BDG arguments;
K is the running maximum, v the final increasing weight and v0 its initial value. -/
theorem increasing_weight_bound {Y Xv R K v v0 : ℝ}
    (he : Y = Xv-R) (hK : 0 ≤ K) (hv0 : 0 ≤ v0)
    (hX : |Xv| ≤ K*v) (hR : |R| ≤ K*(v-v0)) : |Y| ≤ 2*K*v := by
  rw [he]
  have ht : |Xv-R| ≤ |Xv|+|R| := by
    simpa [sub_eq_add_neg] using abs_add_le Xv (-R)
  nlinarith [mul_nonneg hK hv0]

end Asakura.Chapter3Written

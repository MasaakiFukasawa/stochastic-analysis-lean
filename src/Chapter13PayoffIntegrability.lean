import Chapter13BondAlgebra
import Chapter13PricingBayes

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 1200000

theorem discounted_positive_payoff_integrable {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) (p q:Ω → ℝ) (hp:Integrable p P) (hq:Integrable q P) (K:ℝ) :
    Integrable (fun w => max (p w-K*q w) 0) P := by
  exact (hp.sub (hq.const_mul K)).sup (integrable_zero _ _ _)

theorem discounted_caplet_algebra (Bprev BT K:ℝ) (hB:0<BT) :
    BT⁻¹*max (BT/Bprev-K) 0=max (Bprev⁻¹-K*BT⁻¹) 0 := by
  rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr hB.le)]
  congr 1
  · field_simp
  · ring

theorem logarithmic_bond_telescope (p:ℕ → ℝ) (hp:∀i,0<p i) (n:ℕ) :
    Real.log (p n/p 0)= -∑i∈Finset.range n,Real.log (p i/p (i+1)) := by
  have he:=bond_ratio_telescope p (fun i => (hp i).ne') n
  have hlog:=congrArg Real.log he
  rw [Real.log_prod (fun i _ => div_ne_zero (hp i).ne' (hp (i+1)).ne')] at hlog
  rw [hlog,Real.log_div (hp n).ne' (hp 0).ne',Real.log_div (hp 0).ne' (hp n).ne']
  ring

theorem shifted_rate_log_derivative (δ R:ℝ) (hδ:0<δ) (hp:0<1+δ*R) :
    HasDerivAt (fun x => Real.log (1+δ*x)) ((R+1/δ)⁻¹) R := by
  have h:HasDerivAt (fun x => Real.log (1+δ*x)) (δ/(1+δ*R)) R := by
    simpa using ((hasDerivAt_const R 1).add ((hasDerivAt_id R).const_mul δ)).log hp.ne'
  convert h using 1
  field_simp
  ring
end Asakura.Chapter13
#print axioms Asakura.Chapter13.discounted_positive_payoff_integrable
#print axioms Asakura.Chapter13.discounted_caplet_algebra
#print axioms Asakura.Chapter13.logarithmic_bond_telescope
#print axioms Asakura.Chapter13.shifted_rate_log_derivative

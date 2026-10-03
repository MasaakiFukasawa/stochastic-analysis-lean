import Chapter10KyleVarianceIdentification

open Set Filter
open scoped Topology
namespace Asakura.Chapter10
set_option maxHeartbeats 2200000

/-- The actual filtering variance for the proposed equilibrium is the
displayed linear function on every compact interval before T. The singular
feedback is required to be continuous only before T. -/
theorem kyle_actual_equilibrium_variance (S : ℝ → ℝ) (S0 σ T R : ℝ)
    (hS0 : 0<S0) (hσ : 0<σ) (hT : 0<T) (hR : 0≤R) (hRT : R<T)
    (hS : ContinuousOn S (Icc 0 R)) (hinit : S 0=S0)
    (hd : ∀ t∈Ico 0 R,HasDerivWithinAt S
      (-(1/((Real.sqrt S0/(σ*Real.sqrt T))*(T-t)))^2*(S t)^2/σ^2) (Ici t) t) :
    ∀ t∈Icc 0 R,S t=S0*(T-t)/T ∧
      (1/((Real.sqrt S0/(σ*Real.sqrt T))*(T-t)))*(S t)/σ^2=
        Real.sqrt S0/(σ*Real.sqrt T) := by
  let l := Real.sqrt S0/(σ*Real.sqrt T)
  have hl : 0<l := (kyle_equilibrium_coefficients S0 σ T 0 hS0 hσ hT hT).1
  have hb : ContinuousOn (fun t => 1/(l*(T-t))) (Icc 0 R) := by
    apply continuousOn_const.div (continuousOn_const.mul (continuousOn_const.sub continuousOn_id))
    intro t ht
    exact mul_ne_zero hl.ne' (sub_pos.mpr (ht.2.trans_lt hRT)).ne'
  have hv : ContinuousOn (fun t => S0*(T-t)/T) (Icc 0 R) := by fun_prop
  have he := scalar_filter_variance_unique S (fun t => S0*(T-t)/T)
    (fun t => 1/(l*(T-t))) σ R hR hS hv hb (by simp [hinit,hT.ne']) hd (by
      intro t ht
      exact (kyle_equilibrium_variance_equation S0 σ T t hS0 hσ hT (ht.2.trans hRT)).hasDerivWithinAt)
  intro t ht
  refine ⟨he t ht,?_⟩
  rw [he t ht]
  have hg := (kyle_equilibrium_coefficients S0 σ T t hS0 hσ hT (ht.2.trans_lt hRT)).2.2.2.1
  change (1/(l*(T-t)))*(S0*(T-t)/T)=l*σ^2 at hg
  change (1/(l*(T-t)))*(S0*(T-t)/T)/σ^2=l
  rw [hg]
  exact mul_div_cancel_right₀ l (pow_ne_zero 2 hσ.ne')

end Asakura.Chapter10

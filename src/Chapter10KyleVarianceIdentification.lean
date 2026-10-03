import Chapter10MeanODEZero
import Chapter10KyleCoefficients

open Set Filter
open scoped Topology
namespace Asakura.Chapter10
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Uniqueness of the actual scalar filtering variance on each compact
preterminal interval; no rational-pricing assumption is used. -/
theorem scalar_filter_variance_unique (S V b : ℝ → ℝ) (σ R : ℝ) (hR : 0≤R)
    (hS : ContinuousOn S (Icc 0 R)) (hV : ContinuousOn V (Icc 0 R))
    (hb : ContinuousOn b (Icc 0 R)) (h0 : S 0=V 0)
    (hdS : ∀ t∈Ico 0 R,HasDerivWithinAt S (-(b t)^2*(S t)^2/σ^2) (Ici t) t)
    (hdV : ∀ t∈Ico 0 R,HasDerivWithinAt V (-(b t)^2*(V t)^2/σ^2) (Ici t) t) :
    ∀ t∈Icc 0 R,S t=V t := by
  let e := fun t => S t-V t
  let a := fun t => -(b t)^2*(S t+V t)/σ^2
  have hac : ContinuousOn a (Icc 0 R) := ((hb.pow 2).neg.mul (hS.add hV)).div_const _
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hac
  have hed : ∀ t∈Ico 0 R,HasDerivWithinAt e (a t*e t) (Ici t) t := by
    intro t ht
    convert (hdS t ht).sub (hdV t ht) using 1
    dsimp only [a,e]
    ring
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := e) (f' := fun t => a t*e t) (K := K) (hS.sub hV) hed
    (show e 0=0 by simp [e,h0]) (by
      intro t ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hK t ⟨ht.1,ht.2.le⟩) (norm_nonneg _))
  exact fun t ht => sub_eq_zero.mp (hz t ht)

/-- The displayed linear variance solves the nonlinear filtering Riccati
equation for the displayed feedback, not just its rational-price reduction. -/
theorem kyle_equilibrium_variance_equation (S0 σ T t : ℝ)
    (hS : 0<S0) (hσ : 0<σ) (hT : 0<T) (ht : t<T) :
    let l := Real.sqrt S0/(σ*Real.sqrt T)
    let b := 1/(l*(T-t))
    HasDerivAt (fun s => S0*(T-s)/T) (-b^2*(S0*(T-t)/T)^2/σ^2) t := by
  intro l b
  have hcoeff := kyle_equilibrium_coefficients S0 σ T t hS hσ hT ht
  change 0<l ∧ _ at hcoeff
  have hgain : b*(S0*(T-t)/T)=l*σ^2 := hcoeff.2.2.2.1
  have henergy : l^2*σ^2*T=S0 := hcoeff.2.2.2.2.1
  have hd := (((hasDerivAt_const t T).sub (hasDerivAt_id t)).const_mul S0).div_const T
  have he : -b^2*(S0*(T-t)/T)^2/σ^2= -l^2*σ^2 := by
    have hh := kyle_varying_variance b (S0*(T-t)/T) l σ 0 hσ.ne' hgain
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),zero_sub] at hh
    calc
      _ = -(b^2*(S0*(T-t)/T)^2/σ^2) := by ring
      _ = -(l^2*σ^2) := hh
      _ = _ := by ring
  convert hd using 1
  · rfl
  · rw [he]
    field_simp
    nlinarith [henergy]

end Asakura.Chapter10

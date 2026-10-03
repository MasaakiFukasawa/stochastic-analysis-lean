import Chapter11HeatToBlackScholes
import Chapter11HeatGaussianRepresentation

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace Asakura.Chapter11
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

noncomputable def logPayoff (h : Ioi (0:ℝ) → ℝ) (z : ℝ) : ℝ := h ⟨Real.exp z,Real.exp_pos z⟩
noncomputable def europeanHeatPrice (h : Ioi (0:ℝ) → ℝ) (r σ θ x : ℝ) : ℝ :=
  heatPrice (fun q => ∫ z,logPayoff h z*heatLogKernel z q) r σ θ x

theorem log_payoff_regular (h : Ioi (0:ℝ) → ℝ) (hh : Continuous h)
    (hn : ∀ x,0≤h x) (C m : ℝ) (hb : ∀ x,h x≤C*(1+x.val^m)) :
    Continuous (logPayoff h) ∧ (∀ z,0≤logPayoff h z) ∧
      ∀ z,logPayoff h z≤C*(1+Real.exp (m*z)) := by
  refine ⟨hh.comp (Real.continuous_exp.subtype_mk _),fun z => hn _,?_⟩
  intro z
  have he := hb ⟨Real.exp z,Real.exp_pos z⟩
  simpa only [logPayoff,←Real.exp_mul,mul_comm z m] using he

/-- The heat construction is exactly the Gaussian price displayed in the
text, on positive stock prices. -/
theorem european_heat_gaussian_price (h : Ioi (0:ℝ) → ℝ) (hh : Continuous h)
    (r σ θ x : ℝ) (hσ : 0<σ) (hθ : 0<θ) (hx : 0<x) :
    europeanHeatPrice h r σ θ x=Real.exp (-r*θ)*
      (∫ z,h ⟨x*Real.exp ((r-σ^2/2)*θ+σ*Real.sqrt θ*z),mul_pos hx (Real.exp_pos _)⟩ ∂gaussianReal 0 1) := by
  have hm : Measurable (logPayoff h) := (hh.comp (Real.continuous_exp.subtype_mk _)).measurable
  dsimp only [europeanHeatPrice,heatPrice]
  rw [heat_gaussian_representation _ hm _ _ (mul_pos (sq_pos_of_pos hσ) hθ)]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only [logPayoff]
  congr 1
  apply Subtype.ext
  simp only [Real.sqrt_mul (sq_nonneg σ),Real.sqrt_sq_eq_abs,abs_of_pos hσ]
  rw [add_assoc,Real.exp_add,Real.exp_log hx]

theorem european_price_smooth_and_pde (h : Ioi (0:ℝ) → ℝ) (hh : Continuous h)
    (hn : ∀ x,0≤h x) (C m : ℝ) (hC : 0≤C) (hb : ∀ x,h x≤C*(1+x.val^m))
    (r σ T t x : ℝ) (hσ : 0<σ) (ht : t<T) (hx : 0<x) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => europeanHeatPrice h r σ q.1 q.2) (T-t,x) ∧
      deriv (fun s => europeanHeatPrice h r σ (T-s) x) t+
        r*x*deriv (europeanHeatPrice h r σ (T-t)) x+
        σ^2*x^2/2*deriv (deriv (europeanHeatPrice h r σ (T-t))) x-r*europeanHeatPrice h r σ (T-t) x=0 := by
  obtain ⟨hfc,hfn,hfb⟩ := log_payoff_regular h hh hn C m hb
  have hs := exponential_payoff_heat_smooth (logPayoff h) hfc.measurable hfn C m hC hfb
  have hp a y (ha : 0<a) := (exponential_payoff_heat_equation (logPayoff h) hfc.measurable hfn C m hC hfb a y ha).deriv
  exact ⟨heat_price_joint_smooth _ hs r σ (T-t) x hσ.ne' (sub_pos.mpr ht) hx,
    heat_price_backward_equation _ hs hp r σ T t x hσ.ne' ht hx⟩

end Asakura.Chapter11

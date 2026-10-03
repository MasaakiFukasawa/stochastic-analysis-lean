import Chapter11EuropeanIto
import Chapter11EuropeanConditional
import Chapter11EuropeanTerminal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- Identification of the constructed heat price with conditional
expectation of the actual terminal payoff. -/
theorem european_price_conditional_identification {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (h : Ioi (0:ℝ) → ℝ) (hh : Continuous h) (C m : ℝ)
    (hb : ∀ x,‖h x‖≤C*(1+x.val^m))
    (s r σ T t : ℝ) (hs : 0<s) (hσ : 0<σ) (ht : 0≤t) (htT : t<T) :
    let U := fun w => Real.exp (-r*T)*h ⟨s*Real.exp ((r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w),mul_pos hs (Real.exp_pos _)⟩
    P[U|B.F (realTimeClamp t)]=ᵐ[P]
      fun w => europeanBrownianPrice h s r σ T ![t,B.W 0 (realTimeClamp t) w] := by
  let f := logPayoff h
  have hf : Measurable f := (hh.comp (Real.continuous_exp.subtype_mk _)).measurable
  have hT : 0<T := ht.trans_lt htT
  have h2 := european_actual_terminal_L2 P B h hh C m hb s (r-σ^2/2) σ T hs hT
  have he w : f (Real.log s+(r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w)=
      h ⟨s*Real.exp ((r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w),mul_pos hs (Real.exp_pos _)⟩ := by
    dsimp only [f,logPayoff]
    congr 1
    apply Subtype.ext
    change Real.exp (Real.log s+(r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w)=s*Real.exp ((r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w)
    rw [add_assoc,Real.exp_add,Real.exp_log hs]
  have hi : Integrable (fun w => f (Real.log s+(r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w)) P := by
    simpa only [he] using h2.integrable (by norm_num)
  have hc := brownian_log_payoff_conditional P B f hf (Real.log s) (r-σ^2/2) σ T t ht htT.le hi
  have hd := condExp_smul (μ:=P) (Real.exp (-r*T)) (fun w => f (Real.log s+(r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w)) (B.F (realTimeClamp t))
  simp only [Pi.smul_def,smul_eq_mul,he] at hd
  filter_upwards [hc,hd] with w hw hdw
  rw [hdw]
  rw [show P[(fun w => h ⟨s*Real.exp ((r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w),mul_pos hs (Real.exp_pos _)⟩)|B.F (realTimeClamp t)] w=
      P[(fun w => f (Real.log s+(r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w))|B.F (realTimeClamp t)] w by simp only [he],hw]
  dsimp only [europeanBrownianPrice,brownianHeatPrice,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [heat_gaussian_representation _ hf _ _ (mul_pos (sq_pos_of_pos hσ) (sub_pos.mpr htT))]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro z
  simp only [Real.sqrt_mul (sq_nonneg σ),Real.sqrt_sq_eq_abs,abs_of_pos hσ]
  change f _=f _
  congr 1
  ring

end Asakura.Chapter11

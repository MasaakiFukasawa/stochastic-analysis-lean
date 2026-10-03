import Chapter11IndependentAverage
import Chapter4BrownianSystem
import Chapter4LevyConstructed
import Chapter11EuropeanEndpoint

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Conditional Gaussian pricing, derived from the actual Brownian driver.
Only terminal integrability is used, not boundedness of the payoff. -/
theorem brownian_log_payoff_conditional {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (f : ℝ → ℝ) (hf : Measurable f) (y a σ R s : ℝ) (hs : 0≤s) (hsR : s≤R)
    (hi : Integrable (fun w => f (y+a*R+σ*B.W 0 (realTimeClamp R) w)) P) :
    P[(fun w => f (y+a*R+σ*B.W 0 (realTimeClamp R) w))|B.F (realTimeClamp s)]=ᵐ[P]
      fun w => ∫ z,f (y+a*s+σ*B.W 0 (realTimeClamp s) w+a*(R-s)+σ*Real.sqrt (R-s)*z) ∂gaussianReal 0 1 := by
  have hR := hs.trans hsR
  obtain ⟨hlaw,hind⟩ := levy_gaussian_increment_constructed P (T:=(⊤:EReal)) (by simp)
    B.F B.mono B.le B.null (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0)
    (fun w t ht _ => B.diagonal_clock 0 w t ht) R hR (EReal.coe_lt_top R) s ⟨hs,hsR⟩
  let X := fun w => y+a*s+σ*B.W 0 (realTimeClamp s) w
  let Y := fun w => B.W 0 (realTimeClamp R) w-B.W 0 (realTimeClamp s) w
  let g := fun z : ℝ × ℝ => f (z.1+a*(R-s)+σ*z.2)
  have hst : realTimeClamp (T:=(⊤:EReal)) s<⊤ := by
    change (realTimeClamp s:EReal)<⊤
    rw [real_time_clamp_eq s hs le_top]
    exact EReal.coe_lt_top s
  have hRt : realTimeClamp (T:=(⊤:EReal)) R<⊤ := by
    change (realTimeClamp R:EReal)<⊤
    rw [real_time_clamp_eq R hR le_top]
    exact EReal.coe_lt_top R
  have hX : Measurable[B.F (realTimeClamp s)] X :=
    measurable_const.add ((B.martingale 0).adapted P B.F _ hst |>.const_mul σ)
  have hY : Measurable Y := ((B.martingale 0).adapted P B.F _ hRt |>.mono (B.le _) le_rfl).sub
    ((B.martingale 0).adapted P B.F _ hst |>.mono (B.le _) le_rfl)
  have hg : Measurable g := hf.comp ((measurable_fst.add_const _).add (measurable_snd.const_mul _))
  have he : (fun w => g (X w,Y w))=(fun w => f (y+a*R+σ*B.W 0 (realTimeClamp R) w)) := by
    funext w
    dsimp only [g,X,Y]
    congr 1
    ring
  have hgi : Integrable (fun w => g (X w,Y w)) P := by rw [he];exact hi
  have hc := conditional_independent_integrable_average (B.F (realTimeClamp s)) P (B.le _) X Y hX hY hind.symm g hg hgi
  rw [he] at hc
  have hm : (gaussianReal 0 1).map (fun z => Real.sqrt (R-s)*z)=gaussianReal 0 (NNReal.mk (R-s) (sub_nonneg.mpr hsR)) := by
    have hh := gaussianReal_map_const_mul (μ:=0) (v:=1) (Real.sqrt (R-s))
    simpa only [mul_zero,mul_one,Real.sq_sqrt (sub_nonneg.mpr hsR)] using hh
  have hmap : P.map Y=gaussianReal 0 (NNReal.mk (R-s) (sub_nonneg.mpr hsR)) := hlaw.map_eq
  filter_upwards [hc] with w hw
  rw [hw,hmap,←hm]
  have hfm : AEStronglyMeasurable (fun z => g (X w,z)) ((gaussianReal 0 1).map (fun z => Real.sqrt (R-s)*z)) :=
    (hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  rw [integral_map (by fun_prop) hfm]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only [g,X]
  congr 1
  ring

end Asakura.Chapter11

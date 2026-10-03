import Chapter11WealthJoint
import Chapter11OpenHarmonicIto
import Chapter5TimeSpaceIntegrand
import Chapter2ContinuousIntegrand

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The preterminal delta integrand is progressive and locally square
integrable, even if the terminal payoff is only continuous. -/
theorem open_price_gradient_regularity {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (R T : ℝ) (hR : 0≤R) (hRT : R<T)
    (v : (Fin 2 → ℝ) → ℝ) (hv : ContDiffOn ℝ 2 v {q | q 0<T}) :
    let G := fun z : Ω × ℝ => fderiv ℝ v
      ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)
    Measurable G ∧
      (∀ d,0<d → @Measurable _ _
        (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) d => G (z.1,z.2.val))) ∧
      (∀ d,0<d → ∀ w,IntervalIntegrable (fun r => (G (w,r))^2) volume 0 d) := by
  dsimp only
  obtain ⟨g,hg,he⟩ := time_strip_C2_extension R {q : Fin 2 → ℝ | q 0<T}
    (isOpen_lt (continuous_apply 0) continuous_const)
    (fun q hq => lt_of_le_of_lt hq.2 hRT) v hv
  have heq : (fun z : Ω × ℝ => fderiv ℝ g
      ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1))=
    (fun z => fderiv ℝ v
      ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) := by
    funext z
    have hh := he ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,B.W 0 (realTimeClamp z.2) z.1]
      (by simpa using (finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).property)
    exact congrArg (fun L => L (Pi.single 1 1)) hh.2.1
  have hev (w : Ω) (r : ℝ) : fderiv ℝ g ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp r)).val,B.W 0 (realTimeClamp r) w] (Pi.single 1 1)=
      fderiv ℝ v ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp r)).val,B.W 0 (realTimeClamp r) w] (Pi.single 1 1) := congrFun heq (w,r)
  simp_rw [←hev]
  obtain ⟨hm,ha,hc⟩ := time_space_integrand_regularity P B.F (B.W 0) (fun _ _ => 0) (B.W 0)
    (local_martingale_semimartingale_decomposition P (T:=(⊤:EReal)) (by simp) B.F B.mono (B.W 0) (B.martingale 0)) R hR
    (fun q => fderiv ℝ g q (Pi.single 1 1)) ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hj : Measurable (fun z : Ω × ℝ => fderiv ℝ g
      ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) := by
    apply ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).measurable.comp
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · exact (continuous_subtype_val.comp ((finite_prefix_time_continuous R hR).comp real_time_clamp_continuous)).measurable.comp measurable_snd
    · exact half_local_joint_measurable P B.F B.le (B.W 0) (B.martingale 0)
  refine ⟨hj,?_,?_⟩
  · intro d hd
    exact continuous_adapted_real_progressive B.F B.mono
      (fun z : Ω × ℝ => fderiv ℝ g ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) d hd.le
      (fun r hr => ha r hr.1 (EReal.coe_lt_top r)) (hc d hd.le (EReal.coe_lt_top d))
  · intro d hd w
    exact ((hc d hd.le (EReal.coe_lt_top d) w).pow 2).intervalIntegrable_of_Icc hd.le

end Asakura.Chapter11

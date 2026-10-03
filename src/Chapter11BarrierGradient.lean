import Chapter11StoppedGradientEnergy
import Chapter11EuropeanTerminalEnergy
import Chapter11FiniteIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

noncomputable def barrierGradient {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 : ℝ) (z : Ω × ℝ) : ℝ :=
  (Ioc (⊥ : HalfClosedTime) (upperBarrierHit (fun s => barrierLogStock P B y0 r σ s z.1))).indicator
    (fun _ => fderiv ℝ (barrierBrownianPrice b K r σ T y0)
      ![z.2,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) (realTimeClamp z.2)

theorem barrier_gradient_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 : ℝ) : Measurable (barrierGradient P B b K r σ T y0) := by
  obtain ⟨hXa,hXc,_⟩ := barrier_log_stock_regular P B y0 r σ
  have hs := open_continuous_hitting_stopping B.F B.mono (barrierLogStock P B y0 r σ) hXa hXc (Ici 0) isClosed_Ici
  have hhit : Measurable (fun w => upperBarrierHit (fun s => barrierLogStock P B y0 r σ s w)) := by
    apply measurable_of_Iic
    intro t
    exact B.le t _ (hs t)
  have hG : Measurable (fun z : Ω × ℝ => fderiv ℝ (barrierBrownianPrice b K r σ T y0)
      ![z.2,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) := by
    apply (measurable_fderiv_apply_const (𝕜:=ℝ) (f:=barrierBrownianPrice b K r σ T y0) (Pi.single 1 1)).comp
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact measurable_snd
    · exact half_local_joint_measurable P B.F B.le (B.W 0) (B.martingale 0)
  have hc : Measurable (fun z : Ω × ℝ => realTimeClamp (T:=(⊤:EReal)) z.2) := real_time_clamp_continuous.measurable.comp measurable_snd
  have hm := (measurableSet_lt (measurable_const (a:=(⊥ : HalfClosedTime))) hc).inter (measurableSet_le hc (hhit.comp measurable_fst))
  convert hG.indicator hm using 1
  funext z
  simp only [barrierGradient,Set.indicator_apply,mem_Ioc,mem_inter_iff,mem_setOf_eq,Function.comp_def]

theorem barrier_gradient_progressive {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 d : ℝ) (hd : 0≤d) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => barrierGradient P B b K r σ T y0 (z.1,z.2.val)) := by
  obtain ⟨hXa,hXc,_⟩ := barrier_log_stock_regular P B y0 r σ
  have hs := open_continuous_hitting_stopping B.F B.mono (barrierLogStock P B y0 r σ) hXa hXc (Ici 0) isClosed_Ici
  have hm : Measurable (fun q : ℝ × ℝ => fderiv ℝ (barrierBrownianPrice b K r σ T y0) ![q.1,q.2] (Pi.single 1 1)) := by
    apply (measurable_fderiv_apply_const (𝕜:=ℝ) (f:=barrierBrownianPrice b K r σ T y0) (Pi.single 1 1)).comp
    apply Measurable.of_eval
    intro i
    fin_cases i <;> fun_prop
  have hp := borel_diffusion_progressive P B.F B.mono (B.W 0) (fun _ _ => 0) (B.W 0)
    (local_martingale_semimartingale_decomposition P (T:=(⊤:EReal)) (by simp) B.F B.mono (B.W 0) (B.martingale 0))
    d hd (EReal.coe_lt_top d) _ hm
  have hbot : ∀ t,MeasurableSet[B.F t] {w : Ω | (⊥ : HalfClosedTime)≤t} := by simp
  exact stopping_interval_prefix_progressive B.F B.mono (fun _ => ⊥)
    (fun w => upperBarrierHit (fun s => barrierLogStock P B y0 r σ s w)) hbot hs d
    (fun z : Ω × ℝ => fderiv ℝ (barrierBrownianPrice b K r σ T y0) ![z.2,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) hp

/-- Capping the barrier time and clipping the time coordinate do not
change the delta integrand on the interval being checked. -/
theorem barrier_gradient_prefix_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T R y0 : ℝ) (hR : 0≤R) (τ : Ω → Icc (0:ℝ) R)
    (hτ : ∀ w,realTimeClamp (τ w).val=min
      (upperBarrierHit (fun s => barrierLogStock P B y0 r σ s w)) (realTimeClamp R))
    (w : Ω) (t : ℝ) (ht : t∈Icc 0 R) :
    (Ioc (⊥ : HalfClosedTime) (realTimeClamp (τ w).val)).indicator
      (fun _ => fderiv ℝ (barrierBrownianPrice b K r σ T y0)
        ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp t)).val,B.W 0 (realTimeClamp t) w] (Pi.single 1 1)) (realTimeClamp t)=
      barrierGradient P B b K r σ T y0 (w,t) := by
  dsimp only [barrierGradient]
  rw [finite_prefix_time_of_real R t hR ht le_top,hτ]
  simp only [Set.indicator_apply,mem_Ioc,le_min_iff,real_time_clamp_mono ht.2,and_true]

end Asakura.Chapter11

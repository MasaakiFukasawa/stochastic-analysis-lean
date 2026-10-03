import Chapter11BoundedStrategyIntegral
import Chapter5ProgressiveDriftVariation
import Chapter5BracketCommonTime
import Chapter6BoundedIntegrand

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- Construct the logarithmic wealth semimartingale from bounded progressive
coefficients, with its actual time drift and bracket on the entire horizon. -/
theorem logarithmic_wealth_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b H : Ω × ℝ → ℝ) (hbm : Measurable b) (hHm : Measurable H)
    (hbp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => b (z.1,z.2.val)))
    (hHp : ∀ d,0<d → @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) d => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => H (z.1,z.2.val)))
    (K L x R : ℝ) (hK : 0≤K) (hHb : ∀ z,|H z|≤K) (hbb : ∀ z,|b z|≤L) (hR : 0<R) :
    ∃ X A N C : HalfClosedTime → Ω → ℝ,
      SemimartingaleDecomposition P B.F X A N ∧
      ItoCovarianceFormula P B.F (B.W 0) H N ∧ LocalCovarianceWitness P B.F N N C ∧
      (∀ w,A ⊥ w=x) ∧
      (∀ w r,r∈Icc 0 R → A (realTimeClamp r) w=x+∫ s in 0..r,b (w,s)) ∧
      (∀ᵐ w ∂P,∀ r∈Icc 0 R,C (realTimeClamp r) w=∫ s in 0..r,(H (w,s))^2) ∧
      (X ⊥=ᵐ[P] fun _ => x) := by
  obtain ⟨N,C,hN,hNI,hC,hCe,_,_,_⟩ := bounded_strategy_integral P B H hHm hHp K hK hHb
  have hbi w d (hd : 0≤d) := bounded_time_integrable _ (hbm.comp measurable_prodMk_left) L
    (fun s => hbb (w,s)) d hd
  obtain ⟨D,hD,hDc,hDe⟩ := progressive_integrable_drift_variation (T:=(⊤:EReal)) (by simp)
    B.F B.mono R hR.le le_top b (hbp R hR) (fun w => (hbi w R hR.le).1)
  have hconst : AdaptedVariationWitness B.F (fun _ (_ : Ω) => x) := by
    refine ⟨(fun _ _ => x),(fun _ _ => 0),?_,?_,?_,?_⟩
    · exact fun _ => ⟨measurable_const,measurable_const⟩
    · exact fun _ => ⟨monotone_const,monotone_const⟩
    · exact fun _ _ => ⟨continuousWithinAt_const,continuousWithinAt_const⟩
    · exact fun _ _ => (sub_zero _).symm
  let A := fun t w => x+D t w
  let X := fun t w => A t w+N t w
  have hA : AdaptedLocalVariationWitness B.F A :=
    (global_variation_localized (by simp : (0:EReal)<⊤) B.F B.mono _ hconst).add hD B.mono
  have hX : SemimartingaleDecomposition P B.F X A N :=
    ⟨hA,hN,fun w t ht => (continuousAt_const.add (hDc w).continuousAt).add (hN.path P B.F w t ht),fun _ _ _ => rfl⟩
  have hAe w r (hr : r∈Icc 0 R) : A (realTimeClamp r) w=x+∫ s in 0..r,b (w,s) := by
    dsimp only [A]
    rw [hDe,finite_prefix_time_of_real R r hR.le hr le_top]
  have hz : realTimeClamp (T:=(⊤:EReal)) 0=⊥ := by
    apply Subtype.ext
    change (realTimeClamp (T:=(⊤:EReal)) 0 : EReal)=0
    simpa only [EReal.coe_zero] using real_time_clamp_eq (T:=(⊤:EReal)) 0 le_rfl le_top
  have hA0 w : A ⊥ w=x := by simpa only [hz,intervalIntegral.integral_same,add_zero] using hAe w 0 ⟨le_rfl,hR.le⟩
  have hCc := local_covariance_path_continuous P B.F N N C hN hN hC
  have hCv := covariance_adapted_variation P B.F B.mono B.le hN hN hC
  have hqi w : IntervalIntegrable (fun r => (H (w,r))^2) volume 0 R := by
    simpa only [pow_two,Function.comp_def] using bounded_product_time_integrable _ _
      (hHm.comp measurable_prodMk_left) (hHm.comp measurable_prodMk_left) K hK (fun r => hHb (w,r))
      (fun r => hHb (w,r)) R hR.le
  have hCcomm := bracket_primitive_common_time P R hR.le (fun r => C (realTimeClamp r)) (fun w r => (H (w,r))^2)
    ((open_process_real_regularity B.F C hCv.adapted hCc).2 R hR.le (EReal.coe_lt_top R))
    (ae_of_all _ hqi) (fun r hr => hCe r hr.1)
  refine ⟨X,A,N,C,hX,hNI,hC,hA0,hAe,hCcomm,?_⟩
  filter_upwards [hN.initial P B.F] with w hw
  change A ⊥ w+N ⊥ w=x
  simp only [hA0,hw,Pi.zero_apply,add_zero]

end Asakura.Chapter11

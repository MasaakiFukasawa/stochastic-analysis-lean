import Chapter3OpenPathMeasurable
import Chapter6GirsanovItoDrift
import Chapter6WeightedDriftCancellation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The beta*Z part disappears from the actual finite-variation part
under the measure built from the exponential density. -/
theorem linear_bsde_changed_drift {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (B : BrownianSystem P 1)
    (hPQ : ∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w)
    (β Z : Ω × ℝ → ℝ) (hβm : Measurable β) (hZm : Measurable Z)
    (K : ℝ) (hβb : ∀ z,|β z|≤K)
    (N M C Y V : HalfClosedTime → Ω → ℝ)
    (hN : LocalMProcessWitness P B.F N) (hY : SemimartingaleDecomposition P B.F Y V M)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) β N)
    (hMI : ItoCovarianceFormula P B.F (B.W 0) Z M)
    (hC : LocalCovarianceWitness P B.F N N C)
    (hZsq : ∀ b : ℝ,0≤b → ∀ᵐ w ∂P,IntervalIntegrable (fun r => Z (w,r)^2) volume 0 b)
    (R : ℝ) (hR : 0≤R)
    (hmean : (∫ w,Real.exp (N (realTimeClamp R) w-C (realTimeClamp R) w/2) ∂P)=1)
    (hQ : Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp (N (realTimeClamp R) w-C (realTimeClamp R) w/2))))
    (α φ : ℝ → Ω → ℝ) (hαc : ∀ w,Continuous (fun r => α r w)) (hφc : ∀ w,Continuous (fun r => φ r w))
    (hVeq : ∀ᵐ w ∂P,∀ r∈Icc 0 R,V (realTimeClamp r) w=V ⊥ w+
      ∫ s in 0..r,-(φ s w+α s w*Y (realTimeClamp s) w+β (w,s)*Z (w,s))) :
    ∃ VQ MQ,SemimartingaleDecomposition Q B.F Y VQ MQ ∧
      (∀ᵐ w ∂Q,∀ r∈Icc 0 R,VQ (realTimeClamp r) w=VQ ⊥ w+
        ∫ s in 0..r,-(φ s w+α s w*Y (realTimeClamp s) w)) := by
  obtain ⟨A,hA,hAc,hMQ,hAe⟩ := girsanov_ito_drift P Q B β Z hβm hZm K hβb N M C hN hY.martingale hNI hMI hC hZsq R hR hmean hQ
  have hT : (0:EReal)<⊤ := by simp
  have hAa := hA.adapted
  have hArc w : ContinuousOn (fun r => A (realTimeClamp r) w) (Icc 0 R) :=
    (open_process_real_regularity B.F A hAa hAc).2 R hR (EReal.coe_lt_top R) w
  have hYa t (ht : t<⊤) : Measurable[B.F t] (Y t) := by
    have he : Y t=(fun w => V t w+M t w) := funext (hY.decomposition t ht)
    rw [he]; exact (hY.variation.adapted t ht).add (hY.martingale.adapted P B.F t ht)
  have hYc w : ContinuousOn (fun r => Y (realTimeClamp r) w) (Icc 0 R) :=
    (open_process_real_regularity B.F Y hYa hY.continuous).2 R hR (EReal.coe_lt_top R) w
  have hprod : ∀ᵐ w ∂P,IntervalIntegrable (fun r => β (w,r)*Z (w,r)) volume 0 R := by
    filter_upwards [hZsq R hR] with w hw
    have hz2 : MemLp (fun r => Z (w,r)) 2 (volume.restrict (Ioc 0 R)) :=
      (memLp_two_iff_integrable_sq (hZm.comp measurable_prodMk_left).aestronglyMeasurable).mpr hw.1
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
    apply ((hz2.integrable (by norm_num)).norm.const_mul K).mono'
      (((hβm.comp measurable_prodMk_left).mul (hZm.comp measurable_prodMk_left)).aestronglyMeasurable)
    apply ae_of_all
    intro r
    change ‖β (w,r)*Z (w,r)‖≤K*‖Z (w,r)‖
    simpa only [norm_mul,Real.norm_eq_abs] using mul_le_mul_of_nonneg_right (hβb (w,r)) (abs_nonneg (Z (w,r)))
  have hall := bracket_primitive_common_time P R hR (fun r => A (realTimeClamp r))
    (fun w r => β (w,r)*Z (w,r)) hArc hprod (fun r hr => by simpa only [min_eq_right hr.2] using hAe r hr.1)
  let VQ := fun t w => V t w+A t w
  let MQ := fun t w => M t w-A t w
  have hdec : SemimartingaleDecomposition Q B.F Y VQ MQ := by
    refine ⟨hY.variation.add hA B.mono,hMQ,hY.continuous,?_⟩
    intro t ht w
    dsimp [VQ,MQ]
    rw [hY.decomposition t ht]
    ring
  refine ⟨VQ,MQ,hdec,(hPQ _).mp ?_⟩
  filter_upwards [hall,hVeq,hprod] with w hw hv hp
  have hA0 : A ⊥ w=0 := by
    have hz := hw 0 ⟨le_rfl,hR⟩
    have hz0 : realTimeClamp 0=(⊥ : HalfClosedTime) := by apply Subtype.ext; simp [realTimeClamp]
    simpa only [hz0,intervalIntegral.integral_same] using hz
  intro r hr
  have hf : IntervalIntegrable (fun s => φ s w+α s w*Y (realTimeClamp s) w) volume 0 r :=
    (((hφc w).continuousOn.add ((hαc w).continuousOn.mul (hYc w))).mono (Icc_subset_Icc_right hr.2)).intervalIntegrable_of_Icc hr.1
  have hp' : IntervalIntegrable (fun s => β (w,s)*Z (w,s)) volume 0 r := hp.mono_set (by simpa only [uIcc_of_le hr.1,uIcc_of_le hR] using Icc_subset_Icc_right hr.2)
  dsimp [VQ]
  rw [hv r hr,hw r hr,hA0,add_zero]
  rw [intervalIntegral.integral_neg,intervalIntegral.integral_add hf hp',intervalIntegral.integral_neg]
  ring

end Asakura.Chapter6

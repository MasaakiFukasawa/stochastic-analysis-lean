import Chapter12TimeDensityIntegral
import Chapter12CanonicalClock
import Chapter4BrownianSystem
import Chapter2ContinuousIntegrand
import Chapter11ExponentialVariation

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter11
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem constant_rate_bank_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : BrownianSystem P d)
    (i : Fin d) (r : ℝ) (η : Ω × ℝ → ℝ)
    (hηm : ∀ w,Measurable (fun t => η (w,t)))
    (hηp : ∀ n,@Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (canonicalClock n) => W.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (canonicalClock n) => η (z.1,z.2.val)))
    (hηi : ∀ n,∀ᵐ w ∂P,Integrable (fun t => η (w,t)*(r*Real.exp (r*t)))
      (volume.restrict (Ioc 0 (canonicalClock n)))) :
    let B := fun t w => Real.exp (r*W.C i i t w)
    AdaptedLocalVariationWitness W.F B ∧
    (∀ w t,t<⊤ → ContinuousAt (fun s => B s w) t) ∧
    ∃ E : HalfClosedTime → Ω → ℝ,AdaptedLocalVariationWitness W.F E ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => E s w) t) ∧
      VariationIntegralFormula P canonicalClock (fun n => (canonical_clock_properties.1 n).le) B η E := by
  intro B
  let b : Ω × ℝ → ℝ := fun z => r*Real.exp (r*z.2)
  have hbcont : Continuous (fun t : ℝ => r*Real.exp (r*t)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hbm w : Measurable (fun t => b (w,t)) := hbcont.measurable
  have hbp n : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (canonicalClock n) => W.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (canonicalClock n) => b (z.1,z.2.val)) :=
    continuous_adapted_real_progressive W.F W.mono b _ (canonical_clock_properties.1 n).le
      (fun _ _ => by dsimp only [b];exact measurable_const) (fun _ => hbcont.continuousOn)
  have hCv := covariance_adapted_variation P W.F W.mono W.le (W.martingale i) (W.martingale i) (W.cov i i)
  have hCc := covariance_continuous_at P W.F _ _ _ (W.martingale i) (W.martingale i) (W.cov i i)
  have hBv : AdaptedLocalVariationWitness W.F B :=
    exponential_continuous_local_variation W.F W.mono _ (hCv.smul r)
      (fun w t ht => (hCc w t ht).const_mul r)
  have hBc w t ht : ContinuousAt (fun s => B s w) t :=
    Real.continuous_exp.continuousAt.comp ((hCc w t ht).const_mul r)
  have hzero w : W.C i i ⊥ w=0 := by
    have hh := W.diagonal_clock i w 0 le_rfl
    have hz : realTimeClamp (T:=(⊤:EReal)) 0=⊥ := by
      apply Subtype.ext
      change (realTimeClamp (T:=(⊤:EReal)) 0:EReal)=0
      simpa only [EReal.coe_zero] using real_time_clamp_eq (T:=(⊤:EReal)) 0 le_rfl le_top
    simpa only [hz] using hh
  have heB : ∀ᵐ w ∂P,∀ n t,t∈Icc 0 (canonicalClock n) →
      B (realTimeClamp t) w=B ⊥ w+∫ s in 0..t,b (w,s) := by
    apply ae_of_all
    intro w n t ht
    have hd s : HasDerivAt (fun u : ℝ => Real.exp (r*u)) (r*Real.exp (r*s)) s := by
      convert ((hasDerivAt_id s).const_mul r).exp using 1 <;> simp [mul_comm]
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hbcont.intervalIntegrable 0 t)
    dsimp only [B,b]
    rw [W.diagonal_clock i w t ht.1,hzero,mul_zero,Real.exp_zero]
    simpa only [mul_zero,Real.exp_zero,add_comm] using (eq_add_of_sub_eq hh.symm)
  obtain ⟨E,hE,hEc,hEI⟩ := time_density_integral_constructed P W.F W.mono W.null
    canonicalClock (fun n => (canonical_clock_properties.1 n).le) canonical_clock_properties.2.1.monotone
    (fun n => EReal.coe_lt_top _) canonical_clock_properties.2.2.2.2.1 (W.C i i) B
    (fun _ w t ht => W.diagonal_clock i w t ht.1) η b hηm hbm hbp
    (fun n => (hηp n).mul (hbp n))
    (fun n => ae_of_all _ (fun _ => (hbcont.intervalIntegrable 0 (canonicalClock n)).1)) hηi heB
  exact ⟨hBv,hBc,E,hE,hEc,hEI⟩

end Asakura.Chapter12
#print axioms Asakura.Chapter12.constant_rate_bank_integral

import Chapter5LogExtension
import Chapter5ScalarLiftCalculus
import Chapter5TimeSpaceDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Ito's logarithm calculation for the positive conditional exponential.
A smooth extension makes use of the global C² Ito theorem legitimate;
the coefficient agrees with 1/(a X) throughout the required time interval. -/
theorem positive_log_ito
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X M C : ClosedTime T → Ω → ℝ) (U : Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X (fun _ => U) M)
    (hC : LocalCovarianceWitness P F M M C)
    (R : ℝ) (hR : 0 ≤ R) (hRT : (R:EReal) < T)
    (a b : ℝ) (hb : 0 < b)
    (hpos : ∀ᵐ w ∂P,∀ r ∈ Icc 0 R,b ≤ X (realTimeClamp r) w)
    (c : ℕ → ℝ) (hc : ∀ n,0 ≤ c n) (hcm : Monotone c)
    (hcT : ∀ n,(c n:EReal) < T)
    (hcc : ∀ t,t < ⊤ → ∃ n,t < realTimeClamp (T := T) (c n))
    (G : Ω × ℝ → ℝ) (hGm : ∀ w,Measurable (fun r => G (w,r)))
    (hGi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => G (w,r)) volume 0 (c n))
    (hCG : ∀ n,∀ᵐ w ∂P,∀ r ∈ Icc 0 (c n),C (realTimeClamp r) w = ∫ s in 0..r,G (w,s)) :
    ∃ N : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F M (fun z => deriv (logExtension b a) (X (realTimeClamp z.2) z.1)) N ∧
      (∀ᵐ w ∂P,∀ r ∈ Icc 0 R,deriv (logExtension b a) (X (realTimeClamp r) w) = 1/(a*X (realTimeClamp r) w)) ∧
      ∀ d ∈ Icc 0 R,
        (fun w => Real.log (X (realTimeClamp d) w)/a) =ᵐ[P]
          fun w => Real.log (X ⊥ w)/a+N (realTimeClamp d) w-
            (∫ r in 0..d,G (w,r)/(a*(X (realTimeClamp r) w)^2))/2 := by
  let ψ := logExtension b a
  let v : (Fin 2 → ℝ) → ℝ := fun x => ψ (x 1)
  have hψ := logExtension_contDiff b a hb 3
  have hv : ContDiff ℝ 2 v := (hψ.of_le (by norm_num)).comp (by fun_prop)
  have hd x := scalar_lift_derivatives ψ hψ x
  obtain ⟨N,hN,hNI,he⟩ := time_space_density_ito P hT F hF hle hnull
    X M C U hX hC R hR hRT v hv c hc hcm hcT hcc G hGm hGi hCG
  refine ⟨N,hN,?_,?_,?_⟩
  · convert hNI using 1
    funext z
    simpa only [v,ψ,Matrix.cons_val_one,Matrix.cons_val_zero] using
      (hd ![(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val,X (realTimeClamp z.2) z.1]).2.1.symm
  · filter_upwards [hpos] with w hw
    intro r hr
    exact (logExtension_derivatives b a _ hb (hw r hr)).2.1
  intro d hdd
  filter_upwards [he d hdd.1 hdd.2,hpos] with w hw hp
  have hz : realTimeClamp (T := T) 0 = ⊥ := by
    apply Subtype.ext
    exact real_time_clamp_eq 0 le_rfl (by simpa using hT.le)
  have hp0 : b ≤ X ⊥ w := by simpa only [hz] using hp 0 ⟨le_rfl,hR⟩
  have hzero : (fun r => fderiv ℝ v ![r,X (realTimeClamp r) w] (Pi.single 0 1)) = fun _ => 0 := by
    funext r; exact (hd _).1
  have hsecond : (∫ r in 0..d,fderiv ℝ (fderiv ℝ v) ![r,X (realTimeClamp r) w]
      (Pi.single 1 1) (Pi.single 1 1)*G (w,r)) =
      -(∫ r in 0..d,G (w,r)/(a*(X (realTimeClamp r) w)^2)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc 0 R := by
      rw [uIcc_of_le hdd.1] at hr
      exact ⟨hr.1,hr.2.trans hdd.2⟩
    dsimp only [v]
    rw [(hd ![r,X (realTimeClamp r) w]).2.2]
    simp only [ψ,Matrix.cons_val_one,Matrix.cons_val_zero]
    rw [(logExtension_derivatives b a _ hb (hp r hr')).2.2]
    ring
  rw [hzero,intervalIntegral.integral_zero,hsecond] at hw
  change ψ (X (realTimeClamp d) w) = ψ (X ⊥ w)+N (realTimeClamp d) w+0+ _ at hw
  dsimp only [ψ] at hw
  rw [(logExtension_derivatives b a _ hb (hp d hdd)).1,
    (logExtension_derivatives b a _ hb hp0).1] at hw
  linarith

end Asakura.Chapter5

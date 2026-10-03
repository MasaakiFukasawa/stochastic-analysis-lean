import Chapter8LongTimeRescaling
import Chapter7ScaledFiniteCLT

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The scalar long-time CLT used in the MLE proof. Time rescaling,
its n-dependent filtration and the bracket normalization are all constructed. -/
theorem long_time_scalar_clt {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (M C : HalfClosedTime → Ω → ℝ)
    (hM : LocalMProcessWitness P F M) (hC : LocalCovarianceWitness P F M M C)
    (c : ℝ) (hc : 0 < c)
    (havg : TendstoInMeasure P (fun T ω => C (realTimeClamp T) ω/T) atTop (fun _ => c))
    (T : ℕ → ℝ) (hT : ∀ n,0 < T n) (hTlim : Tendsto T atTop atTop) :
    ∃ (Γ : Type) (q : MeasurableSpace Γ) (Q : Measure Γ) (hQ : IsProbabilityMeasure Q),
    letI := q
    letI := hQ
    ∃ B0 : BrownianSystem (P.prod Q) 1,
      TendstoInDistribution (fun n ω => M (realTimeClamp (T n)) ω / Real.sqrt (T n)) atTop
        (fun z => Real.sqrt c*B0.W 0 (realTimeClamp 1) z) (fun _ => P) (P.prod Q) := by
  let G := fun n t => F (linearClock (T n) (hT n) t)
  let N := fun n t ω => M (linearClock (T n) (hT n) t) ω / Real.sqrt (T n*c)
  let D := fun n t ω => C (linearClock (T n) (hT n) t) ω / (T n*c)
  have hGn n : Monotone (G n) := hF.comp (linearClock (T n) (hT n)).monotone
  have hGl n t : G n t ≤ m := hle _
  have hND n := long_time_martingale_rescaling P F M C hM hC (T n) c (hT n) hc
  have hN n : LocalMProcessWitness P (G n) (N n) := (hND n).1
  have hD n : LocalCovarianceWitness P (G n) (N n) (N n) (D n) := (hND n).2
  have hC0 : C ⊥ =ᵐ[P] 0 := by
    filter_upwards [hM.initial P F,hC.defect.initial P F] with ω hm hd
    change M ⊥ ω*M ⊥ ω-C ⊥ ω = 0 at hd
    change M ⊥ ω = 0 at hm
    change C ⊥ ω = 0
    rw [hm] at hd
    linarith
  have hp (t : ℝ≥0) : TendstoInMeasure P (fun n => D n (realTimeClamp t)) atTop (fun _ => (t:ℝ)) := by
    by_cases ht : t = 0
    · subst t
      have hzero : TendstoInMeasure P (fun _ : ℕ => fun _ : Ω => (0:ℝ)) atTop (fun _ => (0:ℝ)) := by
        apply tendstoInMeasure_iff_dist.mpr
        intro ε hε
        simp [hε.not_ge]
      apply hzero.congr (fun n => ?_) .rfl
      filter_upwards [hC0] with ω hω
      have hcl : realTimeClamp (T := (⊤:EReal)) (0:ℝ) = ⊥ := by
        apply Subtype.ext
        exact real_time_clamp_eq 0 le_rfl le_top
      simp [D,hcl,(linearClock (T n) (hT n)).map_bot,hω]
    · have htpos : 0 < (t:ℝ) := NNReal.coe_pos.mpr (lt_of_le_of_ne t.property (Ne.symm ht))
      have hbase := havg.comp (hTlim.atTop_mul_const htpos)
      have hs := probability_const_mul P (fun n ω => C (realTimeClamp (T n*t)) ω/(T n*t))
        (fun _ => c) hbase ((t:ℝ)/c)
      convert hs using 1
      · funext n ω
        dsimp [D]
        rw [linear_clock_finite (T n) (hT n) t t.property]
        field_simp
      · funext ω
        field_simp
  obtain ⟨Γ,q,Q,hQ,B0,hlim⟩ := martingale_clt_varying_filtration_written P G hGn hGl N D hN hD hp
  letI := q
  letI := hQ
  refine ⟨Γ,q,Q,hQ,B0,?_⟩
  have he := hlim.continuous_comp (show Continuous (fun f : C(ℝ≥0,ℝ) => Real.sqrt c*f 1) from
    continuous_const.mul (continuous_eval_const 1))
  convert he using 1
  · funext n ω
    change M (realTimeClamp (T n)) ω/Real.sqrt (T n) =
      Real.sqrt c * (M (linearClock (T n) (hT n) (realTimeClamp 1)) ω / Real.sqrt (T n*c))
    rw [linear_clock_finite (T n) (hT n) 1 zero_le_one,mul_one,Real.sqrt_mul (hT n).le]
    field_simp
  · rfl

end Asakura.Chapter8

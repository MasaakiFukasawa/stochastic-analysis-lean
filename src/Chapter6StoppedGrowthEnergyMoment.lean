import Chapter6StoppedGrowthPathBound

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- A common expected energy bound under every stopped density measure.
Both the Brownian supremum bound and the Gronwall bound are supplied. -/
theorem stopped_growth_energy_moment {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] {d : ℕ} (BQ : BrownianSystem Q d)
    (W : Fin d → HalfClosedTime → Ω → ℝ) (H : Fin d → Ω × ℝ → ℝ)
    (R : ℝ) (hR : 0≤R) (K : ℝ) (hK : 0≤K)
    (hWc : ∀ w,ContinuousOn (fun r => (fun j => W j (realTimeClamp r) w)) (Icc 0 R))
    (hHc : ∀ j w,Continuous (fun r => H j (w,r)))
    (hHb : ∀ w r,r∈Icc 0 R → ‖WithLp.toLp 2 (fun j => H j (w,r))‖≤K*(1+‖WithLp.toLp 2 (fun j => W j (realTimeClamp r) w)‖))
    (u : Ω → ℝ) (hu : ∀ w,u w∈Icc 0 R)
    (hrep : ∀ᵐ w ∂Q,∀ j r,r∈Icc 0 R → BQ.W j (realTimeClamp r) w=W j (realTimeClamp r) w-∫ s in 0..min (u w) r,H j (w,s))
    (A : Ω → ℝ) (hAm : AEStronglyMeasurable A Q)
    (hAe : ∀ᵐ w ∂Q,A w=∫ s in 0..u w,∑ j,(H j (w,s))^2) :
    let a := (d:ℝ)*K*R
    let e := Real.exp (((d:ℝ)*K+1)*R)
    Integrable A Q ∧ (∫ w,A w ∂Q)≤R*K^2*(2*(1+a*e)^2+8*e^2*(d:ℝ)^2*R) := by
  let a := (d:ℝ)*K*R
  let e := Real.exp (((d:ℝ)*K+1)*R)
  have ha : 0≤a := by dsimp [a]; positivity
  have he : 0≤e := (Real.exp_pos _).le
  obtain ⟨G,hGi,hG0,hG2,hGb⟩ := brownian_path_L2_envelope_bound Q BQ R hR
  let V := fun w => R*K^2*(2*(1+a*e)^2+2*e^2*(G w)^2)
  have hVi : Integrable V Q := ((integrable_const (2*(1+a*e)^2)).add (hGi.integrable_sq.const_mul (2*e^2))).const_mul (R*K^2)
  have hb : ∀ᵐ w ∂Q,0≤A w ∧ A w≤V w := by
    filter_upwards [hrep,hAe] with w hw hc
    have hpath := stopped_vector_growth_path_bound
      (fun r j => W j (realTimeClamp r) w) (fun r j => BQ.W j (realTimeClamp r) w) (fun r j => H j (w,r))
      R (u w) K (G w) hR (hu w) hK (hG0 w) (hWc w)
      (continuous_pi (fun j => hHc j w)).continuousOn (hHb w) (hGb w)
      (fun r hr j => by linarith [hw j r hr])
    have hbound s (hs : s∈Icc 0 (u w)) : ∑ j,(H j (w,s))^2≤K^2*(1+(a+G w)*e)^2 := by
      have hsr : s∈Icc 0 R := ⟨hs.1,hs.2.trans (hu w).2⟩
      have hh : ‖WithLp.toLp 2 (fun j => H j (w,s))‖≤K*(1+(a+G w)*e) := (hHb w s hsr).trans (mul_le_mul_of_nonneg_left (by linarith [hpath s hsr]) hK)
      simpa only [EuclideanSpace.real_norm_sq_eq,mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2
    have hi : IntervalIntegrable (fun s => ∑ j,(H j (w,s))^2) volume 0 (u w) :=
      (continuous_finsetSum _ (fun j _ => (hHc j w).pow 2)).continuousOn.intervalIntegrable_of_Icc (hu w).1
    rw [hc]
    refine ⟨intervalIntegral.integral_nonneg (hu w).1 (fun s _ => sum_nonneg (fun j _ => sq_nonneg _)),?_⟩
    calc
      _ ≤ ∫ s in 0..u w,K^2*(1+(a+G w)*e)^2 := intervalIntegral.integral_mono_on (hu w).1 hi intervalIntegrable_const hbound
      _ = K^2*(1+(a+G w)*e)^2*(u w) := by rw [intervalIntegral.integral_const]; simp only [sub_zero,smul_eq_mul]; ring
      _ ≤ K^2*(1+(a+G w)*e)^2*R := mul_le_mul_of_nonneg_left (hu w).2 (by positivity)
      _ ≤ V w := by
        have hs : (1+(a+G w)*e)^2≤2*(1+a*e)^2+2*e^2*(G w)^2 := by nlinarith [sq_nonneg (1+a*e-e*G w)]
        have hh := mul_le_mul_of_nonneg_left hs (mul_nonneg hR (sq_nonneg K))
        dsimp [V]
        nlinarith
  have hAi : Integrable A Q := hVi.mono' hAm (hb.mono (fun w hw => by rw [Real.norm_eq_abs,abs_of_nonneg hw.1]; exact hw.2))
  refine ⟨hAi,?_⟩
  calc
    _ ≤ ∫ w,V w ∂Q := integral_mono_ae hAi hVi (hb.mono (fun _ h => h.2))
    _ = R*K^2*(2*(1+a*e)^2+2*e^2*(∫ w,(G w)^2 ∂Q)) := by
      rw [integral_const_mul,integral_add (integrable_const _) (hGi.integrable_sq.const_mul _),integral_const,integral_const_mul]
      simp
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hG2 (by positivity : 0≤R*K^2*(2*e^2))
      dsimp [a,e] at *
      nlinarith

end Asakura.Chapter6

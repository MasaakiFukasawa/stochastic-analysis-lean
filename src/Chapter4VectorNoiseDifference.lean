import Chapter4VectorCoefficientDifference
import Chapter4ClockRegularity
import Chapter4BrownianFiniteMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- One actual Ito integral whose integrand is a coefficient difference
obeys the Picard estimate, using only its values on the finite horizon. -/
theorem noise_difference_path_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C H N : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hC : LocalCovarianceWitness P F W W C)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → C (realTimeClamp r) w=r)
    (hHa : ∀ t,t<⊤ → Measurable[F t] (H t))
    (hHc : ∀ w t,t<⊤ → ContinuousAt (fun s => H s w) t)
    (hN : LocalMProcessWitness P F N)
    (hNI : ItoCovarianceFormula P F W (fun z => H (realTimeClamp z.2) z.1) N)
    (R L : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (hL : 0≤L)
    (b : (Fin dim → ℝ) → ℝ) (hb : Continuous b)
    (hLip : ∀ x y,(b x-b y)^2≤L*‖x-y‖^2)
    (Y₁ Y₂ : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (hm₁ : Measurable[m] Y₁) (hm₂ : Measurable[m] Y₂) (hi₁ : MemLp Y₁ 2 P) (hi₂ : MemLp Y₂ 2 P)
    (hH : ∀ w r,r∈Icc 0 R → H (realTimeClamp r) w=
      b (Y₁ w (projIcc 0 R hR r))-b (Y₂ w (projIcc 0 R hR r))) :
    ∃ hc : ∀ w,Continuous (fun t => N (min (realTimeClamp R) t) w),
      MemLp (finiteRealPath N R hc) 2 P ∧
      (∫ w,‖finiteRealPath N R hc w‖^2 ∂P)≤
        (4*L)*(∫ r in 0..R,(∫ w,‖prefixPath hR (Y₁ w-Y₂ w) r‖^2 ∂P)) := by
  letI : MeasurableSpace Ω := m
  let U := fun z : Ω × ℝ => b (Y₁ z.1 (projIcc 0 R hR z.2))-b (Y₂ z.1 (projIcc 0 R hR z.2))
  obtain ⟨hiU,hE⟩ := one_coefficient_difference_energy P R L hR hL b hb hLip Y₁ Y₂ hm₁ hm₂ hi₁ hi₂
  have hiU2 := (memLp_two_iff_integrable_sq hiU.aestronglyMeasurable).1 hiU
  have henergy w : (∫ r in 0..R,H (realTimeClamp r) w^2)=∫ r in 0..R,U (w,r)^2 := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc 0 R := by simpa [uIcc_of_le hR] using hr
    dsimp only [U]
    rw [hH w r hr']
  have hei : Integrable (fun w => ∫ r in 0..R,H (realTimeClamp r) w^2) P := by
    simp_rw [henergy,intervalIntegral.integral_of_le hR]
    exact hiU2.integral_prod_left
  obtain ⟨hCm,hCc⟩ := clock_regular_from_identity C hclock
  obtain ⟨hc,hi,hbN⟩ := brownian_ito_finite_path_moment P hT F hF hle hnull W C H N hW hC hCm hCc hclock
    hHa hHc hN hNI R hR hRT hei
  have he : (∫ w,(∫ r in 0..R,H (realTimeClamp r) w^2) ∂P)=∫ z,U z^2 ∂P.prod (volume.restrict (Ioc (0:ℝ) R)) := by
    simp_rw [henergy,intervalIntegral.integral_of_le hR]
    exact (integral_prod _ hiU2).symm
  rw [he] at hbN
  exact ⟨hc,hi,hbN.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hE (by norm_num : (0:ℝ)≤4))⟩

end Asakura.Chapter4.Vector

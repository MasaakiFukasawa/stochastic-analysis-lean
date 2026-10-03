import Chapter4ClockRegularity
import Chapter4BrownianFiniteMoment
import Chapter4PathEquality

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Equal integrands up to a finite time give indistinguishable integrals
up to that time, with no conditions imposed after it. This follows from
the constructed integral's maximal estimate and zero input energy. -/
theorem brownian_ito_prefix_congr
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hC : LocalCovarianceWitness P F W W C)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → C (realTimeClamp r) w=r)
    (H₁ H₂ N₁ N₂ : ClosedTime T → Ω → ℝ)
    (ha₁ : ∀ t,t<⊤ → Measurable[F t] (H₁ t))
    (ha₂ : ∀ t,t<⊤ → Measurable[F t] (H₂ t))
    (hc₁ : ∀ w t,t<⊤ → ContinuousAt (fun s => H₁ s w) t)
    (hc₂ : ∀ w t,t<⊤ → ContinuousAt (fun s => H₂ s w) t)
    (hn₁ : LocalMProcessWitness P F N₁) (hn₂ : LocalMProcessWitness P F N₂)
    (hI₁ : ItoCovarianceFormula P F W (fun z => H₁ (realTimeClamp z.2) z.1) N₁)
    (hI₂ : ItoCovarianceFormula P F W (fun z => H₂ (realTimeClamp z.2) z.1) N₂)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (he : ∀ᵐ w ∂P,∀ r,r∈Icc 0 R → H₁ (realTimeClamp r) w=H₂ (realTimeClamp r) w) :
    ∀ᵐ w ∂P,∀ r,r∈Icc 0 R → N₁ (realTimeClamp r) w=N₂ (realTimeClamp r) w := by
  let H := fun t w => H₁ t w-H₂ t w
  let N := fun t w => N₁ t w-N₂ t w
  have hN : LocalMProcessWitness P F N := by
    simpa only [neg_one_mul,neg_add_eq_sub] using (hn₂.smul P F (-1)).add P F hF hle hn₁
  have hNI : ItoCovarianceFormula P F W (fun z => H (realTimeClamp z.2) z.1) N := by
    simpa only [neg_one_mul,neg_add_eq_sub] using hI₂.add_smul P F hF hle W N₂ N₁ _ _ hI₁ (-1)
  have henergy : (fun w => ∫ r in 0..R,H (realTimeClamp r) w^2)=ᵐ[P] (fun _ => (0:ℝ)) := by
    filter_upwards [he] with w hw
    calc (∫ r in 0..R,H (realTimeClamp r) w^2) = ∫ _r in 0..R,(0:ℝ) := by
           apply intervalIntegral.integral_congr
           intro r hr
           have hr' : r∈Icc 0 R := by simpa [uIcc_of_le hR] using hr
           dsimp only [H]
           rw [hw r hr',sub_self,zero_pow (by decide : (2:ℕ)≠0)]
         _ = 0 := intervalIntegral.integral_zero
  obtain ⟨hCm,hCc⟩ := clock_regular_from_identity C hclock
  obtain ⟨hc,hi,hb⟩ := brownian_ito_finite_path_moment P hT F hF hle hnull W C H N hW hC hCm hCc hclock
    (fun t ht => (ha₁ t ht).sub (ha₂ t ht)) (fun w t ht => (hc₁ w t ht).sub (hc₂ w t ht))
    hN hNI R hR hRT ((integrable_zero Ω ℝ P).congr henergy.symm)
  have hz : (∫ w,‖finiteRealPath N R hc w‖^2 ∂P)=0 := by
    rw [integral_congr_ae henergy,integral_zero,mul_zero] at hb
    exact le_antisymm hb (integral_nonneg (fun _ => sq_nonneg _))
  have heq : finiteRealPath N R hc=ᵐ[P] (fun _ => (0 : C(Icc (0:ℝ) R,ℝ))) :=
    paths_equal_of_zero_second_moment P (finiteRealPath N R hc) (fun _ => 0)
      (by simpa only [sub_zero] using hi) (by simpa only [sub_zero] using hz)
  filter_upwards [heq] with w hw
  intro r hr
  have hv := congrArg (fun p : C(Icc (0:ℝ) R,ℝ) => p ⟨r,hr⟩) hw
  change N₁ (realTimeClamp r) w-N₂ (realTimeClamp r) w=0 at hv
  exact sub_eq_zero.mp hv

end Asakura.Chapter4

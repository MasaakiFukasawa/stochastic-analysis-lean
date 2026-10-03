import Chapter5BrownianIntegralBracket
import Chapter2StoppedM2Equivalence
import Chapter2ContinuousIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- A bounded continuous adapted Brownian integrand gives an M² process
on every finite stopped interval, by the actual bracket and Proposition 2.4.4. -/
theorem bounded_brownian_integral_stopped_M2
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (W A Y : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hA : LocalCovarianceWitness P F W W A)
    (hY : LocalMProcessWitness P F Y)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (G : Ω × ℝ → ℝ)
    (hGa : ∀ r : ℝ,0≤r → (r:EReal)<T → Measurable[F (realTimeClamp r)] (fun w => G (w,r)))
    (hGc : ∀ b : ℝ,0≤b → (b:EReal)<T → ∀ w,ContinuousOn (fun r => G (w,r)) (Icc 0 b))
    (hI : ItoCovarianceFormula P F W G Y)
    (R C : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (hC : 0≤C)
    (hbound : ∀ w r,r∈Icc 0 R → |G (w,r)|≤C) :
    ContinuousM2Witness P F (fun t w => Y (min (realTimeClamp R) t) w) := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hGp n := continuous_adapted_real_progressive F hF G (c n) (hc n).le
    (fun r hr => hGa r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) (hGc (c n) (hc n).le (hcT n))
  have hGi n : ∀ᵐ w ∂P,IntervalIntegrable (fun r => G (w,r)^2) volume 0 (c n) :=
    ae_of_all _ fun w => ((hGc (c n) (hc n).le (hcT n) w).pow 2).intervalIntegrable_of_Icc (hc n).le
  obtain ⟨Q,hQ,hQE⟩ := clock_ito_integral_bracket P hT F hF hle hnull W A Y hW hA hY
    c hc hcm hcT hct hcut hcc (fun n w r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) G hGp hGi hI
  have hRt : realTimeClamp (T := T) R<⊤ := by
    change (realTimeClamp R:EReal)<T
    rw [real_time_clamp_eq R hR hRT.le]
    exact hRT
  have hQm : Measurable (Q (realTimeClamp R)) := by
    have hy := (hY.adapted P F _ hRt).mono (hle _) le_rfl
    have hd := (hQ.defect.adapted P F _ hRt).mono (hle _) le_rfl
    convert (hy.mul hy).sub hd using 1
    funext w
    dsimp only [Pi.sub_apply,Pi.mul_apply]
    ring
  have hQB : ∀ᵐ w ∂P,‖Q (realTimeClamp R) w‖≤C^2*R := by
    filter_upwards [hQE R hR hRT] with w hw
    rw [hw,Real.norm_eq_abs,abs_of_nonneg (intervalIntegral.integral_nonneg_of_forall hR (fun r => sq_nonneg _))]
    have hgi := ((hGc R hR hRT w).pow 2).intervalIntegrable_of_Icc (μ := volume) hR
    calc
      _ ≤ ∫ r in 0..R,C^2 := intervalIntegral.integral_mono_on hR hgi intervalIntegrable_const
        (fun r hr => by simpa only [sq_abs,Pi.pow_apply] using pow_le_pow_left₀ (abs_nonneg _) (hbound w r hr) 2)
      _ = C^2*R := by simp; ring
  have hQi : Integrable (Q (realTimeClamp R)) P := Integrable.of_bound hQm.aestronglyMeasurable (C^2*R) hQB
  have hstop : ∀ t,MeasurableSet[F t] {w : Ω | realTimeClamp (T := T) R≤t} := by
    intro t
    by_cases h : realTimeClamp (T := T) R≤t <;> simp [h]
  have he := stopped_local_M2_equivalences P F hF hle hnull Y Q hY hQ
    (fun _ => realTimeClamp R) hstop (fun _ => hRt)
  exact he.2.mp (he.1.mp hQi)

end Asakura.Chapter5

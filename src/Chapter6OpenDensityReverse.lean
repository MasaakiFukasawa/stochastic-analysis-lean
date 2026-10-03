import Chapter6OpenDensityForward
import Chapter2LocalPathEncoding
import Chapter6InverseDensity

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The reverse product criterion is obtained by actually reversing the density,
including its integrability and conditional-expectation identity. -/
theorem open_local_martingale_of_density_times
    {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (d : Ω → ℝ≥0) (hd : Measurable d)
    (hdi : Integrable (fun w => (d w : ℝ)) P)
    (hp : ∀ᵐ w ∂P,0 < (d w : ℝ))
    (hQ : Q = P.withDensity (fun w => (d w : ℝ≥0∞)))
    (M X : ClosedTime T → Ω → ℝ)
    (hMa : ∀ t,Measurable[F t] (M t)) (hMc : ∀ w t,t < ⊤ → ContinuousAt (fun s => M s w) t)
    (hMp : ∀ t w,0 < M t w)
    (hME : ∀ t,M t =ᵐ[P] P[(fun w => (d w : ℝ))|F t])
    (hXa : ∀ t,Measurable[F t] (X t))
    (hMX : LocalMProcessWitness P F (fun t w => M t w*X t w))
    (u : ℕ → ClosedTime T) (hu : Monotone u) (hut : ∀ n,u n < ⊤)
    (huc : ∀ t,t < ⊤ → ∃ n,t < u n) :
    LocalMProcessWitness Q F X := by
  have hae (p : Ω → Prop) : (∀ᵐ w ∂Q,p w) ↔ (∀ᵐ w ∂P,p w) := by
    rw [hQ]
    exact positive_density_ae_iff P d hd hp p
  have hi : Integrable (fun w => ((d w)⁻¹ : ℝ)) Q := by
    simpa using inverse_density_integrable P Q d hd hp hQ
  have hpos : ∀ᵐ w ∂Q,0 < ((d w)⁻¹ : ℝ) := by
    apply (hae _).mpr
    filter_upwards [hp] with w hw
    simpa using inv_pos.mpr hw
  have he : ∀ t,(fun w => (M t w)⁻¹) =ᵐ[Q]
      Q[(fun w => ((d w)⁻¹ : ℝ))|F t] := by
    intro t
    apply (hae _).mpr
    have hh := inverse_density_conditional P Q (hle t) d hd hdi hp hQ
    filter_upwards [hh,hME t] with w hw hm
    simpa [hm] using hw.symm
  have hh := open_density_times_local_martingale Q P hT F hF hle
    (fun w => (d w)⁻¹) hd.inv hi hpos
    (inverse_nnreal_density_measure P Q d hd hp hQ)
    (fun t w => (M t w)⁻¹) (fun t w => M t w*X t w)
    (fun t => (hMa t).inv)
    (fun w t ht => (hMc w t ht).inv₀ (ne_of_gt (hMp t w))) he
    (fun t => (hMa t).mul (hXa t)) hMX u hu hut huc
  have hcancel : (fun t w => (M t w)⁻¹*(M t w*X t w)) = X := by
    funext t w
    rw [← mul_assoc,inv_mul_cancel₀ (ne_of_gt (hMp t w)),one_mul]
  rwa [hcancel] at hh

theorem open_process_local_of_density_product
    {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (d : Ω → ℝ≥0) (hd : Measurable d)
    (hdi : Integrable (fun w => (d w : ℝ)) P)
    (hp : ∀ᵐ w ∂P,0 < (d w : ℝ))
    (hQ : Q = P.withDensity (fun w => (d w : ℝ≥0∞)))
    (M X : ClosedTime T → Ω → ℝ)
    (hMa : ∀ t,Measurable[F t] (M t)) (hMc : ∀ w t,t < ⊤ → ContinuousAt (fun s => M s w) t)
    (hMp : ∀ t w,0 < M t w)
    (hME : ∀ t,M t =ᵐ[P] P[(fun w => (d w : ℝ))|F t])
    (hXa : ∀ t,t < ⊤ → Measurable[F t] (X t))
    (hMX : LocalMProcessWitness P F (fun t w => M t w*X t w))
    (u : ℕ → ClosedTime T) (hu : Monotone u) (hut : ∀ n,u n < ⊤)
    (huc : ∀ t,t < ⊤ → ∃ n,t < u n) :
    LocalMProcessWitness Q F X := by
  let Y := fun t w => if t < ⊤ then X t w else 0
  have hYa t : Measurable[F t] (Y t) := by
    by_cases ht : t < ⊤
    · simpa only [Y,if_pos ht] using hXa t ht
    · simpa only [Y,if_neg ht] using (measurable_const (a := (0:ℝ)) : Measurable[F t] (fun _ : Ω => (0:ℝ)))
  have hMY : LocalMProcessWitness P F (fun t w => M t w*Y t w) :=
    hMX.congr_before_terminal P F (fun t ht => by funext w; simp only [Y,if_pos ht])
  have hh := open_local_martingale_of_density_times P Q hT F hF hle d hd hdi hp hQ M Y
    hMa hMc hMp hME hYa hMY u hu hut huc
  exact hh.congr_before_terminal Q F (fun t ht => by funext w; simp only [Y,if_pos ht])

end Asakura.Chapter6

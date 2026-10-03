import Chapter8SDELinearCoordinates
import Chapter8AdditiveUniqueness
import Chapter8IndependentInitialBrownian

open MeasureTheory Set
open scoped BigOperators NNReal
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- An actual deterministic-initial-value solution on the product space
agrees with the original solution driven by the second coordinate. -/
theorem product_sde_identification {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    {d n : ℕ} (B : BrownianSystem P n) (B' : BrownianSystem (ν.prod P) n)
    (hW : ∀ j t z,B'.W j t z=B.W j t z.2)
    (b : (Fin d → ℝ) → Fin d → ℝ) (K : ℝ≥0) (hb : LipschitzWith K b)
    (σ : Fin d → Fin n → ℝ) (x : Fin d → ℝ)
    (X : HalfClosedTime → Ω → Fin d → ℝ)
    (X' : HalfClosedTime → A × Ω → Fin d → ℝ)
    (hX : VectorSDESolution P B.F B.W (fun i y => b y i) (fun i j _ => σ i j) (fun _ => x) X)
    (hX' : VectorSDESolution (ν.prod P) B'.F B'.W (fun i y => b y i) (fun i j _ => σ i j) (fun _ => x) X') :
    ∀ᵐ z ∂ν.prod P,∀ t : ℝ,0≤t → X' (realTimeClamp t) z=X (realTimeClamp t) z.2 := by
  have hE := sde_linear_coordinate_equation P B b hb.continuous σ x X hX (ContinuousLinearMap.id ℝ _)
  have hE' := sde_linear_coordinate_equation (ν.prod P) B' b hb.continuous σ x X' hX' (ContinuousLinearMap.id ℝ _)
  have hlift := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := P)).ae hE
  have hc w : Continuous (fun t : ℝ => X (realTimeClamp t) w) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hX.path w _ (half_real_time_finite t)).comp real_time_clamp_continuous.continuousAt
  have hc' z : Continuous (fun t : ℝ => X' (realTimeClamp t) z) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hX'.path z _ (half_real_time_finite t)).comp real_time_clamp_continuous.continuousAt
  filter_upwards [hlift,hE'] with z hz hz'
  intro t ht
  apply additive_path_unique b K hb _ _
    (fun s => ∑ j,B.W j (realTimeClamp s) z.2 • (fun i => σ i j))
    (hc' z) (hc z.2) x t ht _ _ t ⟨ht,le_rfl⟩
  · intro s hs
    simpa only [ContinuousLinearMap.id_apply,hW] using hz' s hs.1
  · intro s hs
    simpa only [ContinuousLinearMap.id_apply] using hz s hs.1
end Asakura.Chapter8

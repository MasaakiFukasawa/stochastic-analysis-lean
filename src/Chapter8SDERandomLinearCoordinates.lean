import Chapter8BrownianForcingPath
import Chapter8SDERandomAdditiveEquation

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Constant linear coordinates commute with the drift integral and the
constant-diffusion Ito integral, simultaneously at all nonnegative times. -/
theorem sde_random_linear_coordinate_equation {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (b : (Fin d → ℝ) → (Fin d → ℝ)) (hb : Continuous b)
    (σ : Fin d → Fin n → ℝ) (x : Ω → Fin d → ℝ)
    (X : HalfClosedTime → Ω → Fin d → ℝ)
    (hX : VectorSDESolution P B.F B.W (fun i y => b y i)
      (fun i j _ => σ i j) x X)
    (A : (Fin d → ℝ) →L[ℝ] E) :
    ∀ᵐ w ∂P,∀ t : ℝ,0≤t →
      A (X (realTimeClamp t) w)=A (x w)+
        (∫ s in 0..t,A (b (X (realTimeClamp s) w)))+
        ∑ j,B.W j (realTimeClamp t) w • A (fun i => σ i j) := by
  have hc w : Continuous (fun r => X (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hX.path w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt
  filter_upwards [sde_random_additive_equation P B (fun i y => b y i) σ x X hX] with w hw
  intro t ht
  have hi := (hb.comp (hc w)).intervalIntegrable 0 t (μ := volume)
  have he : X (realTimeClamp t) w=x w+(∫ s in 0..t,b (X (realTimeClamp s) w))+
      ∑ j,B.W j (realTimeClamp t) w • (fun i => σ i j) := by
    ext i
    have hp := (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm hi
    change (∫ s in 0..t,b (X (realTimeClamp s) w) i)=(∫ s in 0..t,b (X (realTimeClamp s) w)) i at hp
    simpa only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm,←hp]
      using hw t ht i
  rw [he,map_add,map_add,map_sum]
  simp only [map_smul]
  have hA := A.intervalIntegral_comp_comm hi
  simp only [Function.comp_apply] at hA
  rw [hA]

end Asakura.Chapter8

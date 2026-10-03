import Chapter8SDELinearCoordinates
import Chapter8AdditiveUniqueness
import Chapter2CommonTimeEquality
import Chapter6WeakSDEAlgebra

open MeasureTheory Set
open scoped NNReal BigOperators
namespace Asakura.Chapter8
open Asakura.Chapter6 Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The Brownian motion produced by the likelihood density gives the
same observed path as the actual Lipschitz SDE, on the whole observation interval. -/
theorem changed_brownian_actual_sde {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (B : BrownianSystem P d) (BQ : BrownianSystem Q d)
    (S A : Fin d → Fin d → ℝ) (hSA : ∀ i k,∑ j,S i j*A j k=if i=k then 1 else 0)
    (x : Fin d → ℝ) (b : (Fin d → ℝ) → Fin d → ℝ) (K : ℝ≥0) (hb : LipschitzWith K b)
    (R : ℝ) (hR : 0≤R)
    (hrep : ∀ j r,r∈Icc 0 R → BQ.W j (realTimeClamp r)=ᵐ[Q]
      fun w => B.W j (realTimeClamp r) w-∫ s in 0..r,∑ k,A j k*b (fun i => x i+∑ l,S i l*B.W l (realTimeClamp s) w) k)
    (Z : HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : VectorSDESolution Q BQ.F BQ.W (fun i y => b y i) (fun i j _ => S i j) (fun _ => x) Z) :
    ∀ᵐ w ∂Q,∀ r∈Icc 0 R,Z (realTimeClamp r) w=(fun i => x i+∑ j,S i j*B.W j (realTimeClamp r) w) := by
  haveI : Nonempty (Icc (0:ℝ) R) := ⟨⟨0,le_rfl,hR⟩⟩
  let X := fun r w i => x i+∑ j,S i j*B.W j (realTimeClamp r) w
  have hWc j w : Continuous (fun r : ℝ => B.W j (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact ((B.martingale j).path P B.F w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt
  have hQc j w : Continuous (fun r : ℝ => BQ.W j (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact ((BQ.martingale j).path Q BQ.F w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt
  have hXc w : Continuous (fun r => X r w) := continuous_pi (fun i => continuous_const.add
    (continuous_finsetSum _ (fun j _ => (hWc j w).const_mul _)))
  have hbc j w : Continuous (fun r => ∑ k,A j k*b (X r w) k) := continuous_finsetSum _
    (fun k _ => (((continuous_apply k).comp hb.continuous).comp (hXc w)).const_mul _)
  have he j := continuous_process_common_time_equality Q
    (fun r : Icc (0:ℝ) R => BQ.W j (realTimeClamp r.val))
    (fun (r : Icc (0:ℝ) R) w => B.W j (realTimeClamp r.val) w-∫ s in 0..r.val,∑ k,A j k*b (X s w) k)
    (fun w => (hQc j w).comp continuous_subtype_val)
    (fun w => ((hWc j w).sub (intervalIntegral.differentiable_integral_of_continuous (hbc j w)).continuous).comp continuous_subtype_val)
    (fun r => hrep j r.val r.property)
  have hZc w : Continuous (fun r : ℝ => Z (realTimeClamp r) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hZ.path w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt
  filter_upwards [ae_all_iff.mpr he,sde_linear_coordinate_equation Q BQ b hb.continuous S x Z hZ (ContinuousLinearMap.id ℝ _)] with w hw hz
  intro r hr
  apply additive_path_unique b K hb _ _ (fun s => ∑ j,BQ.W j (realTimeClamp s) w • (fun i => S i j))
    (hZc w) (hXc w) x R hR _ _ r hr
  · intro s hs
    simpa only [ContinuousLinearMap.id_apply] using hz s hs.1
  · intro s hs
    ext i
    have hi k := (((continuous_apply k).comp hb.continuous).comp (hXc w)).intervalIntegrable (μ := volume) 0 s
    have hh := weak_sde_matrix_algebra S A hSA (fun k t => b (X t w) k) s hi x
      (fun j => B.W j (realTimeClamp s) w) (fun j => BQ.W j (realTimeClamp s) w)
      (fun j => hw j ⟨s,hs⟩) i
    have hp := (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm
      ((hb.continuous.comp (hXc w)).intervalIntegrable 0 s (μ := volume))
    change (∫ t in 0..s,b (X t w) i)=(∫ t in 0..s,b (X t w)) i at hp
    simpa only [X,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,←hp,mul_comm] using hh
end Asakura.Chapter8

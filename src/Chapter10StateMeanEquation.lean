import Chapter10LinearMeanFubini
import Chapter10DeterministicNoiseMean
import Chapter10LinearStateWitness

open MeasureTheory Set Filter
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Taking expectations of the actual state equation, with integrability and
Fubini established from the finite-horizon path moment. -/
theorem LinearStateWitness.mean_equation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ s,‖A s‖≤K)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T)
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X) (i : Fin d) (r : Icc (0:ℝ) T) :
    (∫ w,X w r i ∂P)=(∫ w,ξ w i ∂P)+
      ∫ s in 0..r.val,∫ w,(A s (X w (projIcc 0 T hT s))) i ∂P := by
  have hn j := deterministic_noise_centered P B j (G i j) (hG i j) (N i j)
    (h.noise i j) (h.ito i j) r.val r.property.1
  have hsum : Integrable (fun w => ∑ j,N i j (realTimeClamp r.val) w) P :=
    integrable_finsetSum _ (fun j _ => (hn j).1)
  have hsum0 : (∫ w,(∑ j,N i j (realTimeClamp r.val) w) ∂P)=0 := by
    rw [integral_finsetSum _ (fun j _ => (hn j).1)]
    simp only [(hn _).2,Finset.sum_const_zero]
  have hxi : Integrable (fun w => ξ w i) P :=
    (show (Fin d → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj i).integrable_comp (hξ2.integrable (by norm_num))
  obtain ⟨hi,hfi⟩ := linear_mean_drift_fubini P T hT X h.measurable h.moment A hA K hAK i r.val r.property.1
  have he : (fun w => X w r i) = fun w => ξ w i+
      (∫ s in 0..r.val,(A s (X w (projIcc 0 T hT s))) i)+∑ j,N i j (realTimeClamp r.val) w := by
    funext w
    have hh := (h.decomposition i).decomposition (realTimeClamp r.val) (half_real_time_finite r.val) w
    rw [finite_prefix_time_of_real T r.val hT r.property le_top,
      min_eq_right (real_time_clamp_mono r.property.2)] at hh
    have hp : finitePrefixTime T hT (realTimeClamp r.val)=r :=
      Subtype.ext (finite_prefix_time_of_real T r.val hT r.property le_top)
    simpa only [hp] using hh
  have hadd : Integrable (fun w => ξ w i + ∫ s in 0..r.val,(A s (X w (projIcc 0 T hT s))) i) P := hxi.add hi
  rw [he,integral_add hadd hsum,integral_add hxi hi,hsum0,add_zero,hfi]

end Asakura.Chapter10

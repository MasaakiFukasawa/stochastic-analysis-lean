import Chapter10LinearStateProducts
import Chapter10ProductResidualMartingale

open MeasureTheory Set Filter
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- L2 state paths supply every bound needed to remove the stochastic terms
in the linear-system covariance computation. -/
theorem linear_product_stopped_martingale {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (T : ℝ) (hT : 0≤T) (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)) (hX : MemLp X 2 P)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ s,‖A s‖≤K) (i j : Fin d)
    (q : ℝ → ℝ) (hq : Continuous q)
    (Z : HalfClosedTime → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (he : ∀ r : Icc (0:ℝ) T,∀ᵐ w ∂P,
      X w r i*X w r j=X w ⟨0,le_rfl,hT⟩ i*X w ⟨0,le_rfl,hT⟩ j+
        (∫ s in 0..r.val,X w (projIcc 0 T hT s) j*(A s (X w (projIcc 0 T hT s))) i)+
        (∫ s in 0..r.val,X w (projIcc 0 T hT s) i*(A s (X w (projIcc 0 T hT s))) j)+
        (∫ s in 0..r.val,q s)+Z (realTimeClamp r.val) w) :
    ContinuousMpWitness P F 1 (fun t w => Z (min (realTimeClamp T) t) w) := by
  let U := fun s w => X w (projIcc 0 T hT s)
  have hUc w : Continuous (fun s => U s w) := (X w).continuous.comp continuous_projIcc
  have hAc w : Continuous (fun s => A s (U s w)) := hA.clm_apply (hUc w)
  have hUn w s : ‖U s w‖≤‖X w‖ := (X w).norm_coe_le_norm _
  have hUi k w s : ‖U s w k‖≤‖X w‖ := (norm_le_pi_norm _ k).trans (hUn w s)
  have hAi k w s : ‖(A s (U s w)) k‖≤(K:ℝ)*‖X w‖ := by
    exact (norm_le_pi_norm _ k).trans (((A s).le_opNorm _).trans
      (mul_le_mul (hAK s) (hUn w s) (norm_nonneg _) K.coe_nonneg))
  have hqc : ContinuousOn (fun r => ∫ s in 0..r,q s) (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using intervalIntegral.continuousOn_primitive_interval'
      (hq.intervalIntegrable 0 T) left_mem_uIcc
  obtain ⟨Q,hQ⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hqc
  apply product_residual_stopped_martingale P F hF hle Z hZ
    (fun s w => U s w i) (fun s w => U s w j)
    (fun s w => (A s (U s w)) i) (fun s w => (A s (U s w)) j)
    (fun r => ∫ s in 0..r,q s) T hT
    (fun w => ((continuous_apply i).comp (hUc w)).continuousOn)
    (fun w => ((continuous_apply j).comp (hUc w)).continuousOn)
    (fun w => ((continuous_apply i).comp (hAc w)).continuousOn)
    (fun w => ((continuous_apply j).comp (hAc w)).continuousOn) hqc
    (fun w => ‖X w‖) hX.norm (fun w => norm_nonneg _) K Q K.coe_nonneg hQ
    (fun w s _ => hUi i w s) (fun w s _ => hUi j w s)
    (fun w s _ => hAi i w s) (fun w s _ => hAi j w s)
  intro r hr
  filter_upwards [he ⟨r,hr⟩] with w hw
  have hp s (hs : s∈Icc (0:ℝ) T) : projIcc 0 T hT s=⟨s,hs⟩ :=
    Subtype.ext (by simp [projIcc,hs.1,hs.2])
  dsimp only [U]
  rw [hp r hr,hp 0 ⟨le_rfl,hT⟩]
  linarith

end Asakura.Chapter10

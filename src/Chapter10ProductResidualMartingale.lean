import Chapter10ProductResidualBound
import Chapter10DominatedLocalMartingale
import Chapter5BracketCommonTime

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter8
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The product residual has mean zero under an L2 path bound. This derives
the martingale property rather than postulating it in the covariance ODE. -/
theorem product_residual_stopped_martingale {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (Z : HalfClosedTime → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (X Y G H : ℝ → Ω → ℝ) (c : ℝ → ℝ) (b : ℝ) (hb : 0≤b)
    (hXc : ∀ w,ContinuousOn (fun s => X s w) (Icc 0 b))
    (hYc : ∀ w,ContinuousOn (fun s => Y s w) (Icc 0 b))
    (hGc : ∀ w,ContinuousOn (fun s => G s w) (Icc 0 b))
    (hHc : ∀ w,ContinuousOn (fun s => H s w) (Icc 0 b))
    (hcc : ContinuousOn c (Icc 0 b))
    (K : Ω → ℝ) (hK : MemLp K 2 P) (hK0 : ∀ w,0≤K w)
    (C q : ℝ) (hC : 0≤C) (hc : ∀ s∈Icc 0 b,‖c s‖≤q)
    (hX : ∀ w s,s∈Icc 0 b → ‖X s w‖≤K w)
    (hY : ∀ w s,s∈Icc 0 b → ‖Y s w‖≤K w)
    (hG : ∀ w s,s∈Icc 0 b → ‖G s w‖≤C*K w)
    (hH : ∀ w s,s∈Icc 0 b → ‖H s w‖≤C*K w)
    (he : ∀ r∈Icc 0 b,Z (realTimeClamp r) =ᵐ[P] fun w =>
      X r w*Y r w-X 0 w*Y 0 w-(∫ s in 0..r,Y s w*G s w)-
        (∫ s in 0..r,X s w*H s w)-c r) :
    ContinuousMpWitness P F 1 (fun t w => Z (min (realTimeClamp b) t) w) := by
  letI : Nonempty (Icc (0:ℝ) b) := ⟨⟨0,le_rfl,hb⟩⟩
  let R := fun (r : Icc (0:ℝ) b) w => X r w*Y r w-X 0 w*Y 0 w-
    (∫ s in 0..r.val,Y s w*G s w)-(∫ s in 0..r.val,X s w*H s w)-c r
  have hRc w : Continuous (fun r => R r w) := by
    have hI : ContinuousOn (fun r => ∫ s in 0..r,Y s w*G s w) (Icc 0 b) := by
      simpa only [uIcc_of_le hb,Pi.mul_apply] using intervalIntegral.continuousOn_primitive_interval'
        (((hYc w).mul (hGc w)).intervalIntegrable_of_Icc hb) left_mem_uIcc
    have hJ : ContinuousOn (fun r => ∫ s in 0..r,X s w*H s w) (Icc 0 b) := by
      simpa only [uIcc_of_le hb,Pi.mul_apply] using intervalIntegral.continuousOn_primitive_interval'
        (((hXc w).mul (hHc w)).intervalIntegrable_of_Icc hb) left_mem_uIcc
    exact continuousOn_iff_continuous_restrict.mp
      (((((hXc w).mul (hYc w)).sub continuousOn_const).sub hI).sub hJ |>.sub hcc)
  have hZc w : Continuous (fun r : Icc (0:ℝ) b => Z (realTimeClamp r.val) w) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact ((hZ.path P F w _ (half_real_time_finite r.val)).comp
      real_time_clamp_continuous.continuousAt).comp continuous_subtype_val.continuousAt
  have hcommon := ae_continuous_common_time_equality P
    (fun r : Icc (0:ℝ) b => Z (realTimeClamp r.val)) R
    (ae_of_all _ hZc) (ae_of_all _ hRc) (fun r => he r.val r.property)
  let D := fun w => 2*(K w)^2+2*b*C*(K w)^2+q
  have hDi : Integrable D P :=
    ((hK.integrable_sq.const_mul 2).add (hK.integrable_sq.const_mul (2*b*C))).add (integrable_const q)
  have hbound : ∀ᵐ w ∂P,∀ t,‖Z (min (realTimeClamp b) t) w‖≤D w := by
    filter_upwards [hcommon] with w hw
    intro t
    let r := finitePrefixTime b hb t
    have hp := finite_prefix_time_clamp b hb (T := (⊤:EReal)) le_top t
    rw [←hp,hw r]
    exact product_residual_bound (fun s => X s w) (fun s => Y s w)
      (fun s => G s w) (fun s => H s w) b r.val (K w) C q (c r.val) hb r.property
      (hK0 w) hC (hc _ r.property) (hX w) (hY w) (hG w) (hH w)
  exact finite_dominated_local_martingale P F hF hle Z hZ b hb D hDi hbound

end Asakura.Chapter10

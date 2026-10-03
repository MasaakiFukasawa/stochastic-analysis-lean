import Chapter4BrownianSystem
import Chapter3ContinuousIntegralConstruction
import Chapter7ClockHalfTime

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The logarithmic stock (also after restarting at a deterministic time)
 has the exact constant drift and covariance used by the local PDE proof. -/
theorem affine_brownian_decomposition {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (ξ : Ω → ℝ) (hξ : Measurable[B.F ⊥] ξ) (a σ : ℝ) :
    let A := fun t w => ξ w+a*B.C 0 0 t w
    let M := fun t w => σ*B.W 0 t w
    let X := fun t w => ξ w+a*B.C 0 0 t w+σ*B.W 0 t w
    SemimartingaleDecomposition P B.F X A M ∧
      LocalCovarianceWitness P B.F M M (fun t w => σ^2*B.C 0 0 t w) ∧
      (∀ w r,0≤r → A (realTimeClamp r) w=A ⊥ w+∫ s in 0..r,a) ∧
      (∀ w r,0≤r → σ^2*B.C 0 0 (realTimeClamp r) w=∫ s in 0..r,σ^2) ∧
      (X ⊥=ᵐ[P] ξ) := by
  dsimp only
  have hT : (0:EReal)<⊤ := by simp
  have hCv := covariance_adapted_variation P B.F B.mono B.le (B.martingale 0) (B.martingale 0) (B.cov 0 0)
  have hCc := local_covariance_path_continuous P B.F _ _ _ (B.martingale 0) (B.martingale 0) (B.cov 0 0)
  have hξv := continuous_increasing_adapted_variation hT B.F B.mono (fun _ w => ξ w)
    (fun _ _ => hξ.mono (B.mono bot_le) le_rfl) (fun _ => monotoneOn_const)
    (fun _ _ _ => continuousAt_const)
  have hA := hξv.add (hCv.smul a) B.mono
  have hM := (B.martingale 0).smul P B.F σ
  have hcross : LocalCovarianceWitness P B.F (fun t w => σ*B.W 0 t w) (B.W 0)
      (fun t w => σ*B.C 0 0 t w) := by
    convert (B.cov 0 0).bilinear P B.F B.mono B.le (B.cov 0 0) (σ-1) using 1 <;> funext <;> ring
  have hcov : LocalCovarianceWitness P B.F (fun t w => σ*B.W 0 t w) (fun t w => σ*B.W 0 t w)
      (fun t w => σ^2*B.C 0 0 t w) := by
    convert (hcross.symm P B.F).bilinear P B.F B.mono B.le (hcross.symm P B.F) (σ-1) using 1 <;> funext <;> ring
  have hz : realTimeClamp (T:=(⊤:EReal)) 0=⊥ := by
    apply Subtype.ext
    change (realTimeClamp (T:=(⊤:EReal)) 0:EReal)=0
    simpa only [EReal.coe_zero] using real_time_clamp_eq (T:=(⊤:EReal)) 0 le_rfl le_top
  have hC0 w : B.C 0 0 ⊥ w=0 := by simpa only [hz] using B.diagonal_clock 0 w 0 le_rfl
  refine ⟨⟨hA,hM,fun w t ht => (continuousAt_const.add (continuousAt_const.mul (hCc w t ht))).add
    (continuousAt_const.mul ((B.martingale 0).path P B.F w t ht)),fun _ _ _ => rfl⟩,hcov,?_,?_,?_⟩
  · intro w r hr
    rw [B.diagonal_clock 0 w r hr,hC0,intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul,mul_zero,add_zero]
    ring
  · intro w r hr
    rw [B.diagonal_clock 0 w r hr,intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul]
    ring
  · filter_upwards [(B.martingale 0).initial P B.F] with w hw
    simp only [hC0,hw,Pi.zero_apply,mul_zero,add_zero]

end Asakura.Chapter11

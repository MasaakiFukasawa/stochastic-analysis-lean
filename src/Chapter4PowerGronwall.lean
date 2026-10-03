import Chapter4ScalarPrefixPowerEstimate
import FullAuditChapter4Gronwall

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter3Complete
set_option maxHeartbeats 1600000

noncomputable def momentGrowthRate (R p K : ℝ) : ℝ :=
  (3:ℝ)^(p-1)*(R^(p-1)+bdgUpperMomentConstant p*R^(p/2-1))*K

/-- Replace the prefix-dependent powers by fixed-horizon constants and
apply the manuscript's Gronwall lemma. -/
theorem moment_gronwall_bound (R p K a : ℝ) (hR : 0≤R) (hp : 2≤p) (hK : 0≤K) (ha : 0≤a)
    (u : ℝ → ℝ) (hu : Continuous u) (hup : ∀ r,0≤u r)
    (hb : ∀ t∈Icc 0 R,u t≤(3:ℝ)^(p-1)*(a+
      (t^(p-1)+bdgUpperMomentConstant p*t^(p/2-1))*K*(t+∫ r in 0..t,u r))) :
    u R≤((3:ℝ)^(p-1)*a+momentGrowthRate R p K*R)*Real.exp ((momentGrowthRate R p K+1)*R) := by
  have hp0 : 0<p := by linarith only [hp]
  have hB := (bdg_moment_constants_positive p hp0).1.le
  have hC : 0≤momentGrowthRate R p K := by
    unfold momentGrowthRate
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (add_nonneg
      (Real.rpow_nonneg hR _) (mul_nonneg hB (Real.rpow_nonneg hR _)))) hK
  have hstep t (ht : t∈Icc 0 R) : u t≤((3:ℝ)^(p-1)*a+momentGrowthRate R p K*R)+
      (momentGrowthRate R p K+1)*(∫ r in 0..t,u r) := by
    have hI : 0≤∫ r in 0..t,u r := intervalIntegral.integral_nonneg_of_forall ht.1 hup
    have hrate : (t^(p-1)+bdgUpperMomentConstant p*t^(p/2-1))*K≤
        (R^(p-1)+bdgUpperMomentConstant p*R^(p/2-1))*K := by
      apply mul_le_mul_of_nonneg_right _ hK
      apply add_le_add (Real.rpow_le_rpow ht.1 ht.2 (by linarith only [hp]))
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1 ht.2 (by linarith only [hp])) hB
    have hraw := hb t ht
    have hscaled := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hrate (add_nonneg ht.1 hI))
      (Real.rpow_nonneg (by norm_num : (0:ℝ)≤3) (p-1))
    have hRt := mul_le_mul_of_nonneg_left ht.2 hC
    dsimp only [momentGrowthRate] at hC hRt ⊢
    nlinarith only [hraw,hscaled,hRt,hI]
  exact (ch4_gronwall_global u hu ((3:ℝ)^(p-1)*a+momentGrowthRate R p K*R)
    (momentGrowthRate R p K+1) R (by linarith only [hC]) hR hstep) R ⟨hR,le_rfl⟩

end Asakura.Chapter4

import Chapter4PowerGronwall
import FullAuditChapter4Gronwall

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter3Complete
set_option maxHeartbeats 1600000

noncomputable def vectorMomentGrowthRate (R p K α β δ : ℝ) : ℝ :=
  α*β*(R^(p-1)+δ*bdgUpperMomentConstant p*R^(p/2-1))*K

/-- Replace the prefix-dependent powers by fixed-horizon constants and
apply the manuscript's Gronwall lemma. -/
theorem vector_moment_gronwall_bound (R p K a α β δ : ℝ) (hα : 0≤α) (hβ : 0≤β) (hδ : 0≤δ) (hR : 0≤R) (hp : 2≤p) (hK : 0≤K) (ha : 0≤a)
    (u : ℝ → ℝ) (hu : Continuous u) (hup : ∀ r,0≤u r)
    (hb : ∀ t∈Icc 0 R,u t≤α*(a+β*
      (t^(p-1)+δ*bdgUpperMomentConstant p*t^(p/2-1))*K*(t+∫ r in 0..t,u r))) :
    u R≤(α*a+vectorMomentGrowthRate R p K α β δ*R)*Real.exp ((vectorMomentGrowthRate R p K α β δ+1)*R) := by
  have hp0 : 0<p := by linarith only [hp]
  have hB := (bdg_moment_constants_positive p hp0).1.le
  have hC : 0≤vectorMomentGrowthRate R p K α β δ := by
    unfold vectorMomentGrowthRate
    exact mul_nonneg (mul_nonneg (mul_nonneg hα hβ) (add_nonneg
      (Real.rpow_nonneg hR _) (mul_nonneg (mul_nonneg hδ hB) (Real.rpow_nonneg hR _)))) hK
  have hstep t (ht : t∈Icc 0 R) : u t≤(α*a+vectorMomentGrowthRate R p K α β δ*R)+
      (vectorMomentGrowthRate R p K α β δ+1)*(∫ r in 0..t,u r) := by
    have hI : 0≤∫ r in 0..t,u r := intervalIntegral.integral_nonneg_of_forall ht.1 hup
    have hrate : (t^(p-1)+δ*bdgUpperMomentConstant p*t^(p/2-1))*K≤
        (R^(p-1)+δ*bdgUpperMomentConstant p*R^(p/2-1))*K := by
      apply mul_le_mul_of_nonneg_right _ hK
      apply add_le_add (Real.rpow_le_rpow ht.1 ht.2 (by linarith only [hp]))
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1 ht.2 (by linarith only [hp])) (mul_nonneg hδ hB)
    have hraw := hb t ht
    have hscaled := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hrate (add_nonneg ht.1 hI))
      (mul_nonneg hα hβ)
    have hRt := mul_le_mul_of_nonneg_left ht.2 hC
    dsimp only [vectorMomentGrowthRate] at hC hRt ⊢
    nlinarith only [hraw,hscaled,hRt,hI]
  exact (ch4_gronwall_global u hu (α*a+vectorMomentGrowthRate R p K α β δ*R)
    (vectorMomentGrowthRate R p K α β δ+1) R (by linarith only [hC]) hR hstep) R ⟨hR,le_rfl⟩

end Asakura.Chapter4

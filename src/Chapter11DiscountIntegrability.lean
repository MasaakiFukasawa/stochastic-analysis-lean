import Chapter11ReplicationIntegrability

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Discounting preserves the required integral domains even when the
holdings and short rate are merely measurable. The balance identity, not
boundedness or continuity of H, supplies integrability of r H S. -/
theorem discounting_path_domains
    (R : ℝ) (hR : 0≤R) (H η S V B r : ℝ → ℝ)
    (hHm : Measurable H) (hBm : Measurable B)
    (hB : ContinuousOn B (Icc 0 R)) (hBpos : ∀ t∈Icc 0 R,0<B t)
    (hV : ContinuousOn V (Icc 0 R))
    (hbalance : ∀ t∈Icc 0 R,V t=H t*S t+η t*B t)
    (hr : Integrable r (volume.restrict (Ioc 0 R)))
    (hη : Integrable (fun t => η t*(r t*B t)) (volume.restrict (Ioc 0 R)))
    (α β : Measure ℝ)
    (hα : ∀ᵐ t ∂α,t∈Icc 0 R) (hβ : ∀ᵐ t ∂β,t∈Icc 0 R)
    (hHA : Integrable H α) (hHM : Integrable (fun t => H t^2) β) :
    Integrable (fun t => H t/B t) α ∧
      Integrable (fun t => (H t/B t)^2) β ∧
      Integrable (fun t => H t*r t*S t/B t) (volume.restrict (Ioc 0 R)) := by
  let D := fun t => (B t)⁻¹
  have hD : ContinuousOn D (Icc 0 R) := hB.inv₀ (fun t ht => (hBpos t ht).ne')
  have hDm : Measurable D := hBm.inv
  have hiA := continuous_multiplier_integrable R hR α hα D H hD hDm hHA
  have hiM := continuous_multiplier_integrable R hR β hβ (fun t => D t^2) (fun t => H t^2)
    (hD.pow 2) (hDm.pow_const 2) hHM
  have ht : ∀ᵐ t ∂volume.restrict (Ioc 0 R),t∈Icc 0 R :=
    (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ⟨ht.1.le,ht.2⟩
  have hVm : Measurable (fun t => V (max 0 (min R t))) := by
    have hc := hV.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
      (fun t => ⟨le_max_left _ _,max_le hR (min_le_left _ _)⟩)
    exact hc.measurable
  have hVr : Integrable (fun t => V t*r t) (volume.restrict (Ioc 0 R)) := by
    have hh := continuous_multiplier_integrable R hR _ ht (fun t => V (max 0 (min R t))) r
      (hV.comp (continuous_const.max (continuous_const.min continuous_id)).continuousOn (by
        intro t ht;exact ⟨le_max_left _ _,max_le hR (min_le_left _ _)⟩)) hVm hr
    apply hh.congr
    filter_upwards [ht] with t hti
    rw [min_eq_right hti.2,max_eq_right hti.1]
  have hHS : Integrable (fun t => H t*r t*S t) (volume.restrict (Ioc 0 R)) := by
    apply (hVr.sub hη).congr
    filter_upwards [ht] with t hti
    dsimp only [Pi.sub_apply]
    rw [hbalance t hti]
    ring
  have hiR := continuous_multiplier_integrable R hR _ ht D (fun t => H t*r t*S t) hD hDm hHS
  refine ⟨?_,?_,?_⟩
  · convert hiA using 1
    funext t
    dsimp only [D]
    rw [div_eq_mul_inv,mul_comm]
  · convert hiM using 1
    funext t
    dsimp only [D]
    rw [div_pow,div_eq_mul_inv,inv_pow,mul_comm]
  · convert hiR using 1
    funext t
    dsimp only [D]
    rw [div_eq_mul_inv,mul_comm]

end Asakura.Chapter11

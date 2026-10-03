import Chapter11ReplicationIntegrability

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter5
set_option maxHeartbeats 2000000

/-- The bounded investment ratio gives admissible integral domains for
 actual stock and bank holdings, even though the holdings need not be bounded. -/
theorem investment_holdings_domains (π V S B : ℝ → ℝ)
    (hπ : Measurable π) (R K μ r σ : ℝ) (hR : 0≤R)
    (hb : ∀ t,|π t|≤K) (hV : ContinuousOn V (Icc 0 R)) (hVm : Measurable V)
    (hS : ∀ t,S t≠0) (hB : ∀ t,B t≠0) :
    let H := fun t => π t*V t/S t
    let η := fun t => (1-π t)*V t/B t
    (∀ t,H t*S t+η t*B t=V t) ∧
    Integrable (fun t => H t*(μ*S t)) (volume.restrict (Ioc 0 R)) ∧
    Integrable (fun t => (H t*(σ*S t))^2) (volume.restrict (Ioc 0 R)) ∧
    Integrable (fun t => η t*(r*B t)) (volume.restrict (Ioc 0 R)) ∧
    (∀ t,r*V t+(μ-r)*H t*S t=V t*(r+π t*(μ-r))) ∧
    (∀ t,H t*(σ*S t)=V t*(σ*π t)) := by
  intro H η
  have hπi : Integrable π (volume.restrict (Ioc 0 R)) :=
    Integrable.of_bound hπ.aestronglyMeasurable K (ae_of_all _ fun t => by simpa only [Real.norm_eq_abs] using hb t)
  have hπ2 : Integrable (fun t => π t^2) (volume.restrict (Ioc 0 R)) :=
    Integrable.of_bound (hπ.pow_const 2).aestronglyMeasurable (K^2) (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (π t),hb t,abs_nonneg (π t)])
  have hs : ∀ᵐ t ∂volume.restrict (Ioc 0 R),t∈Icc 0 R :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun t ht => ⟨ht.1.le,ht.2⟩)
  have hi := continuous_multiplier_integrable R hR _ hs V π hV hVm hπi
  have hi2 := continuous_multiplier_integrable R hR _ hs (fun t => V t^2) (fun t => π t^2) (hV.pow 2) (hVm.pow_const 2) hπ2
  have hVi : Integrable V (volume.restrict (Ioc 0 R)) := hV.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have heH t : H t*S t=π t*V t := div_mul_cancel₀ _ (hS t)
  have heη t : η t*B t=(1-π t)*V t := div_mul_cancel₀ _ (hB t)
  have hn t : H t*(σ*S t)=V t*(σ*π t) := by
    calc _=σ*(H t*S t) := by ring
         _=_ := by rw [heH];ring
  refine ⟨?_,?_,?_,?_,?_,hn⟩
  · intro t;rw [heH,heη];ring
  · convert hi.const_mul μ using 1
    funext t
    calc _=μ*(H t*S t) := by ring
         _=_ := by rw [heH];ring
  · convert hi2.const_mul (σ^2) using 1
    funext t
    rw [hn];ring
  · convert (hVi.sub hi).const_mul r using 1
    funext t
    calc _=r*(η t*B t) := by ring
         _=_ := by rw [heη];simp only [Pi.sub_apply];ring
  · intro t
    calc _=r*V t+(μ-r)*(H t*S t) := by ring
         _=_ := by rw [heH];ring

end Asakura.Chapter11

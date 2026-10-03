import Chapter12FiberwiseClosedGraph

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {S E H V : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ν : Measure S) (A : S → E →L[ℝ] H)
    (J : V →L[ℝ] Lp E 2 ν) (K : V →L[ℝ] Lp H 2 ν)

noncomputable def fiberwiseIdentitySubmodule : Submodule ℝ V where
  carrier := {v | ∀ᵐ t ∂ν,K v t=A t (J v t)}
  zero_mem' := by
    change ∀ᵐ t ∂ν,K 0 t=A t (J 0 t)
    simp only [map_zero]
    filter_upwards [Lp.coeFn_zero H 2 ν,Lp.coeFn_zero E 2 ν] with t ht hu
    simp only [ht,hu,Pi.zero_apply,map_zero]
  add_mem' := by
    intro v w hv hw
    change ∀ᵐ t ∂ν,K (v+w) t=A t (J (v+w) t)
    simp only [map_add]
    filter_upwards [hv,hw,Lp.coeFn_add (K v) (K w),Lp.coeFn_add (J v) (J w)] with t ht hu hk hj
    rw [hk,hj,Pi.add_apply,Pi.add_apply,map_add,ht,hu]
  smul_mem' := by
    intro a v hv
    change ∀ᵐ t ∂ν,K (a • v) t=A t (J (a • v) t)
    simp only [map_smul]
    filter_upwards [hv,Lp.coeFn_smul a (K v),Lp.coeFn_smul a (J v)] with t ht hk hj
    rw [hk,hj,Pi.smul_apply,Pi.smul_apply,map_smul,ht]

theorem fiberwiseIdentitySubmodule_isClosed :
    IsClosed (fiberwiseIdentitySubmodule ν A J K : Set V) := by
  apply isSeqClosed_iff_isClosed.mp
  intro v x hv hx
  exact fiberwise_linear_identity_limit ν A (fun n => J (v n)) (fun n => K (v n)) (J x) (K x)
    (J.continuous.continuousAt.tendsto.comp hx) (K.continuous.continuousAt.tendsto.comp hx) hv

end Asakura.Chapter12

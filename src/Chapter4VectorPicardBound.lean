import Chapter4VectorDriftDifference
import Chapter4VectorNoiseDifference
import Chapter4VectorDifferenceAssembly

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Vector Picard estimate from the actual drift and Ito representations. -/
theorem vector_picard_difference_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (R L : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j))
    (hμLip : ∀ i x y,(μ i x-μ i y)^2≤L*‖x-y‖^2)
    (hσLip : ∀ i j x y,(σ i j x-σ i j y)^2≤L*‖x-y‖^2)
    (Y₁ Y₂ V : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ))
    (hm₁ : Measurable[m] Y₁) (hm₂ : Measurable[m] Y₂) (hv : Measurable[m] V)
    (hi₁ : MemLp Y₁ 2 P) (hi₂ : MemLp Y₂ 2 P)
    (H N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hHa : ∀ i j t,t<⊤ → Measurable[F t] (H i j t))
    (hHc : ∀ i j w t,t<⊤ → ContinuousAt (fun s => H i j s w) t)
    (hN : ∀ i j,LocalMProcessWitness P F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P F (W j) (fun z => H i j (realTimeClamp z.2) z.1) (N i j))
    (hH : ∀ i j w r,r∈Icc 0 R → H i j (realTimeClamp r) w=
      σ i j (Y₁ w (projIcc 0 R hR r))-σ i j (Y₂ w (projIcc 0 R hR r)))
    (he : ∀ᵐ w ∂P,∀ t i,V w t i=
      (∫ r in 0..t.val,(μ i (Y₁ w (projIcc 0 R hR r))-μ i (Y₂ w (projIcc 0 R hR r))))+
      ∑ j,N i j (realTimeClamp t.val) w) :
    MemLp V 2 P ∧ (∫ w,‖V w‖^2 ∂P)≤
      ((dim:ℝ)*(2*R+8*(noise:ℝ)^2)*L)*
        (∫ r in 0..R,(∫ w,‖prefixPath hR (Y₁ w-Y₂ w) r‖^2 ∂P)) := by
  classical
  letI : MeasurableSpace Ω := m
  have hh i j := noise_difference_path_moment P hT F hF hle hnull (W j) (C j) (H i j) (N i j)
    (hW j) (hC j) (hclock j) (hHa i j) (hHc i j) (hN i j) (hNI i j)
    R L hR hRT hL (σ i j) (hσ i j) (hσLip i j) Y₁ Y₂ hm₁ hm₂ hi₁ hi₂ (hH i j)
  choose hc hzi hzb using hh
  let Z := fun i j => finiteRealPath (N i j) R (hc i j)
  have hzm i j : Measurable[m] (Z i j) :=
    finite_real_path_measurable F hle (N i j) R hRT (hc i j) ((hN i j).adapted P F)
  let A := fun i w => coordinateRealPath (V w) i-∑ j,Z i j w
  have ham i : Measurable[m] (A i) := (coordinate_path_measurable V hv i).sub
    (Finset.measurable_sum Finset.univ (fun j _ => hzm i j))
  have har i : ∀ᵐ w ∂P,∀ t,A i w t=∫ r in 0..t.val,
      (μ i (Y₁ w (projIcc 0 R hR r))-μ i (Y₂ w (projIcc 0 R hR r))) := by
    filter_upwards [he] with w hw
    intro t
    change V w t i-(∑ j,Z i j w) t=_
    simp only [ContinuousMap.sum_apply,Z,finiteRealPath,ContinuousMap.coe_mk,hw]
    ring
  have hd i := drift_difference_path_moment P R L hR hL (μ i) (hμ i) (hμLip i)
    Y₁ Y₂ hm₁ hm₂ hi₁ hi₂ (A i) (ham i).aestronglyMeasurable (har i)
  obtain ⟨hi,hb⟩ := coordinate_estimates_assemble P V hv A Z (fun i => (hd i).1) hzi
    _ _ (fun i => (hd i).2) hzb
    (fun i => .of_forall (fun w => by dsimp only [A]; exact (sub_add_cancel _ _).symm))
  refine ⟨hi,hb.trans_eq ?_⟩
  ring

end Asakura.Chapter4.Vector

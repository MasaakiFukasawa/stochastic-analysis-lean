import Chapter8ContractiveFlowInvariant
import Chapter8SDEFlowCommutation
import Chapter8CanonicalSDEContraction
import Chapter8SDERealPathData
import Chapter8LipschitzGrowthData
import Chapter4DeterministicSDEFamily

open MeasureTheory Set
open scoped NNReal BigOperators RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The invariant distribution, uniqueness and geometric convergence are
constructed from the actual additive SDE and strong monotonicity. -/
theorem langevin_invariant_manuscript {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E) (g : (Fin d → ℝ) → (Fin d → ℝ))
    (K : ℝ≥0) (hg : LipschitzWith K g) (σ : Fin d → Fin n → ℝ)
    (κ : ℝ) (hκ : 0<κ)
    (hm : ∀ x y,κ*‖e x-e y‖^2≤⟪e x-e y,e (g x)-e (g y)⟫) :
    ∃ (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
      (F : ℝ → E → Ω → E) (π : Measure E),
      (∀ x,VectorSDESolution P B.F B.W (fun i y => -(g y i))
        (fun i j _ => σ i j) (fun _ => x) (Z x)) ∧
      (∀ t≥0,Measurable (Function.uncurry (F t))) ∧
      (∀ t≥0,∀ x,(fun w => F t (e x) w)=ᵐ[P] fun w => e (Z x (realTimeClamp t) w)) ∧
      IsProbabilityMeasure π ∧ MemLp (fun x : E => x) 2 π ∧
      (∀ t≥0,flowLaw π P (F t)=π) ∧
      (∀ (μ : Measure E),IsProbabilityMeasure μ → MemLp (fun x : E => x) 2 μ →
        ∀ t≥0,transportDistance (flowLaw μ P (F t)) π≤Real.exp (-κ*t)*transportDistance μ π) ∧
      (∀ (ν : Measure E),IsProbabilityMeasure ν → MemLp (fun x : E => x) 2 ν →
        flowLaw ν P (F 1)=ν → ν=π) := by
  let L : ℝ := (d:ℝ)*(K:ℝ)^2
  have hL : 0≤L := by dsimp [L]; positivity
  have hLip : ∀ x y,(∑ i,(-(g x i)- -(g y i))^2)+
      (∑ i : Fin d,∑ j : Fin n,(σ i j-σ i j)^2)≤L*∑ i,(x i-y i)^2 := by
    intro x y
    simpa only [sub_self,zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero,Pi.neg_apply,L]
      using lipschitz_square_coordinates (fun x => -g x) K hg.neg x y
  obtain ⟨Z,hZ⟩ := deterministic_sde_family_exists P B L hL
    (fun i y => -(g y i)) (fun i j _ => σ i j) hLip
  have hex (t : ℝ≥0) := canonical_sde_endpoint_contraction P B e g K hg σ κ hm Z hZ t t.coe_nonneg
  choose A hAm hAr hAc using hex
  let r := fun t : ℝ => (⟨max 0 t,le_max_left _ _⟩ : ℝ≥0)
  let F := fun t y w => e (A (r t) (e.symm y,w))
  have hFm t (ht : 0≤t) : Measurable (Function.uncurry (F t)) :=
    e.continuous.measurable.comp ((hAm (r t)).comp
      ((e.symm.continuous.measurable.comp measurable_fst).prodMk measurable_snd))
  have hFr t (ht : 0≤t) x :
      (fun w => F t (e x) w)=ᵐ[P] fun w => e (Z x (realTimeClamp t) w) := by
    filter_upwards [hAr (r t) x] with w hw
    change A (r t) (x,w)=Z x (realTimeClamp (max 0 t)) w at hw
    simpa only [F,e.symm_apply_apply,max_eq_right ht] using congrArg e hw
  have hF0 t (ht : 0≤t) : MemLp (F t 0) 2 P := by
    have hz := (sde_real_path_data P B L hL (fun i y => -(g y i))
      (fun i j _ => σ i j) hLip (fun _ => (0 : Fin d → ℝ)) (memLp_const 0) (Z 0) (hZ 0)).2.2.1 t
    have hh := e.toContinuousLinearMap.comp_memLp' hz
    apply hh.ae_eq
    filter_upwards [hFr t ht 0] with w hw
    simpa only [max_eq_right ht,map_zero,ContinuousLinearEquiv.coe_coe,Function.comp_apply] using hw.symm
  have hFc t (ht : 0≤t) w x y :
      ‖F t x w-F t y w‖≤Real.exp (-κ*t)*‖x-y‖ := by
    have hh := hAc (r t) w (e.symm x) (e.symm y)
    change ‖F t x w-F t y w‖≤Real.exp (-κ*(max 0 t))*‖e (e.symm x)-e (e.symm y)‖ at hh
    simpa only [max_eq_right ht,e.apply_symm_apply] using hh
  have hcomm (μ : Measure E) (hp : IsProbabilityMeasure μ)
      (_ : MemLp (fun x : E => x) 2 μ) t (ht : 0≤t) :
      flowLaw (flowLaw μ P (F t)) P (F 1)=flowLaw (flowLaw μ P (F 1)) P (F t) := by
    letI := hp
    exact sde_flow_commutation P B e L hL (fun i y => -(g y i))
      (fun i j _ => σ i j) hLip Z hZ F hFm hFr μ 1 t (by norm_num) ht
  obtain ⟨π,hπ⟩ := contractive_flow_invariant P F hFm hF0 κ hκ hFc hcomm
  exact ⟨Z,F,π,hZ,hFm,hFr,hπ⟩

end Asakura.Chapter8

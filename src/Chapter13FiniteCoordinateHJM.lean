import Chapter13HJMPrimitive

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The finite-coordinate form connects the Brownian coefficient
construction directly to the maturity differentiation in the manuscript. -/
theorem finite_coordinate_hjm_drift {d:ℕ} (a:ℝ → ℝ) (σ:Fin d → ℝ → ℝ)
    (ha:LocallyIntegrable a volume) (hσ:∀i,LocallyIntegrable (σ i) volume)
    (he:∀u:ℚ,∫s in 0..(u:ℝ),a s=(∑i,(∫s in 0..(u:ℝ),σ i s)^2)/2) :
    (∀u:ℝ,∫s in 0..u,a s=(∑i,(∫s in 0..u,σ i s)^2)/2) ∧
    (∀ᵐu∂volume,a u=∑i,σ i u*(∫s in 0..u,σ i s)) := by
  have hca:Continuous (fun u => ∫s in 0..u,a s) :=
    intervalIntegral.continuous_primitive (fun x y => intervalIntegrable_iff.mpr ((ha.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)) 0
  have hcs i:Continuous (fun u => ∫s in 0..u,σ i s) :=
    intervalIntegral.continuous_primitive (fun x y => intervalIntegrable_iff.mpr (((hσ i).integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)) 0
  have hc:Continuous (fun u => (∑i,(∫s in 0..u,σ i s)^2)/2) :=
    (continuous_finsetSum _ (fun i _ => (hcs i).pow 2)).div_const 2
  have hf:(fun u => ∫s in 0..u,a s)=(fun u => (∑i,(∫s in 0..u,σ i s)^2)/2) :=
    Rat.isDenseEmbedding_coe_real.dense.equalizer hca hc (funext he)
  refine ⟨congrFun hf,?_⟩
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral ha,
    ae_all_iff.mpr (fun i => _root_.LocallyIntegrable.ae_hasDerivAt_integral (hσ i))] with u hu hs
  have hd:HasDerivAt (fun v => (∑i,(∫s in 0..v,σ i s)^2)/2)
      ((∑i,2*(∫s in 0..u,σ i s)*σ i u)/2) u := by
    convert (HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => (hs i 0).pow 2)).div_const 2 using 1 <;> simp
  have hd0:=hu 0
  rw [hf] at hd0
  have hh:=hd0.unique hd
  rw [hh]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring
end Asakura.Chapter13
#print axioms Asakura.Chapter13.finite_coordinate_hjm_drift

import Chapter13FiniteCoordinateHJM
import FullAuditBVClamp

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.EndToEnd
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false

/-- The countable-maturity argument on the actual finite, positive maturity
interval, with no hypotheses about negative maturities. -/
theorem finite_maturity_drift {d : ℕ} (U : ℝ) (hU : 0≤U)
    (a : ℝ → ℝ) (σ : Fin d → ℝ → ℝ)
    (ha : IntervalIntegrable a volume 0 U) (hσ : ∀ i,IntervalIntegrable (σ i) volume 0 U)
    (he : ∀ q : ℚ, ∫s in 0..intervalClamp 0 U hU q,a s =
      (∑i,(∫s in 0..intervalClamp 0 U hU q,σ i s)^2)/2) :
    (∀ u∈Icc 0 U, ∫s in 0..u,a s=(∑i,(∫s in 0..u,σ i s)^2)/2) ∧
    (∀ᵐ u ∂volume,u∈Ioo 0 U → a u=∑i,σ i u*(∫s in 0..u,σ i s)) := by
  have hca : ContinuousOn (fun u => ∫s in 0..u,a s) (Icc 0 U) := by
    simpa only [uIcc_of_le hU] using intervalIntegral.continuousOn_primitive_interval' ha left_mem_uIcc
  have hcs i : ContinuousOn (fun u => ∫s in 0..u,σ i s) (Icc 0 U) := by
    simpa only [uIcc_of_le hU] using intervalIntegral.continuousOn_primitive_interval' (hσ i) left_mem_uIcc
  have hFa := hca.comp_continuous (intervalClamp_continuous 0 U hU) (intervalClamp_mem 0 U hU)
  have hFs i := (hcs i).comp_continuous (intervalClamp_continuous 0 U hU) (intervalClamp_mem 0 U hU)
  have hF : (fun u => ∫s in 0..intervalClamp 0 U hU u,a s) =
      (fun u => (∑i,(∫s in 0..intervalClamp 0 U hU u,σ i s)^2)/2) :=
    Rat.isDenseEmbedding_coe_real.dense.equalizer hFa
      ((continuous_finsetSum _ (fun i _ => (hFs i).pow 2)).div_const 2) (funext he)
  have hall u (hu : u∈Icc 0 U) : ∫s in 0..u,a s=(∑i,(∫s in 0..u,σ i s)^2)/2 := by
    simpa only [intervalClamp_eq 0 U hU hu] using congrFun hF u
  refine ⟨hall,?_⟩
  filter_upwards [ha.ae_hasDerivAt_integral,
    ae_all_iff.mpr (fun i => (hσ i).ae_hasDerivAt_integral)] with u hu hs
  intro hui
  have hui' : u∈uIcc 0 U := by simpa only [uIcc_of_le hU] using Ioo_subset_Icc_self hui
  have h0 : (0:ℝ)∈uIcc 0 U := left_mem_uIcc
  have hlocal : (fun v => ∫s in 0..v,a s)=ᶠ[𝓝 u]
      (fun v => (∑i,(∫s in 0..v,σ i s)^2)/2) := by
    filter_upwards [Ioo_mem_nhds hui.1 hui.2] with v hv
    exact hall v (Ioo_subset_Icc_self hv)
  have hd : HasDerivAt (fun v => (∑i,(∫s in 0..v,σ i s)^2)/2)
      ((∑i,2*(∫s in 0..u,σ i s)*σ i u)/2) u := by
    convert (HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => (hs i hui' 0 h0).pow 2)).div_const 2 using 1 <;> simp
  have hh := ((hu hui' 0 h0).congr_of_eventuallyEq hlocal.symm).unique hd
  rw [hh,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms finite_maturity_drift
end Asakura.EndToEnd

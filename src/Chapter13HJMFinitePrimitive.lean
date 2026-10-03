import Chapter13HJMPrimitive

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter13
set_option maxHeartbeats 1800000

/-- Maturity differentiation on a finite positive interval; no extension of
coefficients to negative maturities and no continuity of the coefficients. -/
theorem hjm_drift_from_finite_primitive {E:Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ:ℝ → ℝ) (σ:ℝ → E) (R:ℝ) (hR:0≤R)
    (hμ:IntervalIntegrable μ volume 0 R) (hσ:IntervalIntegrable σ volume 0 R)
    (he:∀u∈Icc 0 R,∫s in 0..u,μ s=‖∫s in 0..u,σ s‖^2/2) :
    ∀ᵐu∂volume,u∈Ioo 0 R → μ u=inner ℝ (σ u) (∫s in 0..u,σ s) := by
  filter_upwards [_root_.IntervalIntegrable.ae_hasDerivAt_integral hμ,
    _root_.IntervalIntegrable.ae_hasDerivAt_integral hσ] with u hm hs
  intro hu
  have hui:u∈uIcc 0 R := by simpa only [uIcc_of_le hR] using Ioo_subset_Icc_self hu
  have hz:(0:ℝ)∈uIcc 0 R := by simp [uIcc_of_le hR,hR]
  have hevent:(fun x => ∫s in 0..x,μ s)=ᶠ[𝓝 u]
      (fun x => inner ℝ (∫s in 0..x,σ s) (∫s in 0..x,σ s)/2) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
    rw [he x (Ioo_subset_Icc_self hx),real_inner_self_eq_norm_sq]
  have hd:=((hs hui 0 hz).inner ℝ (hs hui 0 hz)).div_const 2
  have hh:=((hm hui 0 hz).congr_of_eventuallyEq hevent.symm).unique hd
  linarith only [hh,real_inner_comm (∫s in 0..u,σ s) (σ u)]

/-- Countably many maturity identities can be imposed on one common event. -/
theorem countable_maturity_common_event {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) (f g:Ω → ℚ → ℝ) (h:∀q,∀ᵐw∂P,f w q=g w q) :
    ∀ᵐw∂P,∀q,f w q=g w q := ae_all_iff.mpr h
end Asakura.Chapter13
#print axioms Asakura.Chapter13.hjm_drift_from_finite_primitive
#print axioms Asakura.Chapter13.countable_maturity_common_event

import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Chapter13HJMAlgebra
import Mathlib.Analysis.InnerProductSpace.Calculus

open MeasureTheory Set Filter
open scoped RealInnerProductSpace
namespace Asakura.Chapter13
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem hjm_drift_from_primitive {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ:ℝ → ℝ) (σ:ℝ → E) (hμ:LocallyIntegrable μ volume) (hσ:LocallyIntegrable σ volume)
    (he:∀u,∫s in 0..u,μ s=‖∫s in 0..u,σ s‖^2/2) :
    ∀ᵐu∂volume,μ u=inner ℝ (σ u) (∫s in 0..u,σ s) := by
  have hf:(fun u => ∫s in 0..u,μ s)=(fun u => inner ℝ (∫s in 0..u,σ s) (∫s in 0..u,σ s)/2) := by
    funext u
    rw [he,real_inner_self_eq_norm_sq]
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hμ,_root_.LocallyIntegrable.ae_hasDerivAt_integral hσ] with u hm hs
  have hd:=((hs 0).inner ℝ (hs 0)).div_const 2
  have hdm:=hm 0
  rw [hf] at hdm
  have hh:=hdm.unique hd
  have hc := real_inner_comm (∫s in 0..u,σ s) (σ u)
  linarith only [hh,hc]

theorem hjm_primitive_from_dense {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ:ℝ → ℝ) (σ:ℝ → E) (hμ:LocallyIntegrable μ volume) (hσ:LocallyIntegrable σ volume)
    (he:∀u:ℚ,∫s in 0..(u:ℝ),μ s=‖∫s in 0..(u:ℝ),σ s‖^2/2) :
    ∀u:ℝ,∫s in 0..u,μ s=‖∫s in 0..u,σ s‖^2/2 := by
  have hcμ:Continuous (fun u => ∫s in 0..u,μ s) := intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_iff.mpr ((hμ.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)) 0
  have hcσ:Continuous (fun u => ∫s in 0..u,σ s) := intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_iff.mpr ((hσ.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)) 0
  have h := Rat.isDenseEmbedding_coe_real.dense.equalizer hcμ ((hcσ.norm.pow 2).div_const 2) (funext he)
  exact congrFun h
end Asakura.Chapter13
#print axioms Asakura.Chapter13.hjm_drift_from_primitive
#print axioms Asakura.Chapter13.hjm_primitive_from_dense

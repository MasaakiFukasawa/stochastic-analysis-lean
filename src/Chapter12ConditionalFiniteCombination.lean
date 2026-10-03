import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem conditional_finite_linear_combination {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (F : MeasurableSpace Ω) (c : ι → ℝ) (X : ι → Ω → ℝ)
    (hX : ∀ i,Integrable (X i) P) :
    P[(fun w => ∑ i,c i*X i w)|F] =ᵐ[P] (fun w => ∑ i,c i*P[X i|F] w) := by
  classical
  have hs := condExp_finsetSum (s := Finset.univ) (fun i _ => (hX i).const_mul (c i)) F
  have hc := ae_all_iff.mpr (fun i => condExp_smul (c i) (X i) F (μ := P))
  have he : (∑ i,(fun w => c i*X i w)) = (fun w => ∑ i,c i*X i w) := by
    funext w
    exact Finset.sum_apply _ _ _
  rw [he] at hs
  filter_upwards [hs,hc] with w hw hh
  rw [hw,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact hh i

end Asakura.Chapter12

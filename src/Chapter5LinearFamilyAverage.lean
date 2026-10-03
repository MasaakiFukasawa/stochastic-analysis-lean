import Chapter5DominatedC2Integral
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Joint C² regularity of an average over linear maps. For the heat
average the parameter is (x,s) and the random map is (x,s) ↦ x+s z. -/
theorem linear_family_average_C2_of_integrable
    {E V Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (ν : Measure Z) [IsProbabilityMeasure ν]
    (L : Z → E →L[ℝ] V) (hL : Continuous L)
    (b : Z → ℝ) (hb : ∀ z,‖L z‖ ≤ b z) (hbi : Integrable b ν) (hb2 : Integrable (fun z => b z^2) ν)
    (f : V → ℝ) (D : V → V →L[ℝ] ℝ) (DD : V → V →L[ℝ] V →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hdd : ∀ x,HasFDerivAt D (DD x) x)
    (hDc : Continuous D) (hDDc : Continuous DD)
    (C K : ℝ) (hD : ∀ x,‖D x‖ ≤ C) (hDD : ∀ x,‖DD x‖ ≤ K)
    (hFi : ∀ p,Integrable (fun z => f (L z p)) ν) :
    ContDiff ℝ 2 (fun p => ∫ z,f (L z p) ∂ν) := by
  have hC : 0 ≤ C := (norm_nonneg (D 0)).trans (hD 0)
  have hK : 0 ≤ K := (norm_nonneg (DD 0)).trans (hDD 0)
  have hb0 z : 0 ≤ b z := (norm_nonneg (L z)).trans (hb z)
  let D1 := fun p z => (D (L z p)).comp (L z)
  let D2 := fun p z => ((ContinuousLinearMap.compL ℝ E V ℝ).flip (L z)).comp ((DD (L z p)).comp (L z))
  have hp z : ‖(ContinuousLinearMap.compL ℝ E V ℝ).flip (L z)‖ ≤ ‖L z‖ := by
    calc
      _ ≤ ‖(ContinuousLinearMap.compL ℝ E V ℝ).flip‖ * ‖L z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1*‖L z‖ := by rw [ContinuousLinearMap.opNorm_flip]; gcongr; exact ContinuousLinearMap.norm_compL_le ℝ E V ℝ
      _ = _ := one_mul _
  apply dominated_integral_C2 ν (fun p z => f (L z p)) D1 D2
    (fun p z => (hd _).comp p (L z).hasFDerivAt) ?_ ?_ ?_ ?_ ?_
    (fun z => C*b z) (fun z => K*b z^2) (hbi.const_mul C) (hb2.const_mul K) ?_ ?_
  · intro p z
    have hh := ((hdd _).comp p (L z).hasFDerivAt).clm_comp (hasFDerivAt_const (L z) p)
    simpa [D1,D2] using hh
  · intro z
    dsimp only [D2]
    fun_prop
  · intro p
    exact hFi p
  · intro p
    exact (show Continuous (D1 p) by dsimp only [D1]; fun_prop).aestronglyMeasurable
  · intro p
    exact (show Continuous (D2 p) by dsimp only [D2]; fun_prop).aestronglyMeasurable
  · intro z p
    calc
      _ ≤ ‖D (L z p)‖ * ‖L z‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C*b z := mul_le_mul (hD _) (hb z) (norm_nonneg _) hC
  · intro z p
    calc
      _ ≤ ‖(ContinuousLinearMap.compL ℝ E V ℝ).flip (L z)‖ * ‖(DD (L z p)).comp (L z)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖L z‖ * (‖DD (L z p)‖ * ‖L z‖) := mul_le_mul (hp z)
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg ((DD (L z p)).comp (L z))) (norm_nonneg (L z))
      _ ≤ b z * (K*b z) := mul_le_mul (hb z)
        (mul_le_mul (hDD _) (hb z) (norm_nonneg _) hK) (by positivity) (hb0 z)
      _ = K*b z^2 := by ring

theorem linear_family_average_C2
    {E V Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    (ν : Measure Z) [IsProbabilityMeasure ν]
    (L : Z → E →L[ℝ] V) (hL : Continuous L)
    (b : Z → ℝ) (hb : ∀ z,‖L z‖ ≤ b z) (hbi : Integrable b ν) (hb2 : Integrable (fun z => b z^2) ν)
    (f : V → ℝ) (D : V → V →L[ℝ] ℝ) (DD : V → V →L[ℝ] V →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hdd : ∀ x,HasFDerivAt D (DD x) x)
    (hDc : Continuous D) (hDDc : Continuous DD)
    (B C K : ℝ) (hf : ∀ x,‖f x‖ ≤ B) (hD : ∀ x,‖D x‖ ≤ C) (hDD : ∀ x,‖DD x‖ ≤ K) :
    ContDiff ℝ 2 (fun p => ∫ z,f (L z p) ∂ν) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  exact linear_family_average_C2_of_integrable ν L hL b hb hbi hb2 f D DD hd hdd hDc hDDc C K hD hDD
    (fun p => Integrable.of_bound (hfc.comp (hL.clm_apply continuous_const)).aestronglyMeasurable B
      (ae_of_all _ fun z => hf _))

end Asakura.Chapter5

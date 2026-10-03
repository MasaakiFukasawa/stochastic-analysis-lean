import Chapter12TerminalTimeKernel
import Chapter12FiniteBrownianBasketCall

open MeasureTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

theorem terminal_direction_matrix_sum (d : ℕ) (T : ℝ) (hT : 0≤T)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) (c : Fin (d+1) → ℝ) (q : ℝ) :
    q • (∑ i,c i • (∑ j,A i j • brownianTimeDirection (j,⟨T,hT,le_rfl⟩))) =
      WithLp.toLp 2 (fun j => (q*(∑ i,c i*A i j)) • finiteTimeIntervalVector T 0 T) := by
  apply PiLp.ext
  intro j
  change brownianCoordinateProjection T j
    (q • (∑ i,c i • (∑ k,A i k • brownianTimeDirection (k,⟨T,hT,le_rfl⟩)))) = _
  simp only [map_smul,map_sum]
  have hp (k : Fin (d+1)) : brownianCoordinateProjection T j
      (brownianTimeDirection (k,⟨T,hT,le_rfl⟩)) =
        if k=j then finiteTimeIntervalVector T 0 T else 0 := by
    change Pi.single (M := fun _ : Fin (d+1) => Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) k (finiteTimeIntervalVector T 0 T) j = _
    by_cases hkj : k=j <;> simp [hkj,Pi.single_apply]
  simp only [hp,smul_ite,smul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,smul_smul]
  rw [←Finset.sum_smul,smul_smul]


theorem basket_terminal_derivative_time {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ) (hT : 0≤T)
    (A : Matrix (Fin (d+1)) (Fin (d+1)) ℝ)
    (c : Fin (d+1) → Ω → ℝ) (hc : ∀ i,Measurable (c i))
    (q : Ω → ℝ) (hq : Measurable q)
    (U : Lp (FiniteWienerHilbert d T) 2 P)
    (hU : (U : Ω → FiniteWienerHilbert d T) =ᵐ[P]
      (fun w => q w • (∑ i,c i w • (∑ j,A i j • brownianTimeDirection (j,⟨T,hT,le_rfl⟩)))))
    (j : Fin (d+1)) :
    (brownianDerivativeTime P T hT U j : Ω × Icc (0:ℝ) T → ℝ) =ᵐ[P.prod (compactTimeMeasure T hT)]
      (fun z => q z.1*(∑ i,c i z.1*A i j)) := by
  apply terminal_brownian_derivative_time P T hT U (fun j w => q w*(∑ i,c i w*A i j))
  · intro i
    exact hq.mul (Finset.measurable_sum _ (fun k _ => (hc k).mul_const _))
  · filter_upwards [hU] with w hw
    rw [hw,terminal_direction_matrix_sum d T hT]

end Asakura.Chapter12

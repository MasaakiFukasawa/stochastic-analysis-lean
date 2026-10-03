import Chapter4ConditionalCharacteristicProduct

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

lemma dual_matrix_expansion {n d : ℕ} (L : (Fin n → Fin d → ℝ) →L[ℝ] ℝ) (x : Fin n → Fin d → ℝ) :
    L x=∑ k,∑ j,L (Pi.single k (Pi.single j 1))*x k j := by
  classical
  have he : x=∑ k,∑ j,x k j • (Pi.single k (Pi.single j (1:ℝ))) := by
    ext a b
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    simp only [Pi.single_apply,ite_apply,Pi.zero_apply]
    simp
  conv_lhs => rw [he]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_smul,smul_eq_mul,mul_comm]

noncomputable def gridNoiseCharacteristic (n d : ℕ) (h : ℝ)
    (L : (Fin n → Fin d → ℝ) →L[ℝ] ℝ) : ℂ :=
  ∏ k,Complex.exp (-(h:ℂ)*((∑ j,(L (Pi.single k (Pi.single j 1)))^2:ℝ):ℂ)/2)

noncomputable def finiteNoiseGrid {Ω : Type*} {d : ℕ}
    (W : Fin d → ℝ → Ω → ℝ) (h : ℝ) (n : ℕ) (w : Ω) (k : Fin n) (j : Fin d) : ℝ :=
  W j (((k:ℕ)+1)*h) w-W j ((k:ℕ)*h) w


end Asakura.Chapter4

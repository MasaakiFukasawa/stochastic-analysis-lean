import Chapter5BrownianIsometry
import Chapter5ItoOrthogonality
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 2000000

/-- Assemble finitely many orthogonal isometries with the sum-of-squares
norm on their domain. -/
theorem orthogonal_sum_linear_isometry
    {ι H E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (I : ι → H →ₗᵢ[ℝ] E)
    (ho : ∀ i j,i ≠ j → ∀ x y,inner ℝ (I i x) (I j y) = 0) :
    ∃ L : PiLp 2 (fun _ : ι => H) →ₗᵢ[ℝ] E,∀ x,L x = ∑ i,I i (x i) := by
  let J : PiLp 2 (fun _ : ι => H) →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i,I i (x i)
      map_add' := by intro x y; simp [PiLp.add_apply,map_add,Finset.sum_add_distrib]
      map_smul' := by intro a x; simp [PiLp.smul_apply,map_smul,Finset.smul_sum] }
  have hs x : ‖J x‖^2 = ‖x‖^2 := by
    change ‖∑ i,I i (x i)‖^2 = ‖x‖^2
    rw [← real_inner_self_eq_norm_sq,sum_inner]
    simp_rw [inner_sum]
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [real_inner_self_eq_norm_sq,(I i).norm_map]
    · intro j _ hji; exact ho i j hji.symm _ _
    · simp
  refine ⟨⟨J,fun x => ?_⟩,fun _ => rfl⟩
  have hh := hs x
  nlinarith [norm_nonneg (J x),norm_nonneg x]

/-- The real L² inner product of actual terminal representatives. -/
theorem terminal_L2_inner
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    inner ℝ (hX.toLp X) (hY.toLp Y) = ∫ w,X w*Y w ∂P := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hX.coeFn_toLp,hY.coeFn_toLp] with w hx hy
  simp only [hx,hy,Real.inner_apply]

end Asakura.Chapter5

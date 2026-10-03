import Chapter8ChangedBrownianPathMoment
import Chapter6StoppedGrowthPathBound

open MeasureTheory Set
open scoped Topology BigOperators NNReal
namespace Asakura.Chapter8
open Asakura.Chapter6 Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- A square-integrable observed path supplies the random bound needed
for the unbounded score integrals, under either probability measure. -/
theorem observed_path_coefficient_envelope {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d n : ℕ} (B : BrownianSystem P d) (R : ℝ) (hR : 0≤R)
    (hX : MemLp (brownianObservedPath P B (ContinuousLinearEquiv.refl ℝ _) 0 R hR) 2 Q)
    (H : Fin n → Fin d → HalfClosedTime → Ω → ℝ) (K : ℝ) (hK : 0≤K)
    (hH : ∀ k w r,r∈Icc 0 R → ‖WithLp.toLp 2 (fun j => H k j (realTimeClamp r) w)‖≤
      K*(1+‖WithLp.toLp 2 (fun j => B.W j (realTimeClamp r) w)‖)) :
    ∃ V : Ω → ℝ,MemLp V 2 Q ∧ (∀ w,0≤V w) ∧
      ∀ k j w r,r∈Icc 0 R → |H k j (realTimeClamp r) w|≤V w := by
  let X := brownianObservedPath P B (ContinuousLinearEquiv.refl ℝ _) 0 R hR
  let V := fun w => K*(1+(d:ℝ)*‖X w‖)
  have hV : MemLp V 2 Q := ((memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 Q).add (hX.norm.const_mul (d:ℝ))).const_mul K
  refine ⟨V,hV,fun w => by dsimp [V]; positivity,?_⟩
  intro k j w r hr
  apply (PiLp.norm_apply_le (WithLp.toLp 2 (fun j => H k j (realTimeClamp r) w)) j).trans
  apply (hH k w r hr).trans
  apply mul_le_mul_of_nonneg_left _ hK
  apply add_le_add le_rfl
  apply (euclidean_norm_le_abs_sum (fun j => B.W j (realTimeClamp r) w)).trans
  calc
    ∑ j,|B.W j (realTimeClamp r) w| ≤ ∑ _j : Fin d,‖X w‖ := by
      apply Finset.sum_le_sum
      intro j _
      have hi := norm_le_pi_norm (X w ⟨r,hr⟩) j
      have hx := ContinuousMap.norm_coe_le_norm (X w) ⟨r,hr⟩
      simpa only [X,brownianObservedPath,ContinuousMap.coe_mk,ContinuousLinearEquiv.refl_apply,zero_add,Real.norm_eq_abs] using hi.trans hx
    _ = (d:ℝ)*‖X w‖ := by simp
end Asakura.Chapter8

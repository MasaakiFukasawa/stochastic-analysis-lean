import Chapter8AdditivePathMap

open Set
namespace Asakura.Chapter8
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- Uniform initial-state Lipschitz estimates give continuity into the
space of continuous paths, not merely continuity at each fixed time. -/
theorem continuous_path_family {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (T C : ℝ) (hC : 0 ≤ C) (X : E → ℝ → F) (hcX : ∀ x,Continuous (X x))
    (hLip : ∀ x y t,t∈Icc 0 T → ‖X x t-X y t‖ ≤ C*‖x-y‖) :
    Continuous (fun x => (⟨fun t : Icc (0:ℝ) T => X x t.val,
      (hcX x).comp continuous_subtype_val⟩ : C(Icc (0:ℝ) T,F))) := by
  apply LipschitzWith.continuous (K := ⟨C,hC⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  change ‖(⟨fun t : Icc (0:ℝ) T => X x t.val,(hcX x).comp continuous_subtype_val⟩ : C(Icc (0:ℝ) T,F))-
    ⟨fun t => X y t.val,(hcX y).comp continuous_subtype_val⟩‖ ≤ C*‖x-y‖
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  exact hLip x y t.val t.property

end Asakura.Chapter8

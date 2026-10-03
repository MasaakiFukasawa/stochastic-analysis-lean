import Mathlib.Analysis.Normed.Lp.PiLp

open scoped BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem banach_array_norm {I E : Type*} [Fintype I] [NormedAddCommGroup E] (f : I → E) :
    ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : I => E))‖=Real.sqrt (∑i,‖f i‖^2) :=
  PiLp.norm_eq_of_L2 _

theorem banach_array_norm_sum {I J E : Type*} [Fintype I] [Fintype J]
    [NormedAddCommGroup E] (f : J → I → E) :
    Real.sqrt (∑i,‖∑j,f j i‖^2)≤∑j,Real.sqrt (∑i,‖f j i‖^2) := by
  classical
  let v : J → PiLp 2 (fun _ : I => E) := fun j => WithLp.toLp 2 (f j)
  have he : WithLp.toLp 2 (fun i => ∑j,f j i)=(∑j,v j) := by
    apply PiLp.ext
    intro i
    simp [v]
  rw [←banach_array_norm,he]
  simpa only [v,banach_array_norm] using norm_sum_le Finset.univ v
theorem banach_array_norm_finset_sum {I J E : Type*} [Fintype I]
    [NormedAddCommGroup E] (s : Finset J) (f : J → I → E) :
    Real.sqrt (∑i,‖∑j∈s,f j i‖^2)≤∑j∈s,Real.sqrt (∑i,‖f j i‖^2) := by
  classical
  let v : J → PiLp 2 (fun _ : I => E) := fun j => WithLp.toLp 2 (f j)
  have he : WithLp.toLp 2 (fun i => ∑j∈s,f j i)=(∑j∈s,v j) := by
    apply PiLp.ext
    intro i
    simp [v]
  rw [←banach_array_norm,he]
  simpa only [v,banach_array_norm] using norm_sum_le s v
end Asakura.Chapter12
#print axioms Asakura.Chapter12.banach_array_norm_sum

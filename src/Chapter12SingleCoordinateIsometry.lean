import Chapter12PiIsometry

open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

noncomputable def singleCoordinateIsometry {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (i : ι) : H →ₗᵢ[ℝ] PiLp 2 (fun _ : ι => H) where
  toFun h := WithLp.toLp 2 (Pi.single i h)
  map_add' := by
    intro x y
    apply PiLp.ext
    intro j
    by_cases hij : i=j <;> simp [PiLp.add_apply,Pi.single_apply,hij]
  map_smul' := by
    intro a x
    apply PiLp.ext
    intro j
    by_cases hij : i=j <;> simp [PiLp.smul_apply,Pi.single_apply,hij]
  norm_map' := fun h => PiLp.norm_single 2 (fun _ : ι => H) i h

end Asakura.Chapter12

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Set Filter
open scoped Topology
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- The stationary scalar Riccati example: an integrating factor proves an
explicit squared-error decay estimate, rather than only inspecting signs. -/
theorem riccati_equilibrium_decay_right (S : ℝ → ℝ) (a k q v : ℝ)
    (hk : 0≤k) (hv : 0≤v) (heq : q-2*a*v-k*v^2=0)
    (hS : ∀ t,0≤t → 0≤S t)
    (hSc : ContinuousOn S (Ici 0))
    (hd : ∀ t,0≤t → HasDerivWithinAt S (q-2*a*S t-k*(S t)^2) (Ici t) t) :
    ∀ t,0≤t → (S t-v)^2 ≤ (S 0-v)^2*Real.exp (-4*a*t) := by
  let f := fun t => Real.exp (4*a*t)*(S t-v)^2
  let g := fun t => -2*k*(S t+v)*(S t-v)^2*Real.exp (4*a*t)
  have hdf (t : ℝ) (ht : 0≤t) : HasDerivWithinAt f (g t) (Ici t) t := by
    have he := (((hasDerivAt_id t).const_mul (4*a)).exp).hasDerivWithinAt.mul
      (((hd t ht).sub_const v).pow 2)
    convert he using 1
    · rfl
    dsimp [g, Pi.pow_apply, id]
    have hq : q=2*a*v+k*v^2 := by linarith
    rw [hq]
    ring
  intro t ht
  have hfc : ContinuousOn f (Icc 0 t) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (((hSc.mono Icc_subset_Ici_self).sub continuousOn_const).pow 2)
  have hh := image_le_of_deriv_right_le_deriv_boundary hfc
    (fun s hs => hdf s hs.1) (B := fun _ => f 0) (B' := fun _ => 0)
    (le_refl _) continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _) (by
      intro s hs
      dsimp [g]
      have hst := hS s hs.1
      have hnon : 0≤2*k*(S s+v)*(S s-v)^2*Real.exp (4*a*s) := by positivity
      nlinarith) (show t∈Icc 0 t from ⟨ht,le_rfl⟩)
  have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-4*a*t)).le
  dsimp [f] at hh'
  rw [← mul_assoc, ← Real.exp_add] at hh'
  have he : -4*a*t+4*a*t=0 := by ring
  simpa [he,mul_comm] using hh'

end Asakura.Chapter10

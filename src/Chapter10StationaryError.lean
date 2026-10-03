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
theorem riccati_equilibrium_decay (S : ℝ → ℝ) (a k q v : ℝ)
    (hk : 0≤k) (hv : 0≤v) (heq : q-2*a*v-k*v^2=0)
    (hS : ∀ t,0≤t → 0≤S t)
    (hd : ∀ t,0≤t → HasDerivAt S (q-2*a*S t-k*(S t)^2) t) :
    ∀ t,0≤t → (S t-v)^2 ≤ (S 0-v)^2*Real.exp (-4*a*t) := by
  let f := fun t => Real.exp (4*a*t)*(S t-v)^2
  let g := fun t => -2*k*(S t+v)*(S t-v)^2*Real.exp (4*a*t)
  have hdf (t : ℝ) (ht : 0≤t) : HasDerivAt f (g t) t := by
    have he := (((hasDerivAt_id t).const_mul (4*a)).exp).mul
      (((hd t ht).sub_const v).pow 2)
    convert he using 1
    · rfl
    dsimp [g, Pi.pow_apply, id]
    have hq : q=2*a*v+k*v^2 := by linarith
    rw [hq]
    ring
  have hmono : AntitoneOn f (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    · intro t ht
      exact (hdf t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hdf t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      dsimp [g]
      have hst := hS t (interior_subset ht)
      have hnon : 0≤2*k*(S t+v)*(S t-v)^2*Real.exp (4*a*t) := by positivity
      nlinarith
  intro t ht
  have hh := hmono (show (0:ℝ)∈Ici 0 from le_refl (0:ℝ)) ht ht
  have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-4*a*t)).le
  dsimp [f] at hh'
  rw [← mul_assoc, ← Real.exp_add] at hh'
  have he : -4*a*t+4*a*t=0 := by ring
  simpa [he,mul_comm] using hh'

end Asakura.Chapter10

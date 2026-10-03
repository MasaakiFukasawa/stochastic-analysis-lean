import Chapter5FrozenQuotient

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

lemma weighted_realization_norm_sq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R β : ℝ) (hR : 0≤R) (hβ : 0≤β)
    (H : Ω × ℝ → ℝ) (hHm : Measurable H)
    (hH : MemLp H 2 (exponentialEnergyMeasure (P.prod (volume.restrict (Ioc 0 R))) β)) :
    ‖hH.toLp H‖^2=∫ w,(∫ r in 0..R,Real.exp (β*r)*H (w,r)^2) ∂P := by
  have hu := (finite_weighted_memLp_two_iff P R hR β hβ H hHm).mp hH
  have hw := (finite_time_weighted_energy P R hR β hβ H hHm hu).1
  rw [weighted_L2_norm_sq]
  have he : (hH.toLp H) =ᵐ[P.prod (volume.restrict (Ioc 0 R))] H :=
    (exponential_energy_ae_iff _ β _).mp hH.coeFn_toLp
  calc
    _ = ∫ z,Real.exp (β*z.2)*H z^2 ∂P.prod (volume.restrict (Ioc 0 R)) := by
      apply integral_congr_ae
      exact he.mono (fun z hz => by dsimp only; rw [hz])
    _ = _ := by
      rw [integral_prod _ hw]
      simp only [intervalIntegral.integral_of_le hR]

end Asakura.Chapter5

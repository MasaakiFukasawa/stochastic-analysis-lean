import Chapter3BDG
import Chapter2CumulativeBound

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The actual p=2 BDG inequality implies square integrability of the
martingale's path maximum from integrability of its bracket. -/
theorem martingale_maximum_memLp_two
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (M Q : ClosedTime T → Ω → ℝ)
    (hM : LocalMProcessWitness P F M) (hQ : LocalCovarianceWitness P F M M Q)
    (u : ClosedTime T) (hu : u < ⊤)
    (hQi : Integrable (Q u) P) (hQ0 : ∀ᵐ w ∂P, 0 ≤ Q u w) :
    MemLp (runningMaximum M (hM.path P F) u) 2 P := by
  have hsm := Real.continuous_sqrt.comp_aestronglyMeasurable hQi.aestronglyMeasurable
  have he : (fun w => Real.sqrt (Q u w)^2) =ᵐ[P] Q u := hQ0.mono fun w hw => Real.sq_sqrt hw
  have hs : MemLp (fun w => Real.sqrt (Q u w)) 2 P :=
    (memLp_two_iff_integrable_sq hsm).mpr (hQi.congr he.symm)
  have hb := (bdg_norms P hT F hF hle hnull M Q hM hQ 2 (by norm_num) u hu).1
  norm_num only [ENNReal.ofReal_ofNat] at hb
  exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs.eLpNorm_lt_top)

/-- A single square-integrable time integral controls every tail integral. -/
theorem tail_time_integral_square_bound (R : ℝ) (hR : 0 ≤ R)
    (f : ℝ → ℝ) (hf : MemLp f 2 (volume.restrict (Ioc 0 R)))
    (t : ℝ) (ht : t ∈ Icc 0 R) :
    (∫ r in t..R, f r)^2 ≤ R*(∫ r in 0..R, f r^2) := by
  have hh := cumulative_integral_square_bound (volume.restrict (Ioc 0 R)) f hf (Ioc t R)
  have hsub : Ioc t R ⊆ Ioc 0 R := Ioc_subset_Ioc_left ht.1
  rw [Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr hsub] at hh
  have hm : (volume.restrict (Ioc 0 R)).real univ = R := by
    simp [Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal hR]
  rw [hm,Real.norm_eq_abs,sq_abs] at hh
  simpa only [intervalIntegral.integral_of_le ht.2,intervalIntegral.integral_of_le hR] using hh

end Asakura.Chapter5

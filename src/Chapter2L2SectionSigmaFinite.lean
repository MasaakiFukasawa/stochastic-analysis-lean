import Chapter2L2RestrictionLift
import Chapter2DominatedL2Convergence

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {E S : Type*} [MeasurableSpace E] [MeasurableSpace S]

/-- The parameter-to-L2 map is strongly measurable for sigma-finite measures.
This proves the measurability bridge used in stochastic Fubini; it does not
assume that L2 itself is separable. -/
theorem stronglyMeasurable_L2_sections
    (ν : Measure S) [SigmaFinite ν] (H : E × S → ℝ) (hH : Measurable H)
    (hLp : ∀ x, MemLp (fun r => H (x,r)) 2 ν) :
    StronglyMeasurable (fun x => (hLp x).toLp (fun r => H (x,r))) := by
  classical
  let B := spanningSets ν
  have hB n : MeasurableSet (B n) := measurableSet_spanningSets ν n
  let Hn (n : ℕ) (x : E) : S → ℝ := (B n).indicator (fun r => H (x,r))
  have hLn n x : MemLp (Hn n x) 2 ν := (hLp x).indicator (hB n)
  have hsm n : StronglyMeasurable (fun x => (hLn n x).toLp (Hn n x)) := by
    letI : IsFiniteMeasure (ν.restrict (B n)) := ⟨by simpa using (measure_spanningSets_lt_top ν n)⟩
    have hf := stronglyMeasurable_L2_sections_finite (ν.restrict (B n)) H hH (fun x => (hLp x).restrict (B n))
    have hc := (l2RestrictLift_isometry ν (B n) (hB n)).continuous.comp_stronglyMeasurable hf
    simpa only [Function.comp_def,l2RestrictLift_toLp] using hc
  apply stronglyMeasurable_of_tendsto atTop hsm
  apply tendsto_pi_nhds.mpr
  intro x
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mpr
  apply dominated_l2_ae_convergence ν _ _ (fun r => H (x,r)) (hLp x)
  · intro n; exact (hLn n x).aestronglyMeasurable
  · exact (hLp x).aestronglyMeasurable
  · intro n; exact ae_of_all _ (fun r => norm_indicator_le_norm_self _ r)
  · exact ae_of_all _ (fun _ => le_rfl)
  · apply ae_of_all
    intro r
    obtain ⟨k,hk⟩ := iUnion_eq_univ_iff.mp (iUnion_spanningSets ν) r
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (indicator_of_mem (spanningSets_mono hn hk) (fun r => H (x,r))).symm

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stronglyMeasurable_L2_sections

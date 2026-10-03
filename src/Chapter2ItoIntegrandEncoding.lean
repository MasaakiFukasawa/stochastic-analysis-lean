import Chapter2ContinuousIntegrand
import Chapter2SignedDensityIdentification

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Values of an integrand outside the actual time domain play no role in
its covariance characterization. Finite-horizon support is proved from the
interval increments, rather than postulated. -/
theorem ItoCovarianceFormula.congr_on_time_domain
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (X Y : ClosedTime T → Ω → ℝ) (H G : Ω × ℝ → ℝ)
    (h : ItoCovarianceFormula P F X H Y)
    (he : ∀ ω (r : ℝ), 0 ≤ r → (r:EReal) < T → H (ω,r) = G (ω,r)) :
    ItoCovarianceFormula P F X G Y := by
  intro N C hN hC
  obtain ⟨D,hD,hd⟩ := h N C hN hC
  refine ⟨D,hD,?_⟩
  intro d hd0 hdT
  obtain ⟨ν,hν,hν0,hνi,hνD⟩ := hd d hd0 hdT
  have heq : ∀ᵐ ω ∂P, (fun r => H (ω,r)) =ᵐ[(ν ω).totalVariation] (fun r => G (ω,r)) := by
    filter_upwards [hν0] with ω h0
    have hr : ν ω = (ν ω).restrict (Iic d) := by
      apply signed_stopped_interval_consistency (fun r => C (realTimeClamp r) ω)
        d d hd0 le_rfl (ν ω) (ν ω) h0 h0
      all_goals
        intro a b ha hab
        simpa only [real_time_clamp_mono.map_min] using hν ω a b ha hab
    have hm : (ν ω).totalVariation = (ν ω).totalVariation.restrict (Iic d) := by
      calc
        _ = (show SignedMeasure ℝ from (ν ω).restrict (Iic d)).totalVariation := congrArg SignedMeasure.totalVariation hr
        _ = _ := signed_totalVariation_restrict _ measurableSet_Iic
    have hup : ∀ᵐ r ∂(ν ω).totalVariation, r ≤ d := by
      rw [hm]
      exact ae_restrict_mem measurableSet_Iic
    have hlo : ∀ᵐ r ∂(ν ω).totalVariation, 0 < r := by
      rw [ae_iff]
      simp only [not_lt]
      change (ν ω).totalVariation (Iic 0) = 0
      exact h0
    filter_upwards [hup,hlo] with r hr hpos
    exact he ω r hpos.le ((EReal.coe_le_coe hr).trans_lt hdT)
  refine ⟨ν,hν,hν0,?_,?_⟩
  · filter_upwards [hνi,heq] with ω hi heω
    exact hi.congr heω
  · filter_upwards [hνD,heq] with ω hDω heω
    exact hDω.trans (signed_integral_congr_of_absolute_continuity _ (ν ω) (by rfl) heω)

/-- A continuous local-time path has a measurable real-time extension.
The extension is chosen only outside [0,T); all original finite-time values
are kept. Thus pathwise measurability in the previous proof adds no
regularity assumption to the manuscript's continuous-integrand exercise. -/
theorem continuous_local_measurable_encoding
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (H : Ω × ℝ → ℝ)
    (hc : ∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∀ ω, ContinuousOn (fun r => H (ω,r)) (Icc 0 b)) :
    ∃ G : Ω × ℝ → ℝ, (∀ ω, Measurable (fun r => G (ω,r))) ∧
      ∀ ω (r : ℝ), 0 ≤ r → (r:EReal) < T → G (ω,r) = H (ω,r) := by
  classical
  obtain ⟨c,hc0,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hex (ω : Ω) : ∃ g : ℝ → ℝ, Measurable g ∧ ∀ n r, r ∈ Icc 0 (c n) → g r = H (ω,r) := by
    let f := fun n r => H (ω,(projIcc 0 (c n) (hc0 n).le r:ℝ))
    have hf n : Measurable (f n) :=
      ((continuousOn_iff_continuous_restrict.mp (hc (c n) (hc0 n).le (hcT n) ω)).comp continuous_projIcc).measurable
    have he n r (hr : r ∈ Icc 0 (c n)) : f n r = H (ω,r) := by
      dsimp only [f]
      rw [projIcc_of_mem (hc0 n).le hr]
    obtain ⟨g,hg,hgf⟩ := exists_measurable_piecewise (fun n => Icc 0 (c n))
      (fun _ => measurableSet_Icc) f hf (fun i j hij r hr => (he i r hr.1).trans (he j r hr.2).symm)
    exact ⟨g,hg,fun n r hr => (hgf n hr).trans (he n r hr)⟩
  choose g hg hge using hex
  refine ⟨fun z => g z.1 z.2,hg,?_⟩
  intro ω r hr hrT
  have hrt : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r:EReal) < T
    rw [real_time_clamp_eq r hr hrT.le]
    exact hrT
  obtain ⟨n,hn⟩ := hcc _ hrt
  have hrn : r ≤ c n := by
    change (realTimeClamp r:EReal) < (realTimeClamp (c n):EReal) at hn
    rw [real_time_clamp_eq r hr hrT.le,real_time_clamp_eq (c n) (hc0 n).le (hcT n).le] at hn
    exact (EReal.coe_lt_coe_iff.mp hn).le
  exact hge ω n r ⟨hr,hrn⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_local_measurable_encoding
#print axioms Asakura.Chapter2Complete.ItoCovarianceFormula.congr_on_time_domain

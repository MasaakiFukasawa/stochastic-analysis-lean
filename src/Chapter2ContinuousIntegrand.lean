import Chapter2ItoCharacterizedConstruction
import Chapter2ItoConstructionChoices
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Continuous adapted integrands are progressive on each finite real-time
prefix. No joint measurability is assumed: measurable continuous-path-valued
maps and the joint evaluation map supply it. -/
theorem continuous_adapted_real_progressive
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (H : Ω × ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (ha : ∀ r ∈ Icc 0 b, Measurable[F (realTimeClamp r)] (fun ω => H (ω,r)))
    (hc : ∀ ω, ContinuousOn (fun r => H (ω,r)) (Icc 0 b)) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H (z.1,z.2.val)) := by
  apply (measurable_progressive_iff _ _).mpr
  intro t
  letI : MeasurableSpace Ω := F (realTimeClamp t.val)
  letI : CompactSpace (Iic t) := isCompact_iff_compactSpace.mp (isClosed_Iic : IsClosed (Iic t)).isCompact
  let f : Ω → C(Iic t,ℝ) := fun ω => ⟨fun r => H (ω,r.val.val),
    (continuousOn_iff_continuous_restrict.mp (hc ω)).comp continuous_subtype_val⟩
  have hf : Measurable f := ContinuousMap.measurable_iff_eval.mpr (fun r =>
    (ha r.val.val r.val.property).mono (hF (real_time_clamp_mono r.property)) le_rfl)
  have he : Continuous (fun z : C(Iic t,ℝ) × Iic t => z.1 z.2) :=
    continuous_fst.eval continuous_snd
  exact he.measurable.comp ((hf.comp measurable_fst).prodMk measurable_snd)

/-- Continuity makes the square integrable against each finite Stieltjes
measure, even when the random mass has no integrable bound. -/
theorem continuous_stieltjes_square_integrable (b : ℝ) (hb : 0 ≤ b)
    (A : ℝ → ℝ) (hA : MonotoneOn A (Icc 0 b))
    (hr : ∀ r, r ∈ Icc 0 b → ContinuousWithinAt A (Icc 0 b ∩ Ici r) r)
    (H : ℝ → ℝ) (hH : ContinuousOn H (Icc 0 b)) :
    Integrable (fun r => H r^2) (intervalStieltjes 0 b hb A hA hr).measure := by
  let μ := (intervalStieltjes 0 b hb A hA hr).measure
  letI : IsFiniteMeasure μ := intervalStieltjes_finite _ _ _ _ _ _
  have hi : IntegrableOn (fun r => H r^2) (Icc 0 b) μ :=
    (hH.pow 2).integrableOn_compact isCompact_Icc
  have he : μ.restrict (Icc 0 b) = μ := Measure.restrict_eq_self_of_ae_mem
    ((interval_stieltjes_ae_mem_Ioc 0 b hb A hA hr).mono (fun r hr => ⟨hr.1.le,hr.2⟩))
  change Integrable _ (μ.restrict (Icc 0 b)) at hi
  rwa [he] at hi

/-- Construct the Ito integral of an arbitrary continuous adapted integrand
against an actual local martingale. QV and the exhaustion are constructed;
local square integrability is proved from continuity, not assumed. -/
theorem continuous_adapted_ito_exists
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (H : Ω × ℝ → ℝ)
    (ha : ∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun ω => H (ω,r)))
    (hc : ∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∀ ω, ContinuousOn (fun r => H (ω,r)) (Icc 0 b)) :
    ∃ Y : ClosedTime T → Ω → ℝ, LocalMProcessWitness P F Y ∧ ItoCovarianceFormula P F X H Y := by
  obtain ⟨A,hA,hAm,hAc,hA0,hAM⟩ := quadratic_variation_measurable_encoding P hT F hF hle hnull X hX
  obtain ⟨c,hc0,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hbelow n r (hr : r ∈ Icc 0 (c n)) : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r:EReal) < T
    rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans (hcT n).le)]
    exact (EReal.coe_le_coe hr.2).trans_lt (hcT n)
  have hAm' n ω : MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)) :=
    fun s hs t ht hst => hAm ω (hbelow n s hs) (hbelow n t ht) (real_time_clamp_mono hst)
  have hAc' n ω : ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)) :=
    fun r hr => ((hAc ω _ (hbelow n r hr)).comp real_time_clamp_continuous.continuousAt).continuousWithinAt
  apply ito_integral_exists_with_covariance_characterization P hT F hF hle hnull X A hX hA
    c hc0 hcm hcT hct hcut hcc hAm' hAc' H
  · intro n
    exact continuous_adapted_real_progressive F hF H (c n) (hc0 n).le
      (fun r hr => ha r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) (hc (c n) (hc0 n).le (hcT n))
  · intro n
    exact ae_of_all _ (fun ω => continuous_stieltjes_square_integrable (c n) (hc0 n).le _ (hAm' n ω)
      (fun r hr => (hAc' n ω r hr).mono inter_subset_left) _ (hc (c n) (hc0 n).le (hcT n) ω))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_adapted_ito_exists

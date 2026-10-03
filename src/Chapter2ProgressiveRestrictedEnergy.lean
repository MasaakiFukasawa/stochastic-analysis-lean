import Chapter2RandomIntegralMeasurable
import Chapter2ProgressiveSpace
import Chapter2StieltjesRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Local progressive measurability gives both pathwise L2 membership
and measurability of the random energy, even without bounded total mass. -/
theorem progressive_restricted_square_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (b d : ℝ) (hd : 0 ≤ d) (hdb : d ≤ b) (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc 0 b))
    (hc : ∀ ω, ContinuousOn (A ω) (Icc 0 b))
    (hAd : ∀ ω, MonotoneOn (A ω) (Icc 0 d))
    (hcd : ∀ ω, ContinuousOn (A ω) (Icc 0 d))
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (F : ℝ → MeasurableSpace Ω) (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (H : Ω × ℝ → ℝ)
    (hH : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F t.val)) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H (z.1,z.2.val)))
    (hi : ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)^2)
      (intervalStieltjes 0 b (hd.trans hdb) (A ω) (hA ω) (fun r hr => (hc ω r hr).mono inter_subset_left)).measure) :
    (∀ᵐ ω ∂P, MemLp (fun r => H (ω,r)) 2
      (intervalStieltjes 0 d hd (A ω) (hAd ω) (fun r hr => (hcd ω r hr).mono inter_subset_left)).measure) ∧
    Measurable (fun ω => ∫ r, H (ω,r)^2
      ∂(intervalStieltjes 0 d hd (A ω) (hAd ω) (fun r hr => (hcd ω r hr).mono inter_subset_left)).measure) := by
  have hb : 0 ≤ b := hd.trans hdb
  letI : Fact (0 ≤ b) := ⟨hb⟩
  let μ := fun ω => (intervalStieltjes 0 d hd (A ω) (hAd ω)
    (fun r hr => (hcd ω r hr).mono inter_subset_left)).measure
  let q : Ω × ℝ → Ω × Icc (0:ℝ) b := fun z => (z.1,projIcc 0 b hb z.2)
  have hq : Measurable q := measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
  let Hc := fun z : Ω × ℝ => H (z.1,(projIcc 0 b hb z.2:ℝ))
  have hHc : Measurable Hc := (hH.mono
    (progressive_space_le_product (fun t : Icc (0:ℝ) b => F t.val) (fun t => hle t.val)) le_rfl).comp hq
  have he ω : (fun r => Hc (ω,r)) =ᵐ[μ ω] (fun r => H (ω,r)) := by
    filter_upwards [interval_stieltjes_ae_mem_Ioc 0 d hd (A ω) (hAd ω)
      (fun r hr => (hcd ω r hr).mono inter_subset_left)] with r hr
    have hpr : (projIcc 0 b hb r:ℝ) = r := congrArg Subtype.val (projIcc_of_mem hb ⟨hr.1.le,hr.2.trans hdb⟩)
    dsimp only [Hc]
    rw [hpr]
  constructor
  · filter_upwards [hi] with ω hiω
    have hs := (hHc.comp measurable_prodMk_left).aestronglyMeasurable.congr (he ω)
    apply (memLp_two_iff_integrable_sq hs).2
    have hr := interval_stieltjes_restrict_Iic 0 b d hd hdb (A ω) (hA ω)
      (fun r hr => (hc ω r hr).mono inter_subset_left) (hAd ω)
      (fun r hr => (hcd ω r hr).mono inter_subset_left)
    dsimp only [μ]
    rw [hr]
    exact hiω.integrableOn
  · have hmeas := random_stieltjes_integral_measurable 0 d hd A hAd hcd hm
      (fun z => Hc z^2) (hHc.pow_const 2)
    have heq : (fun ω => ∫ r, H (ω,r)^2 ∂μ ω) = fun ω => ∫ r, Hc (ω,r)^2 ∂μ ω := by
      funext ω
      exact integral_congr_ae ((he ω).symm.mono (fun r hr => congrArg (fun x : ℝ => x^2) hr))
    change Measurable (fun ω => ∫ r, H (ω,r)^2 ∂μ ω)
    rw [heq]
    exact hmeas

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.progressive_restricted_square_energy

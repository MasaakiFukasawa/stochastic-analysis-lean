import Chapter2L2SectionSigmaFinite

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {E S : Type*} [MeasurableSpace E] [MeasurableSpace S]

theorem measurable_L2_section_norm
    (ν : Measure S) [SigmaFinite ν] (H : E × S → ℝ) (hH : Measurable H) :
    Measurable (fun x => eLpNorm (fun r => H (x,r)) 2 ν) := by
  have he x := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := ν) (f := fun r => H (x,r))
    (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ∞)
    (hH.comp measurable_prodMk_left).aestronglyMeasurable
  simp_rw [he]
  exact (hH.enorm.pow_const _).lintegral_prod_right.pow_const _

noncomputable def l2Section (ν : Measure S) (H : E × S → ℝ) (x : E) : Lp ℝ 2 ν :=
  if h : MemLp (fun r => H (x,r)) 2 ν then h.toLp (fun r => H (x,r)) else 0

theorem stronglyMeasurable_l2Section
    (ν : Measure S) [SigmaFinite ν] (H : E × S → ℝ) (hH : Measurable H) :
    StronglyMeasurable (l2Section ν H) := by
  classical
  let G := {x | MemLp (fun r => H (x,r)) 2 ν}
  have hG : MeasurableSet G := by
    change MeasurableSet {x | MemLp (fun r => H (x,r)) 2 ν}
    simp only [memLp_iff]
    exact measurableSet_lt (measurable_L2_section_norm ν H hH) measurable_const
  let K : E × S → ℝ := (G ×ˢ univ).indicator H
  have hK : Measurable K := hH.indicator (hG.prod MeasurableSet.univ)
  have hKL x : MemLp (fun r => K (x,r)) 2 ν := by
    by_cases hx : x ∈ G
    · simp only [K,mem_prod,mem_univ,hx,and_self,indicator_of_mem] 
      exact hx
    · simpa [K,hx] using (MemLp.zero : MemLp (0 : S → ℝ) 2 ν)
  have he : l2Section ν H = fun x => (hKL x).toLp (fun r => K (x,r)) := by
    funext x
    by_cases hx : MemLp (fun r => H (x,r)) 2 ν
    · simp only [l2Section,dif_pos hx]
      apply MemLp.toLp_congr
      exact ae_of_all _ (fun r => by simp [K,G,hx])
    · simp only [l2Section,dif_neg hx]
      have hf : (fun r => K (x,r)) = 0 := by funext r; simp [K,G,hx]
      simp only [hf,MemLp.toLp_zero]
  rw [he]
  exact stronglyMeasurable_L2_sections ν K hK hKL

/-- The mixed L1(L2) assumption constructs an integrable L2-valued family;
sections outside L2 are removed only on a parameter-null set. -/
theorem integrable_l2Section
    (μ : Measure E) (ν : Measure S) [SigmaFinite ν]
    (H : E × S → ℝ) (hH : Measurable H)
    (hN : (∫⁻ x, eLpNorm (fun r => H (x,r)) 2 ν ∂μ) < ∞) :
    Integrable (l2Section ν H) μ ∧
      (∀ᵐ x ∂μ, ∃ hx : MemLp (fun r => H (x,r)) 2 ν,
        l2Section ν H x = hx.toLp (fun r => H (x,r))) ∧
      (∫ x, ‖l2Section ν H x‖ ∂μ) =
        ∫ x, (eLpNorm (fun r => H (x,r)) 2 ν).toReal ∂μ := by
  have hm := measurable_L2_section_norm ν H hH
  have hfin : ∀ᵐ x ∂μ, MemLp (fun r => H (x,r)) 2 ν := by
    simpa only [memLp_iff] using ae_lt_top hm hN.ne
  have he : (fun x => ‖l2Section ν H x‖ₑ) =ᵐ[μ] fun x => eLpNorm (fun r => H (x,r)) 2 ν := by
    filter_upwards [hfin] with x hx
    simp only [l2Section,dif_pos hx,Lp.enorm_toLp]
  have hi : Integrable (l2Section ν H) μ := by
    refine ⟨(stronglyMeasurable_l2Section ν H hH).aestronglyMeasurable,?_⟩
    change (∫⁻ x, ‖l2Section ν H x‖ₑ ∂μ) < ∞
    rw [lintegral_congr_ae he]
    exact hN
  refine ⟨hi,hfin.mono (fun x hx => ⟨hx,by simp only [l2Section,dif_pos hx]⟩),?_⟩
  apply integral_congr_ae
  filter_upwards [hfin] with x hx
  simp only [l2Section,dif_pos hx,Lp.norm_toLp]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.integrable_l2Section

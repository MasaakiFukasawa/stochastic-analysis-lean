import Chapter2L2BochnerPointwise

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- All analytic input in the printed mixed-L1(L2) condition: construction
of the Bochner-integrable family, identification of its integral with the
pointwise parameter integral, and the exact Minkowski bound. No separability
of L2 or all-parameter L2 condition is assumed. -/
theorem mixed_l1_l2_fubini_minkowski
    {E S : Type*} [MeasurableSpace E] [MeasurableSpace S]
    (μ : Measure E) [SigmaFinite μ] (ν : Measure S) [SigmaFinite ν]
    (H : E × S → ℝ) (hH : Measurable H)
    (hN : (∫⁻ x, eLpNorm (fun r => H (x,r)) 2 ν ∂μ) < ∞) :
    Integrable (l2Section ν H) μ ∧
      (((∫ x, l2Section ν H x ∂μ : Lp ℝ 2 ν) : S → ℝ)
        =ᵐ[ν] (fun r => ∫ x, H (x,r) ∂μ)) ∧
      MemLp (fun r => ∫ x, H (x,r) ∂μ) 2 ν ∧
      (eLpNorm (fun r => ∫ x, H (x,r) ∂μ) 2 ν).toReal ≤
        ∫ x, (eLpNorm (fun r => H (x,r)) 2 ν).toReal ∂μ := by
  classical
  obtain ⟨hI,hgood,hnorm⟩ := integrable_l2Section μ ν H hH hN
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
  have hKe : (fun x => (hKL x).toLp (fun r => K (x,r))) = l2Section ν H := by
    funext x
    by_cases hx : MemLp (fun r => H (x,r)) 2 ν
    · simp only [l2Section,dif_pos hx]
      apply MemLp.toLp_congr
      exact ae_of_all _ (fun r => by simp [K,G,hx])
    · simp only [l2Section,dif_neg hx]
      have hf : (fun r => K (x,r)) = 0 := by funext r; simp [K,G,hx]
      simp only [hf,MemLp.toLp_zero]
  have hKI : Integrable (fun x => (hKL x).toLp (fun r => K (x,r))) μ := hKe ▸ hI
  have hp := l2_bochner_integral_pointwise μ ν K hK hKL hKI
  rw [hKe] at hp
  have hae : ∀ᵐ x ∂μ, ∀ᵐ r ∂ν, K (x,r) = H (x,r) := by
    filter_upwards [hgood] with x hx
    exact ae_of_all _ (fun r => by simp [K,G,hx.choose])
  have hswap := (Measure.ae_ae_comm (μ := μ) (ν := ν) (measurableSet_eq_fun hK hH)).mp hae
  have hpoint : ((∫ x, l2Section ν H x ∂μ : Lp ℝ 2 ν) : S → ℝ)
      =ᵐ[ν] (fun r => ∫ x, H (x,r) ∂μ) := hp.trans (hswap.mono (fun r hr => integral_congr_ae hr))
  refine ⟨hI,hpoint,(Lp.memLp _).ae_eq hpoint,?_⟩
  rw [← eLpNorm_congr_ae hpoint,← Lp.norm_def,← hnorm]
  exact norm_integral_le_integral_norm _

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.mixed_l1_l2_fubini_minkowski

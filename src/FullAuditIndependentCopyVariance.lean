import FullAuditLangevinContraction
import FullAuditTimeAverageAE

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The independent-copy identity used in the time-average proof, valid for
 Hilbert-valued variables as well as scalar test functions. -/
theorem independent_copy_second_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E)
    (hX : Measurable X) (h2 : MemLp X 2 P) :
    (∫ z : Ω × Ω, ‖X z.1-X z.2‖^2 ∂P.prod P) =
      2*(∫ ω, ‖X ω-(∫ η, X η ∂P)‖^2 ∂P) := by
  let m := ∫ η, X η ∂P
  let Y := fun ω => X ω-m
  have hY : MemLp Y 2 P := h2.sub (memLp_const m)
  have hYi := hY.integrable (by norm_num)
  have hYm : Measurable Y := hX.sub measurable_const
  have hY0 : (∫ ω, Y ω ∂P) = 0 := by
    rw [show Y = (fun ω => X ω-m) from rfl,integral_sub (h2.integrable (by norm_num)) (integrable_const _),
      integral_const,probReal_univ,one_smul]
    exact sub_self m
  have hs : Integrable (fun ω => ‖Y ω‖^2) P := (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mp hY
  have hl : Integrable (fun z : Ω × Ω => ‖Y z.1‖^2) (P.prod P) := by
    simpa only [Function.comp_def] using measurePreserving_fst.integrable_comp_of_integrable hs
  have hr : Integrable (fun z : Ω × Ω => ‖Y z.2‖^2) (P.prod P) := by
    simpa only [Function.comp_def] using measurePreserving_snd.integrable_comp_of_integrable hs
  have hcross : Integrable (fun z : Ω × Ω => ⟪Y z.1,Y z.2⟫_ℝ) (P.prod P) := by
    apply (hYi.norm.mul_prod hYi.norm).mono' (by fun_prop)
    exact ae_of_all _ (fun z => norm_inner_le_norm (Y z.1) (Y z.2))
  have hlaw : (∫ z : Ω × Ω, ‖Y z.1‖^2 ∂P.prod P) = ∫ ω, ‖Y ω‖^2 ∂P := by
    rw [← integral_map (μ := P.prod P) (φ := Prod.fst) (f := fun ω => ‖Y ω‖^2)
      measurable_fst.aemeasurable (by fun_prop),Measure.map_fst_prod,measure_univ,one_smul]
  have hraw : (∫ z : Ω × Ω, ‖Y z.2‖^2 ∂P.prod P) = ∫ ω, ‖Y ω‖^2 ∂P := by
    rw [← integral_map (μ := P.prod P) (φ := Prod.snd) (f := fun ω => ‖Y ω‖^2)
      measurable_snd.aemeasurable (by fun_prop),Measure.map_snd_prod,measure_univ,one_smul]
  have hc0 : (∫ z : Ω × Ω, ⟪Y z.1,Y z.2⟫_ℝ ∂P.prod P) = 0 := by
    rw [integral_prod _ hcross]
    simp_rw [integral_inner hYi,hY0,inner_zero_right]
    exact integral_zero _ _
  have he (z : Ω × Ω) : ‖X z.1-X z.2‖^2 = ‖Y z.1‖^2-2*⟪Y z.1,Y z.2⟫_ℝ+‖Y z.2‖^2 := by
    rw [← norm_sub_sq_real]
    congr 2
    dsimp only [Y]
    abel
  simp_rw [he]
  have hsub : Integrable (fun z : Ω × Ω => ‖Y z.1‖^2-2*⟪Y z.1,Y z.2⟫_ℝ) (P.prod P) := hl.sub (hcross.const_mul 2)
  rw [integral_add hsub hr,integral_sub hl (hcross.const_mul 2),
    integral_const_mul,hlaw,hraw,hc0]
  change (∫ ω, ‖Y ω‖^2 ∂P)-2*0+(∫ ω, ‖Y ω‖^2 ∂P) = 2*(∫ ω, ‖Y ω‖^2 ∂P)
  ring

/-- Apply the independent-copy identity before the Lipschitz inequality,
 exactly as in the manuscript. -/
theorem lipschitz_variance_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure E) [IsProbabilityMeasure P]
    (hP : MemLp (fun x : E => x) 2 P) (f : E → ℝ) (L : ℝ≥0) (hL : LipschitzWith L f)
    (hf : MemLp f 2 P) :
    Var[f; P] ≤ (L:ℝ)^2*(∫ x, ‖x-(∫ y, y ∂P)‖^2 ∂P) := by
  have h1 := independent_copy_second_moment P f hL.continuous.measurable hf
  have h2 := independent_copy_second_moment P (fun x : E => x) measurable_id hP
  have hd : MemLp (fun z : E × E => f z.1-f z.2) 2 (P.prod P) := by
    have hl : MemLp (fun z : E × E => f z.1) 2 (P.prod P) := hf.comp_measurePreserving measurePreserving_fst
    have hr : MemLp (fun z : E × E => f z.2) 2 (P.prod P) := hf.comp_measurePreserving measurePreserving_snd
    exact hl.sub hr
  have hid : Integrable (fun z : E × E => ‖z.1-z.2‖^2) (P.prod P) := by
    have hl : MemLp (fun z : E × E => z.1) 2 (P.prod P) := hP.comp_measurePreserving measurePreserving_fst
    have hr : MemLp (fun z : E × E => z.2) 2 (P.prod P) := hP.comp_measurePreserving measurePreserving_snd
    have hd : MemLp (fun z : E × E => z.1-z.2) 2 (P.prod P) := hl.sub hr
    exact (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd
  have hineq : (∫ z : E × E, ‖f z.1-f z.2‖^2 ∂P.prod P) ≤
      (L:ℝ)^2*(∫ z : E × E, ‖z.1-z.2‖^2 ∂P.prod P) := by
    rw [← integral_const_mul]
    apply integral_mono ((memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd) (hid.const_mul _)
    intro z
    have h := hL.dist_le_mul z.1 z.2
    rw [dist_eq_norm,dist_eq_norm] at h
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [h1,h2] at hineq
  rw [variance_eq_integral hf.aemeasurable]
  simp only [Real.norm_eq_abs,sq_abs] at hineq
  linarith

end Asakura.FullAudit

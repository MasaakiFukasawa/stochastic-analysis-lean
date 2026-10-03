import Chapter12LipschitzLpComposition
import Chapter12VaryingMultiplierLimit
import Chapter12GraphClosure

open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Passing a C1 chain rule along graph-convergent approximations. A
subsequence is extracted only to use dominated convergence on df(F_n). -/
theorem C1_chain_limit_in_closed_graph {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hD : D.IsClosed)
    (F : ℕ → Lp ℝ p P) (U : ℕ → Lp H p P) (F₀ : Lp ℝ p P) (U₀ : Lp H p P)
    (hF : Tendsto F atTop (𝓝 F₀)) (hU : Tendsto U atTop (𝓝 U₀))
    (f df : ℝ → ℝ) (hd : ∀ x, HasDerivAt f (df x) x) (hdc : Continuous df)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |df x| ≤ C)
    (hchain : ∀ n, ∃ hi : MemLp (fun w => df (F n w) • U n w) p P,
      (lipschitzCompositionLp P p (bounded_derivative_lipschitz f df hd C hC hb) (F n),hi.toLp _) ∈ D.graph) :
    ∃ hi : MemLp (fun w => df (F₀ w) • U₀ w) p P,
      (lipschitzCompositionLp P p (bounded_derivative_lipschitz f df hd C hC hb) F₀,hi.toLp _) ∈ D.graph := by
  obtain ⟨ns,hns,hnsAE⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hma n : AEStronglyMeasurable (fun w => df (F (ns n) w)) P :=
    hdc.comp_aestronglyMeasurable (Lp.memLp _).aestronglyMeasurable
  have hmb : AEStronglyMeasurable (fun w => df (F₀ w)) P :=
    hdc.comp_aestronglyMeasurable (Lp.memLp _).aestronglyMeasurable
  have hi : MemLp (fun w => df (F₀ w) • U₀ w) p P := ((Lp.memLp U₀).const_smul C).of_le
    (hmb.smul (Lp.memLp U₀).aestronglyMeasurable) (by
      apply ae_of_all P
      intro w
      change ‖df (F₀ w) • U₀ w‖ ≤ ‖C • U₀ w‖
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hb (F₀ w)) (norm_nonneg (U₀ w)))
  choose hin hgraph using hchain
  have hdiff : Tendsto (fun n => eLpNorm ((U (ns n) : Ω → H)-(U₀ : Ω → H)) p P) atTop (𝓝 0) :=
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hU).comp hns.tendsto_atTop
  have ht := varying_bounded_multiplier_Lp_limit P p (Fact.out : 1 ≤ p) hp
    (fun n => (U (ns n) : Ω → H)) (U₀ : Ω → H) (fun _ => Lp.memLp _) (Lp.memLp _) hdiff
    (fun n w => df (F (ns n) w)) (fun w => df (F₀ w)) hma hmb C hC
    (fun n => ae_of_all P fun w => hb (F (ns n) w)) (ae_of_all P fun w => hb (F₀ w))
    (hnsAE.mono fun w hw => hdc.continuousAt.tendsto.comp hw)
  have hdt : Tendsto (fun n => (hin (ns n)).toLp _) atTop (𝓝 (hi.toLp _)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => hin (ns n)) _ hi).mpr ht
  have hft := (lipschitzCompositionLp_continuous P p
    (bounded_derivative_lipschitz f df hd C hC hb)).continuousAt.tendsto.comp (hF.comp hns.tendsto_atTop)
  exact ⟨hi,hD.mem_of_tendsto (hft.prodMk_nhds hdt) (Eventually.of_forall fun n => hgraph (ns n))⟩

end Asakura.Chapter12

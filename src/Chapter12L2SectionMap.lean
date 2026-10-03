import Chapter12L2Sections

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [SigmaFinite P] (ν : Measure S) [SigmaFinite ν]

noncomputable def l2SectionLp (f : Lp ℝ 2 (P.prod ν)) : Lp (Lp ℝ 2 ν) 2 P :=
  (l2_sections_isometry P ν f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).1.toLp _

theorem l2SectionLp_coe (f : Lp ℝ 2 (P.prod ν)) :
    ∀ᵐ w ∂P, (l2SectionLp P ν f w : S → ℝ) =ᵐ[ν] (fun s => f (w,s)) := by
  obtain ⟨hi,hc,_⟩ := l2_sections_isometry P ν f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
  filter_upwards [hi.coeFn_toLp,hc] with w hw hc
  change (hi.toLp _ w : S → ℝ) =ᵐ[ν] _
  rw [hw]
  exact hc

theorem l2SectionLp_add (f g : Lp ℝ 2 (P.prod ν)) :
    l2SectionLp P ν (f+g) = l2SectionLp P ν f+l2SectionLp P ν g := by
  apply Lp.ext
  filter_upwards [l2SectionLp_coe P ν (f+g),l2SectionLp_coe P ν f,l2SectionLp_coe P ν g,
    Lp.coeFn_add (l2SectionLp P ν f) (l2SectionLp P ν g),
    Measure.ae_ae_of_ae_prod (Lp.coeFn_add f g)] with w hfg hf hg hw hp
  rw [hw,Pi.add_apply]
  apply Lp.ext
  filter_upwards [hfg,hf,hg,hp,Lp.coeFn_add (l2SectionLp P ν f w) (l2SectionLp P ν g w)]
    with s h1 h2 h3 h4 h5
  rw [h1,h4,Pi.add_apply,h5,Pi.add_apply,h2,h3]

theorem l2SectionLp_smul (a : ℝ) (f : Lp ℝ 2 (P.prod ν)) :
    l2SectionLp P ν (a • f) = a • l2SectionLp P ν f := by
  apply Lp.ext
  filter_upwards [l2SectionLp_coe P ν (a • f),l2SectionLp_coe P ν f,
    Lp.coeFn_smul a (l2SectionLp P ν f),Measure.ae_ae_of_ae_prod (Lp.coeFn_smul a f)] with w haf hf hw hp
  rw [hw,Pi.smul_apply]
  apply Lp.ext
  filter_upwards [haf,hf,hp,Lp.coeFn_smul a (l2SectionLp P ν f w)] with s h1 h2 h3 h4
  rw [h1,h3,Pi.smul_apply,h4,Pi.smul_apply,h2]

theorem l2SectionLp_norm (f : Lp ℝ 2 (P.prod ν)) : ‖l2SectionLp P ν f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  obtain ⟨hi,_,hn⟩ := l2_sections_isometry P ν f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
  calc
    _ = ∫ w, ‖l2Section ν f w‖^2 ∂P := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hi.coeFn_toLp] with w hw
      change inner ℝ (hi.toLp _ w) (hi.toLp _ w) = _
      rw [hw,real_inner_self_eq_norm_sq]
    _ = ∫ z, f z^2 ∂P.prod ν := hn
    _ = _ := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by change f z^2 = f z*f z; exact pow_two _)

/-- The actual Fubini map, rather than an assumed identification of spaces. -/
noncomputable def l2SectionsIsometry : Lp ℝ 2 (P.prod ν) →ₗᵢ[ℝ] Lp (Lp ℝ 2 ν) 2 P where
  toFun := l2SectionLp P ν
  map_add' := l2SectionLp_add P ν
  map_smul' := l2SectionLp_smul P ν
  norm_map' := l2SectionLp_norm P ν

end Asakura.Chapter12

import Chapter12L2SectionMap
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Every L2-valued square-integrable random variable has a jointly
measurable realization. Surjectivity is proved using indicator functions
and completeness, not inserted as a Fubini-space identification. -/
theorem l2SectionsIsometry_surjective {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure S) [SigmaFinite ν] :
    Function.Surjective (l2SectionsIsometry P ν) := by
  let J := l2SectionsIsometry P ν
  have hc : IsClosed (range J) := J.isometry.isClosedEmbedding.isClosed_range
  apply Lp.induction (by simp : (2:ℝ≥0∞) ≠ ⊤) (fun f => f ∈ range J) _ _ hc
  · intro h A hA hPA
    let f : Ω × S → ℝ := (A ×ˢ univ).indicator (fun z => h z.2)
    have hi : MemLp f 2 (P.prod ν) := ((Lp.memLp h).comp_snd P).indicator (hA.prod .univ)
    refine ⟨hi.toLp f,?_⟩
    apply Lp.ext
    filter_upwards [l2SectionLp_coe P ν (hi.toLp f),Measure.ae_ae_of_ae_prod hi.coeFn_toLp,
      (indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hPA.ne) (c := h))] with w hw hf ht
    change l2SectionLp P ν (hi.toLp f) w = indicatorConstLp 2 hA hPA.ne h w
    rw [ht]
    by_cases ha : w ∈ A
    · rw [indicator_of_mem ha]
      apply Lp.ext
      filter_upwards [hw,hf] with s hs hfs
      rw [hs,hfs]
      simp only [f,mem_prod,mem_univ,and_true,ha,indicator_of_mem]
    · rw [indicator_of_notMem ha]
      apply Lp.ext
      filter_upwards [hw,hf,Lp.coeFn_zero ℝ 2 ν] with s hs hfs hz
      rw [hs,hfs,hz]
      simp only [f,mem_prod,mem_univ,and_true,ha,not_false_eq_true,indicator_of_notMem,Pi.zero_apply]
  · intro f g hf hg _ hfr hgr
    obtain ⟨u,hu⟩ := hfr
    obtain ⟨v,hv⟩ := hgr
    exact ⟨u+v,by rw [map_add,hu,hv]⟩

noncomputable def l2SectionsEquiv {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure S) [SigmaFinite ν] :
    Lp ℝ 2 (P.prod ν) ≃ₗᵢ[ℝ] Lp (Lp ℝ 2 ν) 2 P :=
  LinearIsometryEquiv.ofSurjective (l2SectionsIsometry P ν) (l2SectionsIsometry_surjective P ν)

end Asakura.Chapter12

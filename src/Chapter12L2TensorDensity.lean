import Chapter12L2SectionSurjective

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem l2_section_indicator_tensor {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure S) [SigmaFinite ν]
    (h : Lp ℝ 2 ν) (A : Set Ω) (hA : MeasurableSet A) (hPA : P A < ⊤) :
    let f : Ω × S → ℝ := (A ×ˢ univ).indicator (fun z => h z.2)
    let hi : MemLp f 2 (P.prod ν) := ((Lp.memLp h).comp_snd P).indicator (hA.prod .univ)
    l2SectionsEquiv P ν (hi.toLp f) = indicatorConstLp 2 hA hPA.ne h := by
  dsimp only
  let f : Ω × S → ℝ := (A ×ˢ univ).indicator (fun z => h z.2)
  have hi : MemLp f 2 (P.prod ν) := ((Lp.memLp h).comp_snd P).indicator (hA.prod .univ)
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

/-- Closed linear subspaces of joint L2 are determined by separated tests. -/
theorem joint_L2_tensor_induction {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure S) [SigmaFinite ν]
    (V : Submodule ℝ (Lp ℝ 2 (P.prod ν))) (hV : IsClosed (V : Set (Lp ℝ 2 (P.prod ν))))
    (htensor : ∀ (h : Lp ℝ 2 ν) (A : Set Ω) (hA : MeasurableSet A) (hPA : P A < ⊤),
      (((Lp.memLp h).comp_snd P).indicator (hA.prod .univ)).toLp
        ((A ×ˢ univ).indicator (fun z => h z.2)) ∈ V) :
    ∀ f : Lp ℝ 2 (P.prod ν),f ∈ V := by
  let J := l2SectionsEquiv P ν
  have hall : ∀ U : Lp (Lp ℝ 2 ν) 2 P,J.symm U ∈ V := by
    apply Lp.induction (by simp : (2:ℝ≥0∞) ≠ ⊤) (fun U => J.symm U ∈ V)
      _ _ (hV.preimage J.symm.continuous)
    · intro h A hA hPA
      have he := l2_section_indicator_tensor P ν h A hA hPA
      have hh := htensor h A hA hPA
      change J.symm (indicatorConstLp 2 hA hPA.ne h) ∈ V
      rw [← he]
      simpa only [J,LinearIsometryEquiv.symm_apply_apply] using hh
    · intro f g hf hg _ hfv hgv
      rw [map_add]
      exact V.add_mem hfv hgv
  intro f
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hall (J f)

end Asakura.Chapter12

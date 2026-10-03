import Chapter12WienerPrefixProcess

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Future Wiener integrals have a jointly continuous-in-time realization
as terminal value minus the single adapted prefix process. -/
theorem coordinate_wiener_future_process {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (J : Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hJ : ∀ (f : ℝ → ℝ) (hm : Measurable f) (hi : MemLp f 2 (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : HalfClosedTime → Ω → ℝ,∃ hN : ContinuousM2Witness P B.F N,
        ItoCovarianceFormula P B.F (B.W i) (fun z => f z.2) N ∧
        J (hi.toLp f)=(hN.moment ⊤).toLp (N ⊤))
    (f : ℝ → ℝ) (hf : Measurable f) (hi : MemLp f 2 (volume.restrict (Ioi (0:ℝ)))) :
    ∃ N : HalfClosedTime → Ω → ℝ,∃ hN : ContinuousM2Witness P B.F N,
      ItoCovarianceFormula P B.F (B.W i) (fun z => f z.2) N ∧
      J (hi.toLp f)=(hN.moment ⊤).toLp (N ⊤) ∧
      ∀ a,0≤a →
        (J ((hi.indicator measurableSet_Ioi).toLp ((Ioi a).indicator f)) : Ω → ℝ)
          =ᵐ[P] fun w => N ⊤ w-N (realTimeClamp a) w := by
  obtain ⟨N,hN,hNI,hJN,hprefix⟩ := coordinate_wiener_prefix_process P B i J hJ f hf hi
  refine ⟨N,hN,hNI,hJN,?_⟩
  intro a ha
  have hid : (hi.indicator measurableSet_Ioi).toLp ((Ioi a).indicator f)=
      hi.toLp f-(hi.indicator measurableSet_Ioc).toLp ((Ioc 0 a).indicator f) := by
    apply Lp.ext
    filter_upwards [(hi.indicator (s := Ioi a) measurableSet_Ioi).coeFn_toLp,
      hi.coeFn_toLp,(hi.indicator (s := Ioc 0 a) measurableSet_Ioc).coeFn_toLp,
      Lp.coeFn_sub (hi.toLp f) ((hi.indicator measurableSet_Ioc).toLp ((Ioc 0 a).indicator f)),
      ae_restrict_mem measurableSet_Ioi] with t hfut hf0 hpast hsub ht0
    rw [hfut,hsub,Pi.sub_apply,hf0,hpast]
    by_cases hta : t≤a
    · rw [indicator_of_notMem (show t ∉ Ioi a from not_lt.mpr hta),
        indicator_of_mem (show t ∈ Ioc 0 a from ⟨ht0,hta⟩)]
      simp
    · rw [indicator_of_mem (show t ∈ Ioi a from lt_of_not_ge hta),
        indicator_of_notMem (show t ∉ Ioc 0 a from fun h => hta h.2)]
      simp
  rw [hid,map_sub,hJN]
  filter_upwards [Lp.coeFn_sub ((hN.moment ⊤).toLp (N ⊤))
    (J ((hi.indicator measurableSet_Ioc).toLp ((Ioc 0 a).indicator f))),
    (hN.moment ⊤).coeFn_toLp,hprefix a ha] with w hsub htop hpre
  rw [hsub,Pi.sub_apply,htop,hpre]

end Asakura.Chapter12
#print axioms Asakura.Chapter12.coordinate_wiener_future_process

import Chapter12SupportedItoTerminal
import Chapter12CanonicalClock

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- All deterministic truncations use one continuous adapted prefix
process, rather than separately chosen conditional-expectation functions. -/
theorem coordinate_wiener_prefix_process {Ω : Type*} [MeasurableSpace Ω]
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
      ∀ a (ha : 0≤a),
        (J ((hi.indicator measurableSet_Ioc).toLp ((Ioc 0 a).indicator f)) : Ω → ℝ)
          =ᵐ[P] N (realTimeClamp a) := by
  obtain ⟨N,hN,hNI,hJN⟩ := hJ f hf hi
  refine ⟨N,hN,hNI,hJN,?_⟩
  intro a ha
  obtain ⟨Z,hZ,hZI,hJZ⟩ := hJ ((Ioc 0 a).indicator f) (hf.indicator measurableSet_Ioc)
    (hi.indicator measurableSet_Ioc)
  obtain ⟨hc,hcm,hct,hcut,hcc,hco⟩ := canonical_clock_properties
  have hlocal (M) (hM : ContinuousM2Witness P B.F M) :=
    continuous_m2_is_local P B.F B.mono B.le
      (fun n => realTimeClamp (T:=⊤) (canonicalClock n)) hct.monotone hcut hcc M hM
  have he := ito_stochastic_interval_identity P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null (B.W i) N Z (fun z => f z.2)
    (B.martingale i) (hlocal N hN) (hlocal Z hZ) (fun _ => hf)
    (fun _ => 0) (fun _ => a) (fun _ => le_rfl) (fun _ => ha) (fun _ => ha)
    (fun t => by by_cases h : realTimeClamp (T:=⊤) 0≤t <;> simp [h])
    (fun t => by by_cases h : realTimeClamp (T:=⊤) a≤t <;> simp [h]) hNI hZI
  have hterminal := supported_ito_terminal_identity P B i a ha f hf Z hZ hZI
  have hat : realTimeClamp (T:=⊤) a<⊤ := by
    change (realTimeClamp a:EReal)<⊤
    rw [real_time_clamp_eq a ha le_top]
    exact EReal.coe_lt_top a
  have hz : realTimeClamp (T:=(⊤:EReal)) 0=⊥ :=
    Subtype.ext (real_time_clamp_eq 0 le_rfl le_top)
  rw [hJZ]
  filter_upwards [(hZ.moment ⊤).coeFn_toLp,hterminal,he,hN.initial] with w hw ht he h0
  rw [hw,ht,he _ hat,min_self,hz,min_bot_left,h0]
  simp

end Asakura.Chapter12
#print axioms Asakura.Chapter12.coordinate_wiener_prefix_process

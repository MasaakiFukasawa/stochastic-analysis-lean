import EndToEndParameterItoConstructed
import EndToEndFiniteCoefficientRepair
import Chapter7ItoCommonIntegrand
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory Set Filter
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

/-- A jointly measurable family of actual Ito integrals on all positive
parameters, constructed using only almost-sure local parameter/time bounds. -/
theorem parameter_ito_global {Ω : Type} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d) (i : Fin d)
    (H : ℝ × (Ω × ℝ) → ℝ) (hm : Measurable H)
    (hp : ∀ b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace ℝ).prod (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z : ℝ × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val))))
    (hb : ∀ᵐw∂P,∀U,0≤U → ∀b,0≤b → ∃K:ℝ,0≤K ∧
      ∀x∈Icc 0 U,∀r∈Icc 0 b,|H (x,(w,r))|≤K) :
    ∃ V : ℝ → HalfClosedTime → Ω → ℝ,
      Measurable (fun z : ℝ × (Ω × HalfClosedTime) => V z.1 z.2.2 z.2.1) ∧
      (∀ x,LocalMProcessWitness P B.F (V x)) ∧
      ∀ᵐx∂volume,0<x → ItoCovarianceFormula P B.F (B.W i) (fun z => H (x,z)) (V x) := by
  have hex (n:ℕ) : ∃V : ℝ → HalfClosedTime → Ω → ℝ,
      Measurable (fun z : ℝ × (Ω × HalfClosedTime) => V z.1 z.2.2 z.2.1) ∧
      (∀ x,LocalMProcessWitness P B.F (V x)) ∧
      ∀ᵐx∂volume.restrict (Ioc 0 ((n:ℝ)+1)),
        ItoCovarianceFormula P B.F (B.W i) (fun z => H (x,z)) (V x) := by
    have hn : 0≤(n:ℝ)+1 := by positivity
    obtain ⟨G,hGm,hGp,hGb,he⟩ := finite_coefficient_repair P B (Icc 0 ((n:ℝ)+1)) measurableSet_Icc H hm hp
      (hb.mono (fun w hw => hw _ hn))
    obtain ⟨V,hVm,hV,hVI⟩ := parameter_ito_constructed P B i (volume.restrict (Ioc 0 ((n:ℝ)+1))) G hGm hGp hGb
    refine ⟨V,hVm,hV,?_⟩
    filter_upwards [hVI,ae_restrict_mem measurableSet_Ioc] with x hx hxi
    apply Asakura.Chapter7.ito_integrand_common_ae P B.F (B.W i) (V x) (fun z => G (x,z)) _ hx
    filter_upwards [he] with w hw
    exact hw x ⟨hxi.1.le,hxi.2⟩
  choose V hVm hV hVI using hex
  let W := fun x => V ⌈x⌉₊ x
  refine ⟨W,?_,fun x => hV _ x,?_⟩
  · have hm : Measurable (fun p : (ℝ × (Ω × HalfClosedTime)) × ℕ => V p.2 p.1.1 p.1.2.2 p.1.2.1) :=
      measurable_from_prod_countable_left hVm
    exact hm.comp (measurable_id.prodMk measurable_fst.nat_ceil)
  · have hi : ∀n:ℕ,∀ᵐx∂volume,x∈Ioc 0 ((n:ℝ)+1) →
        ItoCovarianceFormula P B.F (B.W i) (fun z => H (x,z)) (V n x) :=
      fun n => (ae_restrict_iff' measurableSet_Ioc).mp (hVI n)
    filter_upwards [ae_all_iff.mpr hi] with x hx hxp
    apply hx ⌈x⌉₊
    exact ⟨hxp,(Nat.le_ceil x).trans (by linarith)⟩

#print axioms parameter_ito_global
end Asakura.EndToEnd

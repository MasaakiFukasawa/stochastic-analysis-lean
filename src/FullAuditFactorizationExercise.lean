import FullAuditConditionalExercises
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace Asakura.FullAudit

/-- Factorization is built from constants, measurable simple pieces, and
 their pointwise limits, as suggested in the exercise. The missing measurable
 structure on S is supplied explicitly. No factorization theorem is invoked. -/
theorem measurable_factorization_written {Ω S : Type*} [mS : MeasurableSpace S]
    (G : Ω → S) (X : Ω → ℝ) (hX : Measurable[mS.comap G] X) :
    ∃ φ : S → ℝ, Measurable φ ∧ X = φ ∘ G := by
  have hs := hX.stronglyMeasurable
  suffices ∃ φ : S → ℝ, StronglyMeasurable φ ∧ X = φ ∘ G by
    obtain ⟨φ,hφ,he⟩ := this
    exact ⟨φ,hφ.measurable,he⟩
  letI : MeasurableSpace Ω := mS.comap G
  clear hX
  induction X, hs using StronglyMeasurable.induction' with
  | const c => exact ⟨fun _ => c,stronglyMeasurable_const,rfl⟩
  | @pcw f g A hf hg hA ihf ihg =>
    obtain ⟨B,hB,rfl⟩ := hA
    obtain ⟨φ,hφ,rfl⟩ := ihf
    obtain ⟨ψ,hψ,rfl⟩ := ihg
    classical
    exact ⟨B.piecewise φ ψ,hφ.piecewise hB hψ,by rw [piecewise_comp]⟩
  | @lim f u hu hf ihm ht =>
    choose φ hφ he using ihm
    refine ⟨fun s => limUnder atTop (fun n => φ n s),StronglyMeasurable.limUnder hφ,?_⟩
    funext ω
    rw [Function.comp_apply,Tendsto.limUnder_eq]
    simpa only [he,Function.comp_apply] using ht ω

/-- With the Borel measurable structure the factor is Borel measurable,
 which is the wording used in the corrected exercise. -/
theorem borel_factorization_exercise {Ω S : Type*} [TopologicalSpace S]
    (G : Ω → S) (X : Ω → ℝ) (hX : Measurable[(borel S).comap G] X) :
    ∃ φ : S → ℝ, Measurable[borel S] φ ∧ X = φ ∘ G := by
  letI : MeasurableSpace S := borel S
  exact measurable_factorization_written G X hX

end Asakura.FullAudit

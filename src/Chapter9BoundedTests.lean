import Chapter9ConditionalFubini
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory
namespace Asakura.Chapter9
set_option maxHeartbeats 900000

def IsBoundedBorel {E : Type*} [MeasurableSpace E] (f : E → ℝ) : Prop :=
  Measurable f ∧ ∃ C : ℝ,0≤C ∧ ∀ x,‖f x‖≤C

 theorem IsBoundedBorel.const {E : Type*} [MeasurableSpace E] (c : ℝ) :
    IsBoundedBorel (fun _ : E => c) := ⟨measurable_const,‖c‖,norm_nonneg _,fun _ => le_rfl⟩

 theorem IsBoundedBorel.mul {E : Type*} [MeasurableSpace E] {f g : E → ℝ}
    (hf : IsBoundedBorel f) (hg : IsBoundedBorel g) : IsBoundedBorel (fun x => f x*g x) := by
  obtain ⟨C,hC,hfC⟩ := hf.2
  obtain ⟨D,hD,hgD⟩ := hg.2
  refine ⟨hf.1.mul hg.1,C*D,mul_nonneg hC hD,?_⟩
  intro x
  rw [norm_mul]
  exact mul_le_mul (hfC x) (hgD x) (norm_nonneg _) hC

 theorem IsBoundedBorel.comp {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    {f : E → ℝ} (hf : IsBoundedBorel f) (X : Ω → E) (hX : Measurable X) :
    IsBoundedBorel (fun w => f (X w)) := by
  obtain ⟨C,hC,hfC⟩ := hf.2
  exact ⟨hf.1.comp hX,C,hC,fun w => hfC (X w)⟩

 theorem IsBoundedBorel.integrable {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ℝ} (hf : IsBoundedBorel f) (P : Measure Ω) [IsFiniteMeasure P] : Integrable f P := by
  obtain ⟨C,_,hC⟩ := hf.2
  exact Integrable.of_bound hf.1.aestronglyMeasurable C (ae_of_all _ hC)

noncomputable def finiteTestProduct {ι E Ω : Type*} (X : ι → Ω → E) (f : ι → E → ℝ) : List ι → Ω → ℝ
  | [],_ => 1
  | t::L,w => f t (X t w)*finiteTestProduct X f L w

 theorem finiteTestProduct_bounded {ι E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (X : ι → Ω → E) (hX : ∀ t,Measurable (X t)) (f : ι → E → ℝ)
    (hf : ∀ t,IsBoundedBorel (f t)) (L : List ι) : IsBoundedBorel (finiteTestProduct X f L) := by
  induction L with
  | nil => exact IsBoundedBorel.const 1
  | cons t L ih => exact ((hf t).comp (X t) (hX t)).mul ih
end Asakura.Chapter9

import Chapter4FiniteStepDomain
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4

lemma finite_step_integrand_memLp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (G : ι → Ω → ℝ)
    (hG : ∀ i∈s,MemLp (G i) 2 P) (R : ℝ) :
    MemLp (fun z : Ω × ℝ => ∑ i∈s,(Ioc (a i) (b i)).indicator (fun _ => G i z.1) z.2)
      2 (P.prod (volume.restrict (Ioc 0 R))) := by
  apply memLp_finsetSum
  intro i hi
  have he : (fun z : Ω × ℝ => (Ioc (a i) (b i)).indicator (fun _ => G i z.1) z.2)=
      (Prod.snd ⁻¹' Ioc (a i) (b i)).indicator (fun z => G i z.1) := by
    funext z
    by_cases hz : z.2∈Ioc (a i) (b i) <;> simp [indicator,hz]
  rw [he]
  exact ((hG i hi).comp_fst (volume.restrict (Ioc 0 R))).indicator
    (measurableSet_Ioc.preimage measurable_snd)

end Asakura.Chapter4

import Chapter7QuadraticDegenerate
import Chapter7GridGaussianLimitLaw

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Asakura.Chapter7

lemma distribution_limit_same_law {Ω Γ Δ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Γ] [MeasurableSpace Δ]
    (P : Measure Ω) (Q : Measure Γ) (R : Measure Δ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    {X : ℕ → Ω → ℝ} {Y : Γ → ℝ} {Z : Δ → ℝ} {ν : Measure ℝ}
    (h : TendstoInDistribution X atTop Y (fun _ => P) Q)
    (hY : HasLaw Y ν Q) (hZ : HasLaw Z ν R) :
    TendstoInDistribution X atTop Z (fun _ => P) R := by
  refine ⟨h.forall_aemeasurable,hZ.aemeasurable,?_⟩
  have he : Q.map Y=R.map Z := hY.map_eq.trans hZ.map_eq.symm
  have hp : (⟨Q.map Y,inferInstance⟩ : ProbabilityMeasure ℝ)=⟨R.map Z,inferInstance⟩ := Subtype.ext he
  rw [← hp]
  exact h.tendsto

end Asakura.Chapter7

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Asakura
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma L2_mean_inner (f : Lp ℝ 2 P) :
    (∫ ω, f ω ∂P) = inner ℝ ((memLp_const (1 : ℝ)).toLp (fun _ : Ω => (1 : ℝ))) f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_const (1 : ℝ) (μ := P) (p := 2)).coeFn_toLp] with ω h
  simp [h]

lemma L2_variance_inner (f : Lp ℝ 2 P) :
    Var[f; P] = inner ℝ f f - (∫ ω, f ω ∂P) ^ 2 := by
  rw [variance_eq_sub (Lp.memLp f), L2.inner_def]
  simp [pow_two]

lemma L2_mean_continuous : Continuous (fun f : Lp ℝ 2 P => ∫ ω, f ω ∂P) := by
  simp_rw [L2_mean_inner]
  fun_prop

lemma L2_variance_continuous : Continuous (fun f : Lp ℝ 2 P => Var[f; P]) := by
  simp_rw [L2_variance_inner]
  exact (continuous_id.inner continuous_id).sub (L2_mean_continuous.pow 2)

lemma L2_projected_moments_tendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : ℕ → Lp E 2 P} {g : Lp E 2 P} (h : Tendsto f atTop (𝓝 g)) (t : E) :
    Tendsto (fun n => ∫ ω, inner ℝ t (f n ω) ∂P) atTop
      (𝓝 (∫ ω, inner ℝ t (g ω) ∂P)) ∧
    Tendsto (fun n => Var[fun ω => inner ℝ t (f n ω); P]) atTop
      (𝓝 (Var[fun ω => inner ℝ t (g ω); P])) := by
  let L := innerSL ℝ t
  have he (v : Lp E 2 P) : L.compLp v =ᵐ[P] fun ω => inner ℝ t (v ω) :=
    L.coeFn_compLp v
  have hc := ((L.compLpL (p := 2) (μ := P)).continuous.tendsto g).comp h
  have hm := (L2_mean_continuous.tendsto (L.compLp g)).comp hc
  have hv := (L2_variance_continuous.tendsto (L.compLp g)).comp hc
  have hi (v : Lp E 2 P) := integral_congr_ae (he v)
  have hvar (v : Lp E 2 P) := variance_congr (he v)
  change Tendsto (fun n => ∫ ω, L.compLp (f n) ω ∂P) atTop
    (𝓝 (∫ ω, L.compLp g ω ∂P)) at hm
  change Tendsto (fun n => Var[L.compLp (f n); P]) atTop
    (𝓝 (Var[L.compLp g; P])) at hv
  simpa only [hi, hvar] using And.intro hm hv
end Asakura

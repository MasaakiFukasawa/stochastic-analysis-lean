import Chapter7BrownianQuadraticStatistic

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.Chapter4

lemma matrix_square_sum_zero {d : ℕ} (K : Fin d → Fin d → ℝ)
    (hz : (∑ i,∑ j,(K i j)^2)=0) : ∀ i j,K i j=0 := by
  have hi := (sum_eq_zero_iff_of_nonneg (fun i _ => sum_nonneg (fun j _ => sq_nonneg (K i j)))).mp hz
  intro i j
  exact sq_eq_zero_iff.mp ((sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (K i j))).mp (hi i (mem_univ _)) j (mem_univ _))

lemma brownian_quadratic_statistic_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (K : Fin d → Fin d → ℝ) (hz : (∑ i,∑ j,(K i j)^2)=0) (T : ℝ) (n : ℕ) :
    brownianQuadraticStatistic B K T n=0 := by
  funext w
  simp only [brownianQuadraticStatistic,matrix_square_sum_zero K hz,zero_mul,mul_zero,
    sum_const_zero,sub_zero]
  rfl

lemma brownian_quadratic_statistic_degenerate_clt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (K : Fin d → Fin d → ℝ) (hz : (∑ i,∑ j,(K i j)^2)=0) (T : ℝ) :
    TendstoInDistribution (fun n => brownianQuadraticStatistic B K T (n+1)) atTop
      (fun _ : Ω => (0:ℝ)) (fun _ => P) P := by
  have he : (fun n => brownianQuadraticStatistic B K T (n+1))=(fun (_ : ℕ) (_ : Ω) => (0:ℝ)) := by
    funext n w
    rw [brownian_quadratic_statistic_zero B K hz]
    rfl
  rw [he]
  exact (tendstoInDistribution_const (μ' := P) (l := atTop) (measurable_const.aemeasurable : AEMeasurable (fun _ : Ω => (0:ℝ)) P))

end Asakura.Chapter7

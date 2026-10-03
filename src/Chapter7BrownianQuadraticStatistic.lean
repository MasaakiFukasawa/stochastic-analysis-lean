import Chapter7GridMartingaleCLT
import Chapter7BrownianGridTerminal

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def brownianQuadraticStatistic {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (K : Fin d → Fin d → ℝ) (T : ℝ) (n : ℕ) (w : Ω) : ℝ :=
    (Real.sqrt (n:ℝ)/T)*∑ k : Fin n,
      ((∑ i,∑ j,K i j*(B.W i (realTimeClamp (((k:ℝ)+1)*(T/n))) w-B.W i (realTimeClamp ((k:ℝ)*(T/n))) w)*
        (B.W j (realTimeClamp (((k:ℝ)+1)*(T/n))) w-B.W j (realTimeClamp ((k:ℝ)*(T/n))) w))-(T/n)*(∑ i,K i i))

/-- CLT for the actual centered quadratic statistic of Brownian increments. -/
theorem brownian_quadratic_statistic_clt {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d : ℕ} (B : BrownianSystem P d) (Baux : BrownianSystem Q 1)
    (K : Fin d → Fin d → ℝ) (hKs : ∀ i j,K i j=K j i)
    (T : ℝ) (hT : 0<T) (hK : 0<∑ i,∑ j,(K i j)^2) :
    ∃ B0 : BrownianSystem (P.prod Q) 1,
      TendstoInDistribution (fun n => brownianQuadraticStatistic B K T (n+1)) atTop
        (fun z => Real.sqrt (2*(∑ i,∑ j,(K i j)^2)/T)*B0.W 0 (realTimeClamp T) z) (fun _ => P) (P.prod Q) := by
  obtain ⟨N,B0,hN,hNI,hlim⟩ := brownian_grid_martingale_clt P Q B Baux K T hT hK
  refine ⟨B0,?_⟩
  apply hlim.congr _ (ae_of_all _ (fun _ => rfl))
  intro n
  have he := brownian_grid_terminal_identity P B K hKs T (2*Real.sqrt ((n+1:ℕ):ℝ)/T) hT (n+1)
    (Nat.succ_pos _) (N n) (hN n) (by intro i; simpa only [Nat.cast_add,Nat.cast_one] using hNI n i)
  filter_upwards [he] with w hw
  change (∑ i,N n i (realTimeClamp T) w)=brownianQuadraticStatistic B K T (n+1) w
  dsimp only [brownianQuadraticStatistic]
  apply mul_left_cancel₀ (by norm_num : (2:ℝ)≠0)
  calc
    _ = _ := hw
    _ = _ := by ring

end Asakura.Chapter7

import Chapter12BasketMatrixHedge
import Chapter6VariationAdd

open MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter6
set_option maxHeartbeats 1800000

theorem basket_holding_identification {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det≠0) (S φ H : ι → ℝ) (hS : ∀ i,S i≠0)
    (hmatch : ∀ j,(∑ i,A i j*(S i*H i))=φ j) :
    ∀ i,H i=(∑ j,(A.transpose)⁻¹ i j*φ j)/S i := by
  have hh := (basket_matrix_hedge_unique A hA S φ hS).2 H (funext hmatch)
  exact fun i => congrFun hh i

theorem variation_integrand_nonempty_sum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {T : EReal} [Fact (0≤T)] (c : ℕ → ℝ) (hc : ∀ n,0≤c n)
    (n : ℕ) (B : ClosedTime T → Ω → ℝ)
    (E : Fin (n+1) → ClosedTime T → Ω → ℝ) (η : Fin (n+1) → Ω × ℝ → ℝ)
    (hE : ∀ i,VariationIntegralFormula P c hc B (η i) (E i)) :
    VariationIntegralFormula P c hc B (fun z => ∑ i,η i z) (fun t w => ∑ i,E i t w) := by
  induction n with
  | zero => simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] using hE 0
  | succ n ih =>
    have ht := ih (fun i => E i.succ) (fun i => η i.succ) (fun i => hE i.succ)
    simpa only [Fin.sum_univ_succ] using variation_integrand_add P c hc B (E 0)
      (fun t w => ∑ i : Fin (n+1),E i.succ t w) (η 0)
      (fun z => ∑ i : Fin (n+1),η i.succ z) (hE 0) ht

/-- Sum the realized asset strategies and add the initial bank investment. -/
theorem basket_portfolio_assembly {ι : Type*} [Fintype ι]
    (S H η M G E I : ι → ℝ) (B B0 v E0 : ℝ)
    (hvalue : ∀ i,H i*S i+η i*B=M i*B)
    (hgains : ∀ i,M i*B=I i+G i+E i)
    (hbank : E0=v*(B-B0)) :
    (∑ i,H i*S i)+(v+∑ i,η i)*B=(v+∑ i,M i)*B ∧
      (v+∑ i,M i)*B=v*B0+(∑ i,I i)+(∑ i,G i)+(E0+∑ i,E i) := by
  have hv := Finset.sum_congr (s₁:=Finset.univ) rfl (fun i _ => hvalue i)
  have hg := Finset.sum_congr (s₁:=Finset.univ) rfl (fun i _ => hgains i)
  simp only [Finset.sum_add_distrib,←Finset.sum_mul] at hv hg
  constructor <;> nlinarith
end Asakura.Chapter12
#print axioms Asakura.Chapter12.basket_holding_identification
#print axioms Asakura.Chapter12.basket_portfolio_assembly

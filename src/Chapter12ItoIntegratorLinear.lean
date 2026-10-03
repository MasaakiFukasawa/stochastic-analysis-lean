import Chapter12ItoIntegratorAddition
import Chapter3IdentityItoIntegral
import Chapter4FiniteCovarianceSum

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem ito_integrator_smul {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t A,MeasurableSet[m] A → P A=0 → MeasurableSet[F t] A)
    (X Y : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ) (a : ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hHm : ∀ w,Measurable (fun t => H (w,t)))
    (hI : ItoCovarianceFormula P F X H Y) :
    ItoCovarianceFormula P F (fun t w => a*X t w) H (fun t w => a*Y t w) := by
  have hid := identity_ito_integral P hT F hF hle hnull X hX
  have hinner : ItoCovarianceFormula P F X (fun _ => a) (fun t w => a*X t w) := by
    convert hid.add_smul P F hF hle X X X (fun _ => 1) (fun _ => 1) hid (a-1) using 1
    · funext z;ring
    · funext t w;ring
  have hprod : ItoCovarianceFormula P F X (fun z => H z*a) (fun t w => a*Y t w) := by
    convert hI.add_smul P F hF hle X Y Y H H hI (a-1) using 1
    · funext z;ring
    · funext t w;ring
  exact ito_reverse_associativity P hT F hF hle hnull X _ _ (fun _ => a) H hX
    (hX.smul P F a) (hY.smul P F a) (fun _ => measurable_const) hHm hinner hprod

theorem ito_integrator_nonempty_sum {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t A,MeasurableSet[m] A → P A=0 → MeasurableSet[F t] A)
    (n : ℕ) (X Y : Fin (n+1) → ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hX : ∀ i,LocalMProcessWitness P F (X i))
    (hI : ∀ i,ItoCovarianceFormula P F (X i) H (Y i)) :
    ItoCovarianceFormula P F (fun t w => ∑ i,X i t w) H (fun t w => ∑ i,Y i t w) := by
  induction n with
  | zero => simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] using hI 0
  | succ n ih =>
    have ht := ih (fun i => X i.succ) (fun i => Y i.succ) (fun i => hX i.succ) (fun i => hI i.succ)
    have htail := Asakura.Chapter4.local_martingale_finset_sum P hT F hF hle Finset.univ
      (fun i : Fin (n+1) => X i.succ) (fun i _ => hX i.succ)
    simpa only [Fin.sum_univ_succ] using ito_integrator_addition P hT F hF hle hnull
      (X 0) (fun t w => ∑ i : Fin (n+1),X i.succ t w) (Y 0)
      (fun t w => ∑ i : Fin (n+1),Y i.succ t w) H (hX 0) htail (hI 0) ht
end Asakura.Chapter12
#print axioms Asakura.Chapter12.ito_integrator_smul
#print axioms Asakura.Chapter12.ito_integrator_nonempty_sum

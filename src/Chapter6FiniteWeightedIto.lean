import Chapter4FiniteItoSum

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem finite_weighted_ito {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    {n : ℕ} (H : Fin n → Ω × ℝ → ℝ) (N : Fin n → ClosedTime T → Ω → ℝ)
    (hN : ∀ k,LocalMProcessWitness P F (N k)) (hI : ∀ k,ItoCovarianceFormula P F W (H k) (N k))
    (θ : Fin n → ℝ) :
    LocalMProcessWitness P F (fun t w => ∑ k,θ k*N k t w) ∧
    ItoCovarianceFormula P F W (fun z => ∑ k,θ k*H k z) (fun t w => ∑ k,θ k*N k t w) := by
  have hθ k : LocalMProcessWitness P F (fun t w => θ k*N k t w) := (hN k).smul P F (θ k)
  have hθI k : ItoCovarianceFormula P F W (fun z => θ k*H k z) (fun t w => θ k*N k t w) := by
    have hh := ItoCovarianceFormula.add_smul P F hF hle W (N k) (N k) (H k) (H k) (hI k) (hI k) (θ k-1)
    convert hh using 1 <;> ext z w <;> ring
  exact ⟨local_martingale_finset_sum P hT F hF hle univ _ (fun k _ => hθ k),
    finite_ito_sum P hT F hF hle hnull W hW univ _ _ (fun k _ => hθI k)⟩

end Asakura.Chapter6

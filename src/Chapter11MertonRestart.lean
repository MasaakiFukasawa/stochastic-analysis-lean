import Chapter11MertonAllSolutions

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- Restart with the proved future-increment Brownian system. The result
 gives the manuscript value J(t0,x), with no use of Markov or dynamic
 programming assumptions in the verification. -/
theorem merton_at_starting_time {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (π : Ω × ℝ → ℝ) (hm : Measurable π)
    (T t0 : ℝ) (ht0 : 0≤t0) (htT : t0<T)
    (hp : ∀ d,0<d → @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) d => (B.shift t0 ht0).F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) d => π (z.1,z.2.val)))
    (K x r μ σ γ : ℝ) (hK : 0≤K) (hb : ∀ z,|π z|≤K)
    (hx : 0<x) (hσ : σ≠0) (hγ : 0<γ) (hγ1 : γ≠1)
    (X M : HalfClosedTime → Ω → ℝ)
    (hXa : ∀ t,t<⊤ → Measurable[(B.shift t0 ht0).F t] (X t))
    (hXc : ∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t)
    (hM : LocalMProcessWitness P (B.shift t0 ht0).F M)
    (hMI : ItoCovarianceFormula P (B.shift t0 ht0).F ((B.shift t0 ht0).W 0) (fun z => X (realTimeClamp z.2) z.1*(σ*π z)) M)
    (he : ∀ᵐ w ∂P,∀ t∈Icc 0 (T-t0),X (realTimeClamp t) w=x+
      (∫ s in 0..t,X (realTimeClamp s) w*(r+π (w,s)*(μ-r)))+M (realTimeClamp t) w) :
    Integrable (fun w => (X (realTimeClamp (T-t0)) w)^(1-γ)/(1-γ)) P ∧
      (∫ w,(X (realTimeClamp (T-t0)) w)^(1-γ)/(1-γ) ∂P)≤mertonValue r μ σ γ T t0 x ∧
      ((∀ z,π z=(μ-r)/(γ*σ^2)) →
        (∫ w,(X (realTimeClamp (T-t0)) w)^(1-γ)/(1-γ) ∂P)=mertonValue r μ σ γ T t0 x) := by
  have hh := investment_solution_merton_verified P (B.shift t0 ht0) π hm (T-t0)
    (sub_pos.mpr htT) hp K x r μ σ γ hK hb hx hσ hγ hγ1 X M hXa hXc hM hMI he
  simpa only [mertonValue,sub_zero] using hh

/-- At the terminal starting time the only terminal wealth is the initial
 wealth and the value reduces exactly to utility. -/
theorem merton_zero_horizon {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (x r μ σ γ T : ℝ) (hX : X=ᵐ[P] fun _ => x) :
    Integrable (fun w => (X w)^(1-γ)/(1-γ)) P ∧
      (∫ w,(X w)^(1-γ)/(1-γ) ∂P)=mertonValue r μ σ γ T T x := by
  have he : (fun w => (X w)^(1-γ)/(1-γ))=ᵐ[P] fun _ => x^(1-γ)/(1-γ) :=
    hX.fun_comp (fun z => z^(1-γ)/(1-γ))
  refine ⟨(integrable_const _).congr he.symm,?_⟩
  rw [integral_congr_ae he]
  simp [mertonValue]

end Asakura.Chapter11

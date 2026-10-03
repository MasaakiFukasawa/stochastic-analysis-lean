import Chapter8ContractiveRandomMapInvariant
import Chapter8FlowSecondMoment
import FullAuditLangevinContraction

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Construct an invariant law from independent unit past noises. The
semigroup commutation then upgrades invariance at time one to every time;
the contraction gives uniqueness and the manuscript's geometric estimate. -/
theorem contractive_flow_invariant {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → E → Ω → E) (hX : ∀ t≥0,Measurable (Function.uncurry (X t)))
    (h0 : ∀ t≥0,MemLp (X t 0) 2 P)
    (κ : ℝ) (hκ : 0<κ)
    (hCon : ∀ t≥0,∀ w x y,‖X t x w-X t y w‖≤Real.exp (-κ*t)*‖x-y‖)
    (hcommute : ∀ (μ : Measure E),IsProbabilityMeasure μ →
      MemLp (fun x : E => x) 2 μ → ∀ t≥0,
      flowLaw (flowLaw μ P (X t)) P (X 1)=flowLaw (flowLaw μ P (X 1)) P (X t)) :
    ∃ π : Measure E,IsProbabilityMeasure π ∧ MemLp (fun x : E => x) 2 π ∧
      (∀ t≥0,flowLaw π P (X t)=π) ∧
      (∀ (μ : Measure E),IsProbabilityMeasure μ → MemLp (fun x : E => x) 2 μ →
        ∀ t≥0,transportDistance (flowLaw μ P (X t)) π≤Real.exp (-κ*t)*transportDistance μ π) ∧
      (∀ (ν : Measure E),IsProbabilityMeasure ν → MemLp (fun x : E => x) 2 ν →
        flowLaw ν P (X 1)=ν → ν=π) := by
  let ρ : ℝ≥0 := ⟨Real.exp (-κ), (Real.exp_pos _).le⟩
  have hρ : ρ<1 := by
    change Real.exp (-κ)<1
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hκ)
  obtain ⟨π,hπp,hπ,hπ1⟩ := contractive_random_map_invariant P (X 1) (hX 1 (by norm_num))
    (h0 1 (by norm_num)) ρ hρ (fun w x y => by
      change ‖X 1 x w-X 1 y w‖≤Real.exp (-κ)*‖x-y‖
      simpa only [mul_one] using hCon 1 (by norm_num) w x y)
  letI := hπp
  change flowLaw π P (X 1)=π at hπ1
  have hprop (μ : Measure E) [IsProbabilityMeasure μ] (hm : MemLp (fun x : E => x) 2 μ)
      (t : ℝ) (ht : 0≤t) : MemLp (fun x : E => x) 2 (flowLaw μ P (X t)) :=
    flow_second_moment μ P (X t) (hX t ht) hm (h0 t ht) (Real.exp (-κ*t))
      (fun x => ae_of_all _ (fun w => by simpa only [sub_zero] using hCon t ht w x 0))
  have hcontr (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      (hm : MemLp (fun x : E => x) 2 μ) (hn : MemLp (fun x : E => x) 2 ν)
      (t : ℝ) (ht : 0≤t) :
      transportDistance (flowLaw μ P (X t)) (flowLaw ν P (X t))≤
        Real.exp (-κ*t)*transportDistance μ ν := by
    haveI := quadratic_coupling_nonempty μ ν hm hn
    exact shared_noise_transport_contraction μ ν P (X t) (hX t ht) _ (Real.exp_pos _)
      (fun x y => ae_of_all _ (fun w => hCon t ht w x y))
  have huniq (ν : Measure E) (hp : IsProbabilityMeasure ν) (hn : MemLp (fun x : E => x) 2 ν)
      (hinv : flowLaw ν P (X 1)=ν) : ν=π := by
    letI := hp
    exact langevin_invariant_unique ν π hn hπ P (X 1) κ 1 hκ (by norm_num)
      (hcontr ν π hn hπ 1 (by norm_num)) hinv hπ1
  have hinv t (ht : 0≤t) : flowLaw π P (X t)=π := by
    have hp : IsProbabilityMeasure (flowLaw π P (X t)) :=
      (Measure.isProbabilityMeasure_map_iff (hX t ht).aemeasurable).mpr inferInstance
    apply huniq _ hp (hprop π hπ t ht)
    rw [hcommute π hπp hπ t ht,hπ1]
  refine ⟨π,hπp,hπ,hinv,?_,huniq⟩
  intro μ hp hm t ht
  letI := hp
  have hh := hcontr μ π hm hπ t ht
  rwa [hinv t ht] at hh

end Asakura.Chapter8

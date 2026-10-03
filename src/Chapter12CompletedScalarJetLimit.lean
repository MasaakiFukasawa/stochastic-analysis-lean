import Chapter12SobolevSequenceCauchy

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000

theorem completed_scalar_jet_cauchy_limit {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤) (k:ℕ)
    (x:ℕ → malliavinSobolevJetSpace H P W S hS hcore p hp k)
    (hx:CauchySeq (fun m => WithLp.toLp 1 (fun j => (x m).val j))) :
    ∃y:malliavinSobolevJetSpace H P W S hS hcore p hp k,
      Tendsto (fun m => WithLp.toLp 1 (fun j => (x m).val j)) atTop
        (𝓝 (WithLp.toLp 1 (fun j => y.val j))) := by
  let E:Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) p P
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hx
  let y:PiLp p E := WithLp.toLp p v.ofLp
  have ht:Tendsto (fun m => (x m).val) atTop (𝓝 y) :=
    (((PiLp.continuous_toLp p E).comp (PiLp.continuous_ofLp 1 E)).tendsto v).comp hv
  have hy:y∈malliavinSobolevJetSpace H P W S hS hcore p hp k :=
    (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht (Eventually.of_forall (fun m => (x m).property))
  exact ⟨⟨y,hy⟩,hv⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.completed_scalar_jet_cauchy_limit

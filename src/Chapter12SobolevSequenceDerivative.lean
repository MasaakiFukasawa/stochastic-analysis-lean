import Chapter12SobolevSequenceCauchy
import Chapter12SobolevDerivativeTail
import Chapter12SobolevFirstCoordinates

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem scalar_even_jet_cauchy_of_derivative {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (D:Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (F:ℕ → Ω → ℝ) (U:ℕ → Ω → H)
    (hF:∀m,MemLp (F m) 2 P) (hU:∀m,MemLp (U m) 2 P)
    (hgraph:∀m,((hF m).toLp _,(hU m).toLp _)∈D.graph)
    (hzero:∀(p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤)
      (v:ℕ → Lp ℝ p P), (∀m,(v m:Ω → ℝ)=ᵐ[P] F m) → CauchySeq v)
    (k:ℕ) (hc:VectorEvenJetCauchy H P W S hS hcore U k) :
    ScalarEvenJetCauchy H P W S hS hcore F (k+1) := by
  intro n hn hp1 x hx
  let p:ℝ≥0∞ := (2*n:ℕ)
  letI : Fact (1≤p) := ⟨hp1⟩
  have hp:p≠⊤ := ENNReal.natCast_ne_top _
  have h2p:2≤p := by dsimp [p];exact_mod_cast (show 2≤2*n by omega)
  have ht : ∀m,∃y:vectorSobolevJetSpace H P W S hS hcore p hp k,
      ∀j:Fin (k+1),y.val j=(x m).val j.succ := by
    intro m
    obtain ⟨y,hy⟩ := sobolev_derivative_tail H P W S hS hcore p p le_rfl hp hp k (x m)
    refine ⟨y,fun j => ?_⟩
    rw [hy j]
    exact Lp.ext (probabilityLpInclusion_coe P p p le_rfl _)
  choose y hy using ht
  have hraw:∀m,((y m).val 0:Ω → H)=ᵐ[P] U m := by
    intro m
    have hmem := sobolev_first_coordinates_graph H P W S hS hcore 2 p h2p
      (by simp) hp D hg k (x m)
    have hval:probabilityLpInclusion P 2 p h2p ((x m).val 0)=(hF m).toLp _ :=
      Lp.ext ((probabilityLpInclusion_coe P 2 p h2p _).trans ((hx m).trans (hF m).coeFn_toLp.symm))
    rw [hval] at hmem
    have he := partial_linear_graph_output_unique D hmem (hgraph m)
    have hae := probabilityLpInclusion_coe P 2 p h2p ((x m).val 1)
    rw [he] at hae
    rw [hy m 0]
    exact hae.symm.trans (hU m).coeFn_toLp
  have hcy := hc n hn hp1 y hraw
  let E:Fin (k+1+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) p P
  let V:Fin (k+1) → Type _ := fun j => Lp (positiveMalliavinTensorPower H j.val) p P
  have hcoords:∀j:Fin (k+1+1),CauchySeq (fun m => (x m).val j) := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact hzero p hp (fun m => (x m).val 0) hx
    · have hh := (PiLp.proj (𝕜:=ℝ) 1 V i).uniformContinuous.comp_cauchySeq hcy
      simpa only [Function.comp_def,PiLp.proj_apply,hy] using hh
  have hex:∀j:Fin (k+1+1),∃v:E j,Tendsto (fun m => (x m).val j) atTop (𝓝 v) :=
    fun j => cauchySeq_tendsto_of_complete (hcoords j)
  choose v hv using hex
  exact (((PiLp.continuous_toLp 1 E).tendsto v).comp (tendsto_pi_nhds.mpr hv)).cauchySeq
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_even_jet_cauchy_of_derivative

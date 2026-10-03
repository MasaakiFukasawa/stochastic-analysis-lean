import Chapter8NewtonEuclideanNorm
import Chapter8TransportNormComparison
import Chapter8PhaseLinearEquiv

open MeasureTheory
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance : MeasurableSpace (WithLp 2 (E × E)) := borel _
local instance : BorelSpace (WithLp 2 (E × E)) := ⟨rfl⟩

/-- The physical position-velocity Euclidean distance is compared with
the Newton energy distance using constants independent of the dimension. -/
theorem newton_physical_transport {d : ℕ} (e : (Fin d → ℝ) ≃L[ℝ] E)
    (δ b : ℝ) (hp : 0<b+δ^2/4)
    (μ ν : Measure (Fin (d+d) → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun z => z) 2 μ) (hν : MemLp (fun z => z) 2 ν) :
    let A := (phaseLinearEquiv e).trans (newtonCoordinateEquiv δ b hp)
    let R := (phaseLinearEquiv e).trans (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm
    let c := Real.sqrt (b+δ^2/4)
    transportDistance (μ.map A) (ν.map A)≤(c+1+|δ/2|)*transportDistance (μ.map R) (ν.map R) ∧
    transportDistance (μ.map R) (ν.map R)≤(1+(1+|δ/2|)*c⁻¹)*transportDistance (μ.map A) (ν.map A) := by
  dsimp only
  have hc : 0<Real.sqrt (b+δ^2/4) := Real.sqrt_pos.mpr hp
  constructor
  · apply transport_between_coordinate_norms _ _ μ ν hμ hν _ (by positivity)
    intro z
    exact (newton_euclidean_norm_comparison δ b hp (phaseLinearEquiv e z)).1
  · apply transport_between_coordinate_norms _ _ μ ν hμ hν _ (by positivity)
    intro z
    exact (newton_euclidean_norm_comparison δ b hp (phaseLinearEquiv e z)).2

/-- Coordinate projections are contractions in the physical Euclidean
phase norm, so the same transport rate applies to both marginals. -/
theorem phase_marginal_transport (μ ν : Measure (WithLp 2 (E × E)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun z => z) 2 μ) (hν : MemLp (fun z => z) 2 ν) :
    transportDistance (μ.map (fun z => z.ofLp.1)) (ν.map (fun z => z.ofLp.1))≤transportDistance μ ν ∧
    transportDistance (μ.map (fun z => z.ofLp.2)) (ν.map (fun z => z.ofLp.2))≤transportDistance μ ν := by
  haveI := quadratic_coupling_nonempty μ ν hμ hν
  constructor
  · have hh := transport_map_bound μ ν (fun z => z.ofLp.1) (by fun_prop) 1 (by norm_num)
      (fun x y => by simpa only [one_mul,WithLp.fst,WithLp.ofLp_sub,Prod.fst_sub] using WithLp.norm_fst_le E (x-y))
    simpa only [one_mul] using hh
  · have hh := transport_map_bound μ ν (fun z => z.ofLp.2) (by fun_prop) 1 (by norm_num)
      (fun x y => by simpa only [one_mul,WithLp.snd,WithLp.ofLp_sub,Prod.snd_sub] using WithLp.norm_snd_le E (x-y))
    simpa only [one_mul] using hh

end Asakura.Chapter8

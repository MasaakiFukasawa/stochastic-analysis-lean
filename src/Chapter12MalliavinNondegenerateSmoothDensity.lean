import Chapter12MalliavinDirectionsSmoothDensity
import Chapter12MalliavinInverseCovarianceSobolev

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem malliavin_nondegenerate_smooth_density {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (D:Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD:D.IsClosed)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hd:DenseRange (fun f:D.domain => (f:Lp ℝ 2 P)))
    (hdense:∀(q:ℝ≥0∞) [Fact (1≤q)] (hq:q≠⊤),
      DenseRange (fun c:SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (d:ℕ) (F:Fin (d+1) → Lp ℝ 2 P) (U:Fin (d+1) → Lp H 2 P)
    (hF:∀i,HasAllSobolevJets H P W S hS hcore (F i))
    (hFU:∀i,(F i,U i)∈D.graph)
    (hpos:∀ᵐw∂P,0<(derivativeGram (fun i => U i w)).det)
    (hi:∀(p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤),
      MemLp (fun w => ((derivativeGram (fun i => U i w)).det)⁻¹) p P) :
    let f:Ω → EuclideanSpace ℝ (Fin (d+1)) := fun w => WithLp.toLp 2 (fun i => F i w)
    ∃p:EuclideanSpace ℝ (Fin (d+1)) → ℝ,ContDiff ℝ ∞ p ∧ (∀x,0≤p x) ∧
      P.map f=volume.withDensity (fun x => ENNReal.ofReal (p x)) := by
  obtain ⟨hInv,hA,hdual⟩ := malliavin_inverse_covariance_sobolev H P W S hS hcore hdense
    D hD hg F U hF hFU hpos hi
  exact malliavin_directions_smooth_density H P W S hS hcore D hD hg hd hdense d F U hFU
    (fun i w => ∑j,(derivativeGram (fun l => U l w))⁻¹ i j • U j w) hA hdual
end Asakura.Chapter12
#print axioms Asakura.Chapter12.malliavin_nondegenerate_smooth_density

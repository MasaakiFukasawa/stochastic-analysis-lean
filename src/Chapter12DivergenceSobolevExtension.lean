import Chapter12ActualDivergenceJetBound
import Chapter12CoreRelationExtension
import Chapter12SobolevJetExponent

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

/-- The finite estimates extend the actual divergence to completed vector
Sobolev jets. The output jet is obtained by a Cauchy limit and the closed
adjoint relation identifies its zeroth coordinate. -/
theorem divergence_sobolev_jet_extension {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D₀ : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hgraph : (D₀.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hd : DenseRange (fun f : D₀.domain => (f : Lp ℝ 2 P)))
    (p : ℕ) (hp : 0<p) [Fact (1≤((2*p:ℕ):ℝ≥0∞))]
    (h2p : (2:ℝ≥0∞)≤(2*p:ℕ))
    (q : ℝ≥0∞) [Fact (1≤q)] [HolderConjugate ((2*p:ℕ):ℝ≥0∞) q] (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (k : ℕ) (x : vectorSobolevJetSpace H P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _) (k+2*p)) :
    ∃ y : (Submodule.span ℝ (range (scalarSobolevSumCoreJet H P W S hS hcore
      (2*p:ℕ) (ENNReal.natCast_ne_top _) k))).topologicalClosure,
      IsDivergence D₀ (probabilityLpInclusion P 2 (2*p:ℕ) h2p (x.val 0))
        (probabilityLpInclusion P 2 (2*p:ℕ) h2p (y.val 0)) ∧
      ‖y.val‖≤(k+1:ℕ)*((k:ℝ)+(2*(2*p-1):ℕ)*(2*p+1:ℕ))*‖x.val‖ := by
  let E := PiLp 1 (fun j : Fin (k+2*p+1) => Lp (positiveMalliavinTensorPower H j.val) (2*p:ℕ) P)
  let F := PiLp 1 (fun j : Fin (k+1) => Lp (malliavinTensorOrder H j.val) (2*p:ℕ) P)
  let vjet := vectorSobolevCoreJet H P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _) (k+2*p)
  let sjet := scalarSobolevSumCoreJet H P W S hS hcore (2*p:ℕ) (ENNReal.natCast_ne_top _) k
  let V : Submodule ℝ E := Submodule.span ℝ (range vjet)
  let A : Submodule ℝ F := Submodule.span ℝ (range sjet)
  let L : E →L[ℝ] Lp H 2 P := (probabilityLpInclusion P 2 (2*p:ℕ) h2p).comp (PiLp.proj (𝕜:=ℝ) 1 (fun j : Fin (k+2*p+1) => Lp (positiveMalliavinTensorPower H j.val) (2*p:ℕ) P) 0)
  let M : F →L[ℝ] Lp ℝ 2 P := (probabilityLpInclusion P 2 (2*p:ℕ) h2p).comp (PiLp.proj (𝕜:=ℝ) 1 (fun j : Fin (k+1) => Lp (malliavinTensorOrder H j.val) (2*p:ℕ) P) 0)
  obtain ⟨Dv,hDv,hcv⟩ := higher_vector_core_operators H P W S hS hcore
    (2*p:ℕ) q (ENNReal.natCast_ne_top _) hq hdense
  obtain ⟨Ds,hDs,hcs⟩ := scalar_jet_operators_from_core H P W S hS hcore
    (2*p:ℕ) q (ENNReal.natCast_ne_top _) hq hdense
  have hV : (V : Set E)=range vjet := vector_sobolev_core_range H P W S hS hcore
    (2*p:ℕ) (ENNReal.natCast_ne_top _) (k+2*p) Dv hcv
  have hA : (A : Set F)=range sjet := cylinder_sum_jet_span_range P W S hS hcore
    (2*p:ℕ) (ENNReal.natCast_ne_top _)
    (fun j : Fin (k+1) => Lp (malliavinTensorOrder H j.val) (2*p:ℕ) P)
    (fun j : Fin k => Ds j.val) sjet (fun c j => hcs c j.val)
    (LinearMap.id : Lp ℝ (2*p:ℕ) P →ₗ[ℝ] Lp ℝ (2*p:ℕ) P) (fun c => rfl)
  have hL (c : VectorCylinderExpr H H) : L (vjet c)=c.valueLp P W S hS hcore 2 (by simp) :=
    vector_cylinder_exponent P W S hS hcore 2 (2*p:ℕ) h2p (by simp) (ENNReal.natCast_ne_top _) c
  have hM (c : SmoothCylinder H) : M (sjet c)=c.valueLp P W S hS hcore 2 (by simp) :=
    cylinder_jet_coordinate_exponent H P W S hS hcore 2 (2*p:ℕ) h2p (by simp) (ENNReal.natCast_ne_top _) c 0
  have hex : ∀ a∈V,∃ b∈A,(L a,M b)∈divergenceGraph D₀ := by
    intro a ha
    change a∈(V : Set E) at ha
    rw [hV] at ha
    obtain ⟨c,rfl⟩ := ha
    obtain ⟨g,hg,_,_⟩ := vector_divergence_all_bounds H P W S hS hcore D₀ hgraph p hp q hq hdense c
    refine ⟨sjet g,?_,?_⟩
    · change sjet g∈(A : Set F)
      rw [hA]
      exact mem_range_self g
    · change IsDivergence D₀ (L (vjet c)) (M (sjet g))
      rw [hL,hM]
      exact hg
  have hbnd : ∀ a∈V,∀ b∈A,(L a,M b)∈divergenceGraph D₀ →
      ‖b‖≤((k+1:ℕ)*((k:ℝ)+(2*(2*p-1):ℕ)*(2*p+1:ℕ)))*‖a‖ := by
    intro a ha b hb hab
    change a∈(V : Set E) at ha
    rw [hV] at ha
    change b∈(A : Set F) at hb
    rw [hA] at hb
    obtain ⟨c,rfl⟩ := ha
    obtain ⟨g,rfl⟩ := hb
    change IsDivergence D₀ (L (vjet c)) (M (sjet g)) at hab
    rw [hL,hM] at hab
    exact actual_divergence_finite_jet_bound H P W S hS hcore D₀ hgraph p hp q hq hdense hd c g hab k
  obtain ⟨y,hy,hrel,hbound⟩ := core_relation_extension V A L M (divergenceGraph D₀)
    (divergence_graph_isClosed D₀) ((k+1:ℕ)*((k:ℝ)+(2*(2*p-1):ℕ)*(2*p+1:ℕ))) (by positivity)
    hex hbnd x.val x.property
  exact ⟨⟨y,hy⟩,hrel,hbound⟩

end Asakura.Chapter12

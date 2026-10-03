import Chapter12AllSobolevScalarVectorProduct
import Chapter12AllVectorSobolevLinear
import Chapter12AllSobolevFiniteAlgebra
import Chapter12AllSobolevFirstGraph

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

variable {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (D:Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hd:DenseRange (fun f:D.domain => (f:Lp ℝ 2 P)))
    (hdense:∀(q:ℝ≥0∞) [Fact (1≤q)] (hq:q≠⊤),
      DenseRange (fun c:SmoothCylinder H => c.valueLp P W S hS hcore q hq))

include hg hd hdense

theorem all_sobolev_weighted_divergence (A:Ω → H)
    (hA:HasAllVectorSobolevJets H P W S hS hcore A)
    (G:Lp ℝ 2 P) (hG:HasAllSobolevJets H P W S hS hcore G) :
    ∃(Z:Lp ℝ 2 P),HasAllSobolevJets H P W S hS hcore Z ∧
      ∃B:Lp H 2 P,(B:Ω → H)=ᵐ[P] (fun w => G w • A w) ∧ IsDivergence D B Z := by
  have hB := all_sobolev_scalar_vector_product H P W S hS hcore hdense G A hG hA
  have hm := all_vector_sobolev_memLp H P W S hS hcore _ hB 2 (by simp)
  have hb := all_vector_sobolev_congr H P W S hS hcore _ _ hB hm.coeFn_toLp.symm
  obtain ⟨Z,hZ,hZS⟩ := divergence_all_sobolev_orders H P W S hS hcore D hg hd hdense (hm.toLp _) hb
  exact ⟨Z,hZS,hm.toLp _,hm.coeFn_toLp,hZ⟩

theorem all_sobolev_iterated_weights (A:Ω → H)
    (hA:HasAllVectorSobolevJets H P W S hS hcore A) :
    ∃Z:ℕ → Lp ℝ 2 P,
      (Z 0:Ω → ℝ)=ᵐ[P] (fun _ => 1) ∧
      (∀k,HasAllSobolevJets H P W S hS hcore (Z k)) ∧
      ∀k,∃B:Lp H 2 P,(B:Ω → H)=ᵐ[P] (fun w => Z k w • A w) ∧ IsDivergence D B (Z (k+1)) := by
  classical
  let E := {G:Lp ℝ 2 P // HasAllSobolevJets H P W S hS hcore G}
  have hstep:∀G:E,∃Z:E,∃B:Lp H 2 P,(B:Ω → H)=ᵐ[P] (fun w => G.val w • A w) ∧ IsDivergence D B Z.val := by
    intro G
    obtain ⟨Z,hZ,B,hB,hdiv⟩ := all_sobolev_weighted_divergence H P W S hS hcore D hg hd hdense A hA G.val G.property
    exact ⟨⟨Z,hZ⟩,B,hB,hdiv⟩
  choose step hstep using hstep
  have h1:MemLp (fun _:Ω => (1:ℝ)) 2 P := memLp_const 1
  let z0:E := ⟨h1.toLp _,all_sobolev_congr H P W S hS hcore _ _
    (all_sobolev_const H P W S hS hcore 1) h1.coeFn_toLp.symm⟩
  let z:ℕ → E := Nat.rec z0 (fun _ v => step v)
  refine ⟨fun k => (z k).val,h1.coeFn_toLp,fun k => (z k).property,fun k => ?_⟩
  exact hstep (z k)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_sobolev_iterated_weights

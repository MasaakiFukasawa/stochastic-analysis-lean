import Chapter12BrownianSolutionCylinderFrames
import Chapter12BrownianGridScalarStability
import Chapter12RebasedDerivativePathBound
import Chapter12CylinderValueEquality
import Chapter12NaturalBrownianAllOrders

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem brownian_cylinder_jet_bounds {Ω : Type*} {E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ) (hT : 0<T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀u,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (B : BrownianTimeCoordinates d T → Ω → ℝ)
    (hB : ∀z,B z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (v : Fin (d+1) → E) (x : E) (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E)) (hS : ContDiff ℝ ∞ S)
    (hSeq : ∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT.le s)))
    (hSB : ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀a,‖iteratedFDeriv ℝ k S a‖≤C)
    (ell : E →L[ℝ] ℝ) (t : Icc (0:ℝ) T)
    (n : ℕ → ℕ) (h : ℕ → ℝ) (hn : ∀i,0<n i) (hh : ∀i,0<h i)
    (hnT : ∀i,(n i:ℝ)*h i=T) :
    letI := finite_horizon_L2_nontrivial T hT
    let H := finiteWienerHilbertData d T
    let hc := fun u (_ : u∈(univ : Set H)) => hW u
    ∀ (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W univ dense_univ hc q hq))
      (c : ℕ → SmoothCylinder H)
      (V : ℕ → Lp C(Icc (0:ℝ) T,E) p P),
      (∀i,(c i).value P W=ᵐ[P] (fun w => ell (S (ContinuousMap.const _ x+brownianPolygonalForcing d T hT.le B v (h i) (n i) w) t))) →
      (∀i,(V i : Ω → C(Icc (0:ℝ) T,E))=ᵐ[P] (fun w => S (ContinuousMap.const _ x+brownianPolygonalForcing d T hT.le B v (h i) (n i) w))) →
      ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀i j,
        ‖cylinderJetCoordinate H P W univ dense_univ hc p hp (c i) k-
          cylinderJetCoordinate H P W univ dense_univ hc p hp (c j) k‖≤
          C*(‖V i-V j‖+Real.sqrt (h i)+Real.sqrt (h j)) := by
  intro H hc hdense c V hcv hV
  letI := finite_horizon_L2_nontrivial T hT
  have hf (a : ℕ × ℕ) := brownian_forcing_frames P d T hT W B hB v
    (h a.1) (h a.2) (hh a.1) (hh a.2) (n a.1) (n a.2) (hnT a.1) (hnT a.2)
  choose m e he hf hg using hf
  have hbnd := brownian_grid_scalar_stability b hb hbound d T hT.le v x S hS hSeq ell
    (fun a => m a+1) (fun a => n a.1) (fun a => n a.2) (fun a => h a.1) (fun a => h a.2)
    (fun a => hh a.1) (fun a => hh a.2) (fun a => hn a.1) (fun a => hn a.2)
    (fun a => hnT a.1) (fun a => hnT a.2) e he
  intro k hk
  obtain ⟨C,hC,hbC⟩ := hbnd k hk
  refine ⟨C,hC,?_⟩
  intro i j
  let a := (i,j)
  obtain ⟨f,hff,hfv⟩ := forcing_gaussian_representation _ P W T S hS hSB (m a+1) (e a) _
    (ContinuousMap.const _ x) ell t _ (hf a)
  obtain ⟨g,hgf,hgv⟩ := forcing_gaussian_representation _ P W T S hS hSB (m a+1) (e a) _
    (ContinuousMap.const _ x) ell t _ (hg a)
  have hci := cylinder_value_equality H P W univ dense_univ hc p hp (c i) (f.toCylinder (e a)) ((hcv i).trans hfv.symm)
  have hcj := cylinder_value_equality H P W univ dense_univ hc p hp (c j) (g.toCylinder (e a)) ((hcv j).trans hgv.symm)
  obtain ⟨l,rfl⟩ : ∃l,k=l+1 := ⟨k-1,by omega⟩
  have hres := rebased_derivative_path_bound H P W univ dense_univ hc p q hp hq hdense
    (c i) (c j) f g (e a) (he a) hci hcj l (V i-V j) C
    (Real.sqrt (h i)+Real.sqrt (h j)) hC (by positivity) ?_
  · simpa only [add_assoc] using hres
  filter_upwards [hf a,hg a,hV i,hV j,Lp.coeFn_sub (V i) (V j)] with w hfw hgw hvi hvj hvij
  rw [hff,hgf]
  have hh := hbC a (fun z => W (e a z) w) t
  dsimp only at hh
  rw [hfw,hgw] at hh
  rw [hvij,Pi.sub_apply,hvi,hvj]
  exact hh
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_cylinder_jet_bounds

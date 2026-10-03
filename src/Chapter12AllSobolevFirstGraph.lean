import Chapter12DivergenceAllSobolev

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)

theorem all_sobolev_memLp (F : Ω → ℝ) (hF : HasAllSobolevJets H P W S hS hcore F)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) : MemLp F p P := by
  obtain ⟨x,hx⟩ := hF p Fact.out hp 0
  exact MemLp.ae_eq hx (Lp.memLp (x.val 0))

theorem all_vector_sobolev_memLp (U : Ω → H) (hU : HasAllVectorSobolevJets H P W S hS hcore U)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) : MemLp U p P := by
  obtain ⟨x,hx⟩ := hU p Fact.out hp 0
  exact MemLp.ae_eq hx (Lp.memLp (x.val 0))

theorem all_sobolev_first_graph (F : Ω → ℝ) (hF : HasAllSobolevJets H P W S hS hcore F)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp))) :
    ∃ (V : Ω → H) (hF' : MemLp F p P) (hV : MemLp V p P),
      (hF'.toLp _,hV.toLp _)∈D.graph := by
  obtain ⟨x,hx⟩ := hF p Fact.out hp 1
  let E : Fin 2 → Type _ := fun j => Lp (malliavinTensorOrder H j.val) p P
  let J : PiLp p E →L[ℝ] Lp ℝ p P × Lp H p P :=
    (PiLp.proj (𝕜:=ℝ) p E 0).prod (PiLp.proj (𝕜:=ℝ) p E 1)
  let jet := fun c : SmoothCylinder H => WithLp.toLp p
    ((fun j : Fin 2 => cylinderJetCoordinate H P W S hS hcore p hp c j.val) : ∀ j,E j)
  have hc (c : SmoothCylinder H) : J (jet c)∈D.graph := by
    change (c.valueLp P W S hS hcore p hp,
      (cylinderFirstGradientExpr c).valueLp P W S hS hcore p hp)∈D.graph
    have he : (cylinderFirstGradientExpr c).valueLp P W S hS hcore p hp=
      c.gradientLp P W S hS hcore p hp := by
      exact scalar_gradient_expression P W S hS hcore p hp c
    rw [he]
    change cylinderPair P W S hS hcore p hp c∈(D.graph : Set _)
    rw [hg]
    exact subset_closure (mem_range_self c)
  have hs : Submodule.span ℝ (range jet)≤D.graph.comap J.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c,rfl⟩
    exact hc c
  have hclosed : IsClosed (J ⁻¹' (D.graph : Set (Lp ℝ p P × Lp H p P))) := by
    have hDc : IsClosed (D.graph : Set (Lp ℝ p P × Lp H p P)) := by
      rw [hg]
      exact isClosed_closure
    exact hDc.preimage J.continuous
  have hj : J x.val∈D.graph := (closure_minimal hs hclosed) x.property
  have hF' : MemLp F p P := MemLp.ae_eq hx (Lp.memLp (x.val 0))
  have hv : MemLp (x.val 1 : Ω → H) p P := Lp.memLp _
  have he : hF'.toLp F=x.val 0 := by
    apply Lp.ext
    exact hF'.coeFn_toLp.trans hx.symm
  refine ⟨(x.val 1 : Ω → H),hF',hv,?_⟩
  rw [he,Lp.toLp_coeFn]
  exact hj

end Asakura.Chapter12

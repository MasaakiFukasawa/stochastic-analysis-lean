import Chapter12JetCoreRange
import Chapter12CylinderPairLinear

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- A compatible jet whose zeroth coordinate is the actual cylinder value
has a linear range, so its completion admits single-cylinder approximations. -/
theorem cylinder_jet_span_range {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    {n : ℕ} (E : Fin (n+1) → Type*)
    [∀ j,NormedAddCommGroup (E j)] [∀ j,NormedSpace ℝ (E j)]
    (D : ∀ j : Fin n,E j.castSucc →ₗ.[ℝ] E j.succ)
    (jet : SmoothCylinder H → PiLp p E)
    (hjet : ∀ c j,(jet c j.castSucc,jet c j.succ)∈(D j).graph)
    (I : Lp ℝ p P →ₗ[ℝ] E 0)
    (hzero : ∀ c,jet c 0=I (c.valueLp P W S hS hcore p hp)) :
    (Submodule.span ℝ (range jet) : Set _) = range jet := by
  apply jet_span_eq_range p E D jet hjet
  · let c := smoothCylinderOfFunction (fun _ : Fin 0 => (0:H))
      (fun _ => 0) contDiff_const (fun k => by
        refine ⟨0,le_rfl,0,fun x => ?_⟩
        cases k <;> simp [norm_iteratedFDeriv_zero,iteratedFDeriv_succ_const])
    refine ⟨scaleSmoothCylinder 0 c,?_⟩
    have he := congrArg Prod.fst (cylinderPair_smul P W S hS hcore p hp 0 c)
    change (scaleSmoothCylinder 0 c).valueLp P W S hS hcore p hp = 0 • c.valueLp P W S hS hcore p hp at he
    rw [hzero,he,zero_smul,map_zero]
  · intro c d
    refine ⟨addSmoothCylinder c d,?_⟩
    have he := congrArg Prod.fst (cylinderPair_add P W S hS hcore p hp c d)
    change (addSmoothCylinder c d).valueLp P W S hS hcore p hp =
      c.valueLp P W S hS hcore p hp+d.valueLp P W S hS hcore p hp at he
    rw [hzero,hzero,hzero,he,map_add]
  · intro a c
    refine ⟨scaleSmoothCylinder a c,?_⟩
    have he := congrArg Prod.fst (cylinderPair_smul P W S hS hcore p hp a c)
    change (scaleSmoothCylinder a c).valueLp P W S hS hcore p hp = a • c.valueLp P W S hS hcore p hp at he
    rw [hzero,hzero,he,map_smul]

/-- One sequence approximates all orders simultaneously in the Sobolev norm. -/
theorem jet_single_core_approximation {ι : Type*} {n : ℕ} (p : ℝ≥0∞) [Fact (1≤p)]
    (E : Fin (n+1) → Type*) [∀ j,NormedAddCommGroup (E j)] [∀ j,NormedSpace ℝ (E j)]
    (jet : ι → PiLp p E)
    (hspan : (Submodule.span ℝ (range jet) : Set _) = range jet)
    (x : (Submodule.span ℝ (range jet)).topologicalClosure) :
    ∃ c : ℕ → ι,Tendsto (fun m => jet (c m)) atTop (𝓝 x.val) := by
  have hx : x.val∈closure (range jet) := by
    have hh := x.property
    change x.val∈closure (Submodule.span ℝ (range jet) : Set _) at hh
    rwa [hspan] at hh
  obtain ⟨a,ha,hat⟩ := mem_closure_iff_seq_limit.mp hx
  choose c hc using ha
  exact ⟨c,by simpa only [hc] using hat⟩

end Asakura.Chapter12

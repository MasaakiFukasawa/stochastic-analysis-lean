import Chapter12CylinderAddition
import Chapter12CylinderScaling

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
  (p : ℝ≥0∞) (hp : p ≠ ⊤)

noncomputable def cylinderPair (c : SmoothCylinder H) : Lp ℝ p P × Lp H p P :=
  (c.valueLp P W S hS hcore p hp,c.gradientLp P W S hS hcore p hp)

theorem cylinderPair_add (c d : SmoothCylinder H) :
    cylinderPair P W S hS hcore p hp (addSmoothCylinder c d) =
      cylinderPair P W S hS hcore p hp c+cylinderPair P W S hS hcore p hp d := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [((addSmoothCylinder c d).value_memLp P W S hS hcore p hp).coeFn_toLp,
      (c.value_memLp P W S hS hcore p hp).coeFn_toLp,
      (d.value_memLp P W S hS hcore p hp).coeFn_toLp,
      Lp.coeFn_add (c.valueLp P W S hS hcore p hp) (d.valueLp P W S hS hcore p hp)] with w he hc hd hs
    dsimp only [cylinderPair,Prod.fst_add,SmoothCylinder.valueLp] at *
    rw [he,hs,Pi.add_apply,hc,hd,addSmoothCylinder_value]
  · apply Lp.ext
    filter_upwards [((addSmoothCylinder c d).gradient_memLp P W S hS hcore p hp).coeFn_toLp,
      (c.gradient_memLp P W S hS hcore p hp).coeFn_toLp,
      (d.gradient_memLp P W S hS hcore p hp).coeFn_toLp,
      Lp.coeFn_add (c.gradientLp P W S hS hcore p hp) (d.gradientLp P W S hS hcore p hp)] with w he hc hd hs
    dsimp only [cylinderPair,Prod.snd_add,SmoothCylinder.gradientLp] at *
    rw [he,hs,Pi.add_apply,hc,hd,addSmoothCylinder_gradient]

theorem cylinderPair_smul (a : ℝ) (c : SmoothCylinder H) :
    cylinderPair P W S hS hcore p hp (scaleSmoothCylinder a c) =
      a • cylinderPair P W S hS hcore p hp c := by
  apply Prod.ext
  · change (scaleSmoothCylinder a c).valueLp P W S hS hcore p hp = a • c.valueLp P W S hS hcore p hp
    apply Lp.ext
    filter_upwards [((scaleSmoothCylinder a c).value_memLp P W S hS hcore p hp).coeFn_toLp,
      (c.value_memLp P W S hS hcore p hp).coeFn_toLp,
      Lp.coeFn_smul a (c.valueLp P W S hS hcore p hp)] with w he hc hs
    dsimp only [cylinderPair,Prod.fst_smul,SmoothCylinder.valueLp] at *
    rw [he,hs,Pi.smul_apply,hc,scaleSmoothCylinder_value]
  · change (scaleSmoothCylinder a c).gradientLp P W S hS hcore p hp = a • c.gradientLp P W S hS hcore p hp
    apply Lp.ext
    filter_upwards [((scaleSmoothCylinder a c).gradient_memLp P W S hS hcore p hp).coeFn_toLp,
      (c.gradient_memLp P W S hS hcore p hp).coeFn_toLp,
      Lp.coeFn_smul a (c.gradientLp P W S hS hcore p hp)] with w he hc hs
    dsimp only [cylinderPair,Prod.snd_smul,SmoothCylinder.gradientLp] at *
    rw [he,hs,Pi.smul_apply,hc,scaleSmoothCylinder_gradient]

/-- The span used to construct the partial linear operator introduces no
extra domain elements: each graph point is already one smooth cylinder. -/
theorem cylinderPair_span_eq_range [Fact (1 ≤ p)] :
    (Submodule.span ℝ (range (cylinderPair P W S hS hcore p hp)) :
      Set (Lp ℝ p P × Lp H p P)) = range (cylinderPair P W S hS hcore p hp) := by
  let G : Submodule ℝ (Lp ℝ p P × Lp H p P) :=
    { carrier := range (cylinderPair P W S hS hcore p hp)
      zero_mem' := by
        refine ⟨scaleSmoothCylinder 0 (smoothCylinderOfFunction (fun _ : Fin 0 => (0:H))
          (fun _ => 0) contDiff_const (fun k => ?_)),?_⟩
        · refine ⟨0,le_rfl,0,fun x => ?_⟩
          cases k <;> simp [norm_iteratedFDeriv_zero,iteratedFDeriv_succ_const]
        · rw [cylinderPair_smul,zero_smul]
      add_mem' := by
        rintro _ _ ⟨c,rfl⟩ ⟨d,rfl⟩
        exact ⟨addSmoothCylinder c d,cylinderPair_add P W S hS hcore p hp c d⟩
      smul_mem' := by
        rintro a _ ⟨c,rfl⟩
        exact ⟨scaleSmoothCylinder a c,cylinderPair_smul P W S hS hcore p hp a c⟩ }
  have he : Submodule.span ℝ (range (cylinderPair P W S hS hcore p hp)) = G := Submodule.span_eq G
  rw [he]
  rfl

end Asakura.Chapter12

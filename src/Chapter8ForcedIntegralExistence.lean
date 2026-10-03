import Chapter8WeightedVolterra

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Construct the forced integral equation on any finite horizon by an
actual Banach fixed point. The forcing path is merely continuous. -/
theorem forced_integral_equation_exists {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 ≤ T) (K : ℝ≥0)
    (F : ℝ → E → E) (hFc : Continuous (Function.uncurry F))
    (hF : ∀ t,LipschitzWith K (F t)) (q : ℝ → E) (hq : Continuous q) :
    ∃ X : ℝ → E,Continuous X ∧ ∀ t,t∈Icc 0 T → X t=q t+∫ s in 0..t,F s (X s) := by
  let a : ℝ := (K:ℝ)+1
  have ha : 0<a := by dsimp [a]; positivity
  let G := fun (z : C(Icc (0:ℝ) T,E)) s => F s (Real.exp (a*s) • z (projIcc 0 T hT s))
  have hGc z : Continuous (G z) := by
    simpa only [G,Function.comp_def,Function.uncurry_def,Pi.smul_apply,Pi.smul_apply',id_eq] using hFc.comp (continuous_id.prodMk ((by fun_prop : Continuous (fun s : ℝ => Real.exp (a*s))).smul
      (z.continuous.comp continuous_projIcc)))
  have hPc z : Continuous (fun t : ℝ => Real.exp (-a*t) • (q t+∫ s in 0..t,G z s)) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-a*t))).smul
      (hq.add (intervalIntegral.differentiable_integral_of_continuous (hGc z)).continuous)
  let P : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E) := fun z =>
    ⟨fun t => Real.exp (-a*t.val) • (q t.val+∫ s in 0..t.val,G z s),(hPc z).comp continuous_subtype_val⟩
  have hPLip : LipschitzWith (K/(K+1)) P := by
    apply LipschitzWith.of_dist_le_mul
    intro z y
    rw [dist_eq_norm,dist_eq_norm]
    simpa only [NNReal.coe_div,NNReal.coe_add,NNReal.coe_one,a] using
      weighted_volterra_lipschitz T hT K a ha F hFc hF q P (fun z t => rfl) z y
  have hctr : ContractingWith (K/(K+1)) P :=
    ⟨(div_lt_one (by positivity : (0:ℝ≥0)<K+1)).mpr (by simp),hPLip⟩
  let z := ContractingWith.fixedPoint P hctr
  have hz : P z=z := hctr.fixedPoint_isFixedPt
  let X := fun t : ℝ => Real.exp (a*t) • z (projIcc 0 T hT t)
  refine ⟨X,(by fun_prop : Continuous (fun t : ℝ => Real.exp (a*t))).smul
    (z.continuous.comp continuous_projIcc),?_⟩
  intro t ht
  let s : Icc (0:ℝ) T := ⟨t,ht⟩
  have hproj : projIcc 0 T hT t=s := by
    apply Subtype.ext
    simp [projIcc,ht.1,ht.2,s]
  have he := congrArg (fun f : C(Icc (0:ℝ) T,E) => f s) hz
  change Real.exp (-a*t) • (q t+∫ r in 0..t,G z r)=z s at he
  dsimp only [X]
  rw [hproj,← he,smul_smul]
  have hee : Real.exp (a*t)*Real.exp (-a*t)=1 := by
    rw [← Real.exp_add]
    simp
  rw [hee,one_smul]

end Asakura.Chapter8

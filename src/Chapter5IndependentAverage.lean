import Chapter5FrozenQuotient
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2000000

/-- Integration against independent coordinates is integration against their
actual product law; no conditional-distribution formula is assumed. -/
theorem independent_bounded_average
    {Ω E K : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace K]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → E) (Y : Ω → K) (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y P) (f : E × K → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ z, ‖f z‖ ≤ B) :
    (∫ w, f (X w,Y w) ∂P) = ∫ w, (∫ y, f (X w,y) ∂P.map Y) ∂P := by
  have hi : Integrable f ((P.map X).prod (P.map Y)) :=
    Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ hb)
  have hm := hf.stronglyMeasurable.integral_prod_right' (ν := P.map Y)
  calc
    _ = ∫ z, f z ∂P.map (fun w => (X w,Y w)) :=
      (integral_map (hX.prodMk hY).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(P.map X).prod (P.map Y) := by rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
    _ = ∫ x, (∫ y, f (x,y) ∂P.map Y) ∂P.map X := integral_prod f hi
    _ = _ := integral_map hX.aemeasurable hm.aestronglyMeasurable

/-- The independent-increment averaging rule used by the Burgers example,
proved from the defining set-integral identity of conditional expectation. -/
theorem conditional_independent_bounded_average
    {Ω E K : Type*} (G : MeasurableSpace Ω) {m : MeasurableSpace Ω} [MeasurableSpace E] [MeasurableSpace K]
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G ≤ m)
    (X : Ω → E) (Y : Ω → K) (hX : Measurable[G] X) (hY : Measurable Y)
    (hind : Indep G (MeasurableSpace.comap Y inferInstance) P)
    (f : E × K → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z, ‖f z‖ ≤ B) :
    P[(fun w => f (X w,Y w))|G] =ᵐ[P] fun w => ∫ y, f (X w,y) ∂P.map Y := by
  classical
  have hXm : Measurable X := hX.mono hG le_rfl
  have hav : StronglyMeasurable (fun x => ∫ y, f (x,y) ∂P.map Y) :=
    hf.stronglyMeasurable.integral_prod_right'
  have hab x : ‖∫ y, f (x,y) ∂P.map Y‖ ≤ B := by
    calc
      _ ≤ ∫ y, ‖f (x,y)‖ ∂P.map Y := norm_integral_le_integral_norm _
      _ ≤ ∫ y, B ∂P.map Y := integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        (integrable_const B) (ae_of_all _ fun y => hb (x,y))
      _ = B := by simp [Measure.map_apply hY MeasurableSet.univ]
  have hami : Integrable (fun w => ∫ y, f (X w,y) ∂P.map Y) P :=
    Integrable.of_bound (hav.comp_measurable hXm).aestronglyMeasurable B (ae_of_all _ fun w => hab (X w))
  have hfi : Integrable (fun w => f (X w,Y w)) P :=
    Integrable.of_bound (hf.comp (hXm.prodMk hY)).aestronglyMeasurable B (ae_of_all _ fun w => hb _)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hG hfi
    (fun s _ _ => hami.integrableOn) ?_ (hav.comp_measurable hX).aestronglyMeasurable).symm
  intro s hs _
  let U : Ω → E × Bool := fun w => (X w,if w ∈ s then true else false)
  have hUG : Measurable[G] U := hX.prodMk (Measurable.ite hs measurable_const measurable_const)
  have hUm : Measurable U := hUG.mono hG le_rfl
  have hUY : IndepFun U Y P := indep_of_indep_of_le_left hind hUG.comap_le
  let k : (E × Bool) × K → ℝ := fun z => if z.1.2 then f (z.1.1,z.2) else 0
  have hk : Measurable k := Measurable.ite
    ((measurable_snd.comp measurable_fst) (measurableSet_singleton true))
    (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)) measurable_const
  have hkb z : ‖k z‖ ≤ B := by
    dsimp [k]
    split
    · exact hb _
    · simpa using hB
  have he := independent_bounded_average P U Y hUm hY hUY k hk B hkb
  have hleft : (fun w => k (U w,Y w)) = s.indicator (fun w => f (X w,Y w)) := by
    funext w; simp [k,U,Set.indicator]
  have hright : (fun w => ∫ y, k (U w,y) ∂P.map Y) = s.indicator (fun w => ∫ y, f (X w,y) ∂P.map Y) := by
    funext w; by_cases hw : w ∈ s <;> simp [k,U,Set.indicator,hw]
  rw [hleft,hright,integral_indicator (hG _ hs),integral_indicator (hG _ hs)] at he
  exact he.symm

end Asakura.Chapter5

import Chapter5IndependentAverage

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Independent averaging for integrable, possibly unbounded, payoffs. -/
theorem independent_integrable_average
    {Ω E K : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace K]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → E) (Y : Ω → K) (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y P) (f : E × K → ℝ) (hf : Measurable f)
    (hi : Integrable (fun w => f (X w,Y w)) P) :
    Integrable (fun w => ∫ y,f (X w,y) ∂P.map Y) P ∧
      (∫ w,f (X w,Y w) ∂P)=∫ w,(∫ y,f (X w,y) ∂P.map Y) ∂P := by
  have hp : Integrable f ((P.map X).prod (P.map Y)) := by
    rw [←hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
    exact (integrable_map_measure hf.aestronglyMeasurable (hX.prodMk hY).aemeasurable).mpr hi
  have hm := hf.stronglyMeasurable.integral_prod_right' (ν:=P.map Y)
  refine ⟨hp.integral_prod_left.comp_aemeasurable hX.aemeasurable,?_⟩
  calc
    _ = ∫ z,f z ∂P.map (fun w => (X w,Y w)) :=
      (integral_map (hX.prodMk hY).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ z,f z ∂(P.map X).prod (P.map Y) := by rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
    _ = ∫ x,(∫ y,f (x,y) ∂P.map Y) ∂P.map X := integral_prod f hp
    _ = _ := integral_map hX.aemeasurable hm.aestronglyMeasurable

/-- Conditional independent-increment averaging for all integrable payoffs,
so that the European option argument does not silently assume boundedness. -/
theorem conditional_independent_integrable_average
    {Ω E K : Type*} (G : MeasurableSpace Ω) {m : MeasurableSpace Ω} [MeasurableSpace E] [MeasurableSpace K]
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G≤m)
    (X : Ω → E) (Y : Ω → K) (hX : Measurable[G] X) (hY : Measurable Y)
    (hind : Indep G (MeasurableSpace.comap Y inferInstance) P)
    (f : E × K → ℝ) (hf : Measurable f) (hi : Integrable (fun w => f (X w,Y w)) P) :
    P[(fun w => f (X w,Y w))|G]=ᵐ[P] fun w => ∫ y,f (X w,y) ∂P.map Y := by
  classical
  have hXm : Measurable X := hX.mono hG le_rfl
  have hXY : IndepFun X Y P := indep_of_indep_of_le_left hind hX.comap_le
  have hav : StronglyMeasurable (fun x => ∫ y,f (x,y) ∂P.map Y) :=
    hf.stronglyMeasurable.integral_prod_right'
  have hami := (independent_integrable_average P X Y hXm hY hXY f hf hi).1
  apply (ae_eq_condExp_of_forall_setIntegral_eq hG hi
    (fun s _ _ => hami.integrableOn) ?_ (hav.comp_measurable hX).aestronglyMeasurable).symm
  intro s hs _
  let U : Ω → E × Bool := fun w => (X w,if w∈s then true else false)
  have hUG : Measurable[G] U := hX.prodMk (Measurable.ite hs measurable_const measurable_const)
  have hUm : Measurable U := hUG.mono hG le_rfl
  have hUY : IndepFun U Y P := indep_of_indep_of_le_left hind hUG.comap_le
  let k : (E × Bool) × K → ℝ := fun z => if z.1.2 then f (z.1.1,z.2) else 0
  have hk : Measurable k := Measurable.ite
    ((measurable_snd.comp measurable_fst) (measurableSet_singleton true))
    (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)) measurable_const
  have hleft : (fun w => k (U w,Y w))=s.indicator (fun w => f (X w,Y w)) := by
    funext w; simp [k,U,Set.indicator]
  have hki : Integrable (fun w => k (U w,Y w)) P := by rw [hleft];exact hi.indicator (hG _ hs)
  have he := (independent_integrable_average P U Y hUm hY hUY k hk hki).2
  have hright : (fun w => ∫ y,k (U w,y) ∂P.map Y)=s.indicator (fun w => ∫ y,f (X w,y) ∂P.map Y) := by
    funext w;by_cases hw : w∈s <;> simp [k,U,Set.indicator,hw]
  rw [hleft,hright,integral_indicator (hG _ hs),integral_indicator (hG _ hs)] at he
  exact he.symm

end Asakura.Chapter11

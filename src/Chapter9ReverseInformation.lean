import Chapter9FutureCylinderTransition
import Chapter9FiniteObservationExtension
import Chapter9ConditionalPairing
import Mathlib.Data.Finset.Sort

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

 theorem indicator_bounded_borel {E : Type*} [MeasurableSpace E]
    (A : Set E) (hA : MeasurableSet A) : IsBoundedBorel (A.indicator (fun _ => (1:ℝ))) := by
  refine ⟨measurable_const.indicator hA,1,by norm_num,?_⟩
  intro x
  by_cases hx : x∈A <;> simp [hx]

open scoped Classical in
 theorem finiteTestProduct_indicator {ι E Ω : Type*} (X : ι → Ω → E) (A : ι → Set E)
    (L : List ι) (w : Ω) :
    finiteTestProduct X (fun t => (A t).indicator (fun _ => (1:ℝ))) L w=
      if ∀ t∈L,X t w∈A t then 1 else 0 := by
  classical
  induction L with
  | nil => simp [finiteTestProduct]
  | cons t L ih =>
    by_cases ht : X t w∈A t <;> by_cases hL : ∀ u∈L,X u w∈A u <;>
      simp [finiteTestProduct,ih,ht,hL]

/-- Reversing the direction of information for a Markov process: the
conditional law of a past variable given the entire future depends only on
the present. Finite cylinders and the monotone-class extension are proved,
not included as a reverse-Markov assumption. -/
theorem reverse_information_regression {Ω E ι : Type*}
    [m : MeasurableSpace Ω] [MeasurableSpace E] [LinearOrder ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ι → MeasurableSpace Ω)
    (hmono : Monotone F) (hle : ∀ t,F t≤m) (X : ι → Ω → E) (hX : ∀ t,Measurable[F t] (X t))
    (htrans : ∀ s t,s≤t → ∀ f : E → ℝ,IsBoundedBorel f →
      ∃ g : E → ℝ,IsBoundedBorel g ∧ P[(fun w => f (X t w))|F s]=ᵐ[P] (fun w => g (X s w)))
    (s : ι) (Y : Ω → ℝ) (hY : @IsBoundedBorel Ω m Y) (hYF : Measurable[F s] Y)
    (z : E → ℝ) (hz : IsBoundedBorel z)
    (hreg : P[Y|MeasurableSpace.comap (X s) inferInstance]=ᵐ[P] (fun w => z (X s w))) :
    P[Y|MeasurableSpace.comap (fun w (t : {t : ι // s≤t}) => X t w) MeasurableSpace.pi]=ᵐ[P]
      (fun w => z (X s w)) := by
  classical
  letI : MeasurableSpace Ω := m
  let J := {t : ι // s≤t}
  let s0 : J := ⟨s,le_rfl⟩
  let XJ : J → Ω → E := fun t => X t
  let W := fun w (t : J) => X t w
  let G := MeasurableSpace.comap W MeasurableSpace.pi
  letI : MeasurableSpace Ω := m
  have hZ : @IsBoundedBorel Ω m (fun w => z (X s w)) := hz.comp _ ((hX s).mono (hle s) le_rfl)
  have hmZ : Measurable[G] (fun w => z (X s w)) :=
    hz.1.comp ((measurable_pi_apply s0).comp (comap_measurable W))
  apply conditional_expectation_of_finite_observations (m := m) P XJ
    (fun t => (hX t).mono (hle t) le_rfl) Y _ (hY.integrable P) (hZ.integrable P) hmZ.aestronglyMeasurable
  intro I A hA
  letI : MeasurableSpace Ω := m
  let f := fun t : J => (A t).indicator (fun _ => (1:ℝ))
  let L := I.sort (· ≤ ·)
  let V := finiteTestProduct XJ f L
  have hf (t : J) : IsBoundedBorel (f t) := indicator_bounded_borel _ (hA t)
  have htr : ∀ a b : J,a≤b → ∀ f : E → ℝ,IsBoundedBorel f →
      ∃ g : E → ℝ,IsBoundedBorel g ∧ P[(fun w => f (XJ b w))|F a]=ᵐ[P] (fun w => g (XJ a w)) :=
    fun a b hab f hbf => htrans a b hab f hbf
  obtain ⟨g,hg,hfuture⟩ := future_cylinder_conditional_transition P (fun t : J => F t)
    (fun a b hab => hmono hab) (fun t => hle t) XJ (fun t => hX t) htr f hf L s0
    (I.pairwise_sort _) (fun t _ => t.property)
  have hV : Integrable V P :=
    (finiteTestProduct_bounded XJ (fun t => (hX t).mono (hle t) le_rfl) f hf L).integrable P
  have he := future_test_regression_pairing P (F s) (hle s) (X s) (hX s) Y (fun w => z (X s w)) V
    hY hZ hV hYF (hz.1.comp (hX s)) hreg g hg hfuture
  let B : Set Ω := {w | ∀ t∈I,XJ t w∈A t}
  have hB : MeasurableSet B := by
    have heB : B=⋂ t∈I,{w | XJ t w∈A t} := by ext w; simp [B]
    rw [heB]
    exact I.measurableSet_biInter (fun t _ => ((hX t).mono (hle t) le_rfl) (hA t))
  have hVeq (w : Ω) : V w=B.indicator (fun _ => (1:ℝ)) w := by
    rw [show V w=finiteTestProduct XJ f L w from rfl,finiteTestProduct_indicator]
    simp only [L,Finset.mem_sort,Set.indicator,B,Set.mem_ofPred_eq]
  have heY : (fun w => Y w*V w)=B.indicator Y := by
    funext w
    rw [hVeq]
    by_cases hw : w∈B <;> simp [hw]
  have heZ : (fun w => z (X s w)*V w)=B.indicator (fun w => z (X s w)) := by
    funext w
    rw [hVeq]
    by_cases hw : w∈B <;> simp [hw]
  rw [heY,heZ,integral_indicator hB,integral_indicator hB] at he
  exact he
end Asakura.Chapter9

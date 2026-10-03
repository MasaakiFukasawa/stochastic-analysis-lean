import EndToEndHJMConstructedGlobal

open MeasureTheory Set
namespace Asakura.EndToEnd
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Piecewise continuous sample functions and measurable random sections are
jointly measurable. Singleton pieces may contain every partition endpoint. -/
theorem piecewise_parameter_measurable {Ω : Type*} [MeasurableSpace Ω]
    (f : ℝ → Ω → ℝ) (A : ℕ → Set ℝ) (hA : ∀n,MeasurableSet (A n))
    (hcover : ∀x,∃n,x∈A n)
    (hc : ∀n w,ContinuousOn (fun x => f x w) (A n))
    (hm : ∀x,Measurable (f x)) : Measurable (fun z : ℝ × Ω => f z.1 z.2) := by
  classical
  have hp n : Measurable (fun z : A n × Ω => f z.1 z.2) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun w => (continuousOn_iff_continuous_domRestrict).mp (hc n w)) (fun x => hm x)
  let g := fun n (z : ℝ × Ω) => if z.1∈A n then f z.1 z.2 else 0
  have hg n : Measurable (g n) := by
    apply measurable_of_restrict_of_restrict_compl ((hA n).preimage measurable_fst)
    · have hh : Measurable (fun z : (Prod.fst ⁻¹' A n : Set (ℝ × Ω)) =>
          f (⟨z.val.1,z.property⟩ : A n) z.val.2) :=
        (hp n).comp (((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk
          (measurable_snd.comp measurable_subtype_coe))
      convert hh using 1
      funext z
      change (if z.val.1∈A n then f z.val.1 z.val.2 else 0)=_
      exact if_pos z.property
    · change Measurable (fun z : ↥((Prod.fst ⁻¹' A n : Set (ℝ × Ω))ᶜ) => g n z.val)
      have he : (fun z : ↥((Prod.fst ⁻¹' A n : Set (ℝ × Ω))ᶜ) => g n z.val)=(fun _ => (0:ℝ)) := by
        funext z
        exact if_neg z.property
      rw [he]
      exact measurable_const
  have hs := Measurable.find hg (fun n => (hA n).preimage measurable_fst)
    (fun z : ℝ × Ω => hcover z.1)
  convert hs using 1
  funext z
  simp only [g,if_pos (Nat.find_spec (hcover z.1))]

/-- The initial maturity integral is measurable in the initial information;
no independence or triviality of that information is needed. -/
theorem piecewise_initial_integral_measurable {Ω : Type*} [MeasurableSpace Ω]
    (f : ℝ → Ω → ℝ) (A : ℕ → Set ℝ) (hA : ∀n,MeasurableSet (A n))
    (hcover : ∀x,∃n,x∈A n)
    (hc : ∀n w,ContinuousOn (fun x => f x w) (A n))
    (hm : ∀x,Measurable (f x)) (U : ℝ) :
    Measurable (fun w => ∫x in Ioc 0 U,f x w) :=
  (piecewise_parameter_measurable f A hA hcover hc hm).stronglyMeasurable.integral_prod_left'.measurable

#print axioms piecewise_parameter_measurable
#print axioms piecewise_initial_integral_measurable
end Asakura.EndToEnd

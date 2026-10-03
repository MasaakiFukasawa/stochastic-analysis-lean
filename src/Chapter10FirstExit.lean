import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

open Set
namespace Asakura.Chapter10

/-- First level crossing for a continuous scalar path on a compact interval. -/
theorem first_level_crossing (f : ℝ → ℝ) (hf : Continuous f)
    (T R : ℝ) (hT : 0≤T) (h0 : f 0<R) (hEnd : R≤f T) :
    ∃ τ∈Ioc 0 T,f τ=R ∧ ∀ s∈Icc 0 τ,f s≤R := by
  let E := Icc (0:ℝ) T ∩ f ⁻¹' {R}
  have hEc : IsCompact E := isCompact_Icc.inter_right (isClosed_singleton.preimage hf)
  have hEn : E.Nonempty := by
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc hT hf.continuousOn ⟨h0.le,hEnd⟩
    exact ⟨t,ht,he⟩
  obtain ⟨τ,hτ⟩ := hEc.exists_isLeast hEn
  have ht : τ∈Icc (0:ℝ) T := hτ.1.1
  have he : f τ=R := hτ.1.2
  have ht0 : 0<τ := lt_of_le_of_ne ht.1 (by intro hz; rw [←hz] at he; linarith)
  refine ⟨τ,⟨ht0,ht.2⟩,he,?_⟩
  intro s hs
  by_contra hn
  have hgt : R<f s := lt_of_not_ge hn
  obtain ⟨u,hu,hue⟩ := intermediate_value_Icc hs.1 hf.continuousOn ⟨h0.le,hgt.le⟩
  have htu : τ≤u := hτ.2 ⟨⟨hu.1,hu.2.trans (hs.2.trans ht.2)⟩,hue⟩
  have hus : u<s := lt_of_le_of_ne hu.2 (by intro heq; rw [heq] at hue; linarith)
  exact (not_lt_of_ge hs.2) (htu.trans_lt hus)

end Asakura.Chapter10

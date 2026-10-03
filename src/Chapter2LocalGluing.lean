import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

open Set Filter
open scoped Topology
namespace Asakura.Chapter2Complete

/-- The pointwise gluing argument in the construction of local covariation.
The only compatibility input is equality after stopping, not convergence. -/
theorem compatible_stops_eventually_constant
    {ι E : Type*} [LinearOrder ι] [OrderTop ι]
    (τ : ℕ → ι) (hτ : Monotone τ)
    (hcofinal : ∀ t : ι, t < ⊤ → ∃ n, t ≤ τ n)
    (A : ℕ → ι → E)
    (hcompat : ∀ n m, n ≤ m → ∀ t, A m (min (τ n) t) = A n t)
    (t : ι) (ht : t < ⊤) :
    ∃ z : E, ∀ᶠ n in atTop, A n t = z := by
  obtain ⟨n, hn⟩ := hcofinal t ht
  refine ⟨A n t, eventually_atTop.2 ⟨n, ?_⟩⟩
  intro m hnm
  simpa only [min_eq_right hn] using hcompat n m hnm t

/-- An actual glued function exists, and stopping recovers every original
piece, at every time. No convergence or gluing conclusion is assumed. -/
theorem compatible_stops_glue
    {ι E : Type*} [LinearOrder ι] [OrderTop ι] [Nonempty E]
    (τ : ℕ → ι) (hτ : Monotone τ) (hτtop : ∀ n, τ n < ⊤)
    (hcofinal : ∀ t : ι, t < ⊤ → ∃ n, t ≤ τ n)
    (A : ℕ → ι → E)
    (hcompat : ∀ n m, n ≤ m → ∀ t, A m (min (τ n) t) = A n t) :
    ∃ G : ι → E,
      (∀ t, t < ⊤ → ∀ᶠ n in atTop, A n t = G t) ∧
      (∀ n t, G (min (τ n) t) = A n t) := by
  classical
  have hex := compatible_stops_eventually_constant τ hτ hcofinal A hcompat
  let G : ι → E := fun t => if ht : t < ⊤ then (hex t ht).choose else Classical.arbitrary E
  have he (t) (ht : t < ⊤) : ∀ᶠ n in atTop, A n t = G t := by
    simpa only [G, dite_eq_left ht] using (hex t ht).choose_spec
  refine ⟨G, he, ?_⟩
  intro n t
  have ht : min (τ n) t < ⊤ := lt_of_le_of_lt (min_le_left _ _) (hτtop n)
  obtain ⟨m, hm⟩ := eventually_atTop.1 (he _ ht)
  have hm' := hm (max m n) (le_max_left _ _)
  exact hm'.symm.trans (hcompat n (max m n) (le_max_right _ _) t)

/-- Cofinal stopped identities determine a process uniquely below T. -/
theorem cofinal_stops_determine
    {ι E : Type*} [LinearOrder ι] [OrderTop ι]
    (τ : ℕ → ι)
    (hcofinal : ∀ t : ι, t < ⊤ → ∃ n, t ≤ τ n)
    (X Y : ι → E)
    (h : ∀ n t, X (min (τ n) t) = Y (min (τ n) t)) :
    ∀ t, t < ⊤ → X t = Y t := by
  intro t ht
  obtain ⟨n, hn⟩ := hcofinal t ht
  simpa only [min_eq_right hn] using h n t

/-- Local continuity follows because the glued path agrees with a single
continuous stopped path on a whole neighbourhood of each time below T. -/
theorem glued_path_continuous_below_terminal
    {ι : Type*} [LinearOrder ι] [OrderTop ι] [TopologicalSpace ι]
    [OrderTopology ι]
    (τ : ℕ → ι) (hcofinal : ∀ t : ι, t < ⊤ → ∃ n, t < τ n)
    (A : ℕ → ι → ℝ) (hA : ∀ n, Continuous (A n)) (G : ι → ℝ)
    (hstop : ∀ n t, G (min (τ n) t) = A n t) :
    ∀ t, t < ⊤ → ContinuousAt G t := by
  intro t ht
  obtain ⟨n, hn⟩ := hcofinal t ht
  apply (hA n).continuousAt.congr_of_eventuallyEq
  filter_upwards [gt_mem_nhds hn] with s hs
  simpa only [min_eq_right (le_of_lt hs)] using hstop n s

/-- Pointwise eventual constancy of measurable stopped pieces proves
measurability of the glued random variable without a measurable choice. -/
theorem glued_value_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (A : ℕ → Ω → ℝ) (hA : ∀ n, Measurable (A n)) (G : Ω → ℝ)
    (hG : ∀ ω, ∀ᶠ n in atTop, A n ω = G ω) : Measurable G := by
  apply measurable_of_tendsto_metrizable hA
  rw [tendsto_pi_nhds]
  intro ω
  have he : (fun n => A n ω) =ᶠ[atTop] (fun _ => G ω) := hG ω
  exact tendsto_const_nhds.congr' he.symm

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.compatible_stops_eventually_constant
#print axioms Asakura.Chapter2Complete.compatible_stops_glue
#print axioms Asakura.Chapter2Complete.cofinal_stops_determine

#print axioms Asakura.Chapter2Complete.glued_path_continuous_below_terminal
#print axioms Asakura.Chapter2Complete.glued_value_measurable

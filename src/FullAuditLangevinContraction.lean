import FullAuditTransportFlow

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace
namespace Asakura.FullAudit
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Assemble the written proof: Hessian bound, noise cancellation, pathwise
 integrating factor, product coupling, expectation, and infimum. Existence,
 continuity and joint measurability of the SDE solution are prior results. -/
theorem langevin_wasserstein_contraction {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ → E → Ω → E) (W : Ω → ℝ → E)
    (g : E → E) (H : E → E →L[ℝ] E) (κ t : ℝ) (ht : 0 ≤ t)
    (hD : ∀ x, HasFDerivAt g (H x) x)
    (hH : ∀ x v, κ*‖v‖^2 ≤ ⟪v,H x v⟫_ℝ)
    (hm : Measurable (Function.uncurry (X t)))
    (hpaths : ∀ x, ∀ᵐ ω ∂P, Continuous (fun u => X u x ω) ∧ X 0 x ω = x ∧
      ∀ u ∈ Icc 0 t, X u x ω = x-(∫ s in (0:ℝ)..u, g (X s x ω))+W ω u)
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x : E => x) 2 μ) (hν : MemLp (fun x : E => x) 2 ν) :
    transportDistance (flowLaw μ P (X t)) (flowLaw ν P (X t)) ≤
      Real.exp (-κ*t)*transportDistance μ ν := by
  have hg : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)
  have hLip : ∀ x y, ∀ᵐ ω ∂P, ‖X t x ω-X t y ω‖ ≤ Real.exp (-κ*t)*‖x-y‖ := by
    intro x y
    filter_upwards [hpaths x,hpaths y] with ω hx hy
    have hd := langevin_common_noise_difference (fun u => X u x ω) (fun u => X u y ω)
      (W ω) g x y t hx.1 hy.1 hg hx.2.2 hy.2.2
    have h := langevin_path_contraction (fun u => X u x ω) (fun u => X u y ω) g κ t ht
      hx.1.continuousOn hy.1.continuousOn (langevin_gradient_monotone g H κ hD hH) hd t ⟨ht,le_rfl⟩
    simpa only [hx.2.1,hy.2.1] using h
  haveI := quadratic_coupling_nonempty μ ν hμ hν
  exact shared_noise_transport_contraction μ ν P (X t) hm _ (Real.exp_pos _) hLip

/-- Substitute the invariant law in the first contraction inequality. -/
theorem langevin_convergence_to_invariant {E Ω : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSpace Ω] (μ π : Measure E) (P : Measure Ω)
    (F : E → Ω → E) (κ t : ℝ)
    (hcontr : transportDistance (flowLaw μ P F) (flowLaw π P F) ≤
      Real.exp (-κ*t)*transportDistance μ π)
    (hinv : flowLaw π P F = π) :
    transportDistance (flowLaw μ P F) π ≤ Real.exp (-κ*t)*transportDistance μ π := by
  simpa only [hinv] using hcontr

/-- A strict contraction at one positive time forces two invariant finite-
 second-moment laws to agree. Zero transport distance is proved to separate
 measures, rather than taken as an extra assumption. -/
theorem langevin_invariant_unique {E Ω : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    (μ π : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : MemLp (fun x : E => x) 2 μ) (hπ : MemLp (fun x : E => x) 2 π)
    (P : Measure Ω) (F : E → Ω → E) (κ t : ℝ) (hκ : 0 < κ) (ht : 0 < t)
    (hcontr : transportDistance (flowLaw μ P F) (flowLaw π P F) ≤
      Real.exp (-κ*t)*transportDistance μ π)
    (hinvμ : flowLaw μ P F = μ) (hinvπ : flowLaw π P F = π) : μ=π := by
  haveI := quadratic_coupling_nonempty μ π hμ hπ
  rw [hinvμ,hinvπ] at hcontr
  have he : Real.exp (-κ*t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hn : 0 ≤ transportDistance μ π := Real.sqrt_nonneg _
  have hz : transportDistance μ π = 0 := by nlinarith
  have hsq : transportEnergy μ π = 0 := by
    have h := Real.sq_sqrt (transport_energy_nonnegative μ π)
    change (transportDistance μ π)^2 = transportEnergy μ π at h
    rw [hz,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at h
    exact h.symm
  exact zero_transport_measures_equal μ π hsq

end Asakura.FullAudit

import Chapter8StationaryCovariance

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit

/-- Conditioning the future observable and pushing the initial variable to
its stationary law gives the covariance used in the manuscript. -/
theorem markov_stationary_covariance {Ω E : Type*} {G m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G ≤ m)
    (π : Measure E) [IsProbabilityMeasure π] (hπ : MemLp (fun x : E => x) 2 π)
    (Y Z : Ω → E) (hY : Measurable Y) (hZ : Measurable Z)
    (hYlaw : P.map Y = π) (hZlaw : P.map Z = π)
    (hYG : AEStronglyMeasurable[G] Y P)
    (X : E → Ω → E) (hX : ∀ x, MemLp (X x) 2 P)
    (f : E → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) (κ t : ℝ)
    (hLip : ∀ x y, ∀ᵐ ω ∂P, ‖X x ω-X y ω‖ ≤ Real.exp (-κ*t)*‖x-y‖)
    (hCE : P[(fun ω => f (Z ω))|G] =ᵐ[P] fun ω => ∫ η,f (X (Y ω) η) ∂P) :
    |cov[fun ω => f (Y ω),fun ω => f (Z ω);P]| ≤
      (L:ℝ)^2*(∫ x, ‖x‖^2 ∂π)*Real.exp (-κ*t) := by
  letI : MeasurableSpace Ω := m
  let a : ℝ≥0 := ⟨Real.exp (-κ*t),(Real.exp_pos _).le⟩
  let g := fun x => ∫ ω,f (X x ω) ∂P
  have hg : LipschitzWith (L*a) g := lipschitz_transition_from_coupling P X hX f L a hf hLip
  have hfπ := lipschitz_observable_memLp π (fun x => x) hπ f L hf
  have hgπ := lipschitz_observable_memLp π (fun x => x) hπ g (L*a) hg
  have hfY : MemLp (fun ω => f (Y ω)) 2 P := by
    apply MemLp.comp_of_map (f := Y) _ hY.aemeasurable
    rwa [hYlaw]
  have hfZ : MemLp (fun ω => f (Z ω)) 2 P := by
    apply MemLp.comp_of_map (f := Z) _ hZ.aemeasurable
    rwa [hZlaw]
  have hgY : MemLp (fun ω => g (Y ω)) 2 P := by
    have hh : MemLp g 2 (P.map Y) := by rwa [hYlaw]
    convert hh.comp_of_map hY.aemeasurable using 1 <;> rfl
  have hc := covariance_conditional_future P hG (fun ω => f (Y ω)) (fun ω => f (Z ω))
    (fun ω => g (Y ω)) hfY hfZ hgY (hf.continuous.comp_aestronglyMeasurable hYG) hCE
  have hmap : cov[f,g;π] = cov[fun ω => f (Y ω),fun ω => g (Y ω);P] := by
    rw [← hYlaw]
    exact covariance_map_fun hf.continuous.aestronglyMeasurable hg.continuous.aestronglyMeasurable hY.aemeasurable
  rw [hc,← hmap]
  exact stationary_transition_covariance P π hπ X hX f L hf κ t hLip

end Asakura.Chapter8

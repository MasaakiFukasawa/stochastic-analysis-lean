import Chapter8NewtonCoordinates
import Chapter8ConjugateFlow

open MeasureTheory Set
namespace Asakura.Chapter8
open Asakura.FullAudit
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance : MeasurableSpace (WithLp 2 (E × E)) := borel _
local instance : BorelSpace (WithLp 2 (E × E)) := ⟨rfl⟩

theorem newton_finite_shared_noise_transport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (l u δ : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (hδ : Real.sqrt u - Real.sqrt l < δ)
    (g : E → E) (H : E → E →L[ℝ] E)
    (hd : ∀ x, HasFDerivAt g (H x) x) (hH : Continuous H)
    (hsym : ∀ x, (H x).toLinearMap.IsSymmetric)
    (hbound : ∀ x z, l*‖z‖^2 ≤ inner ℝ z (H x z) ∧ inner ℝ z (H x z) ≤ u*‖z‖^2)
    (T : ℝ) (hT : 0 ≤ T)
    (X : ℝ → (E × E) → Ω → (E × E)) (W : Ω → ℝ → E)
    (hm : ∀ t ≥ 0, Measurable (Function.uncurry (X t)))
    (hpaths : ∀ x, ∀ᵐ ω ∂P,
      Continuous (fun t => (X t x ω).1) ∧ Continuous (fun t => (X t x ω).2) ∧
      X 0 x ω = x ∧
      (∀ t ∈ Icc 0 T, (X t x ω).1 = x.1+∫ s in (0:ℝ)..t,(X s x ω).2) ∧
      (∀ t ∈ Icc 0 T, (X t x ω).2 = x.2+(∫ s in (0:ℝ)..t,-g (X s x ω).1-δ • (X s x ω).2)+W ω t)) :
    ∃ b r : ℝ, 0 < r ∧ ∃ hp : 0 < b+δ^2/4,
      ∀ (t : ℝ), t ∈ Icc 0 T → ∀ (μ ν : Measure (E × E)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      MemLp (fun z : E × E => z) 2 μ → MemLp (fun z : E × E => z) 2 ν →
      transportDistance ((flowLaw μ P (X t)).map (newtonCoordinateEquiv δ b hp))
        ((flowLaw ν P (X t)).map (newtonCoordinateEquiv δ b hp)) ≤
        Real.exp (-r*t)*transportDistance (μ.map (newtonCoordinateEquiv δ b hp))
          (ν.map (newtonCoordinateEquiv δ b hp)) := by
  obtain ⟨b,r,hr,hp,hpath⟩ := newton_integral_path_contraction (E := E) l u δ hl hlu hδ
  refine ⟨b,r,hr,hp,?_⟩
  intro t ht μ ν hμprob hνprob hμ hν
  letI := hμprob
  letI := hνprob
  let A := newtonCoordinateEquiv (E := E) δ b hp
  let e := A.toHomeomorph.toMeasurableEquiv
  have hμ' : MemLp (fun z : WithLp 2 (E × E) => z) 2 (μ.map e) := by
    apply (e.memLp_map_measure_iff).mpr
    convert A.toContinuousLinearMap.comp_memLp' hμ using 1 <;> rfl
  have hν' : MemLp (fun z : WithLp 2 (E × E) => z) 2 (ν.map e) := by
    apply (e.memLp_map_measure_iff).mpr
    convert A.toContinuousLinearMap.comp_memLp' hν using 1 <;> rfl
  apply conjugate_shared_noise_contraction e μ ν P (X t) (hm t ht.1) hμ' hν'
    (Real.exp (-r*t)) (Real.exp_pos _)
  intro x y
  filter_upwards [hpaths x,hpaths y] with ω hx hy
  have hh := hpath g H hd hH hsym hbound
    (fun s => (X s x ω).1) (fun s => (X s x ω).2)
    (fun s => (X s y ω).1) (fun s => (X s y ω).2) (W ω)
    x.1 x.2 y.1 y.2 t ht.1 hx.1 hx.2.1 hy.1 hy.2.1
    (fun s hs => hx.2.2.2.1 s ⟨hs.1,hs.2.trans ht.2⟩) (fun s hs => hy.2.2.2.1 s ⟨hs.1,hs.2.trans ht.2⟩)
    (fun s hs => hx.2.2.2.2 s ⟨hs.1,hs.2.trans ht.2⟩) (fun s hs => hy.2.2.2.2 s ⟨hs.1,hs.2.trans ht.2⟩) t ⟨ht.1,le_rfl⟩
  rw [hx.2.2.1,hy.2.2.1] at hh
  have hn := newton_norm_contraction_of_energy δ b r t hp.le
    (X t x ω-X t y ω) (x-y) hh
  change ‖A (X t x ω)-A (X t y ω)‖ ≤ Real.exp (-r*t)*‖A x-A y‖
  rw [← map_sub A,← map_sub A]
  exact hn

end
end Asakura.Chapter8

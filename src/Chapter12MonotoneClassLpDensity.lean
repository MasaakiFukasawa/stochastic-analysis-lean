import Chapter12DominatedLpLimit
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

open Set Filter MeasureTheory MeasurableSpace
open scoped Topology ENNReal symmDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The simple-function step following the monotone-class theorem:
a dense family of measurable sets suffices for density in finite Lp. -/
theorem lp_closed_subspace_of_dense_sets {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    (C : Set (MeasuredSets P)) (hC : Dense C)
    (V : Submodule ℝ (Lp ℝ p P)) (hV : IsClosed (V : Set (Lp ℝ p P)))
    (hc : ∀ s∈C,indicatorConstLp p s.property (measure_ne_top P _) (1:ℝ)∈V) :
    ∀ f : Lp ℝ p P,f∈V := by
  let I : MeasuredSets P → Lp ℝ p P := fun s =>
    indicatorConstLp p s.property (measure_ne_top P _) (1:ℝ)
  have hi : Continuous I := by
    apply continuous_indicatorConstLp_set (μ := P) (p := p) (s := fun s : MeasuredSets P => (s : Set Ω)) hp
    intro s
    simpa [MeasuredSets.edist_def] using
      (((continuous_id : Continuous (fun t : MeasuredSets P => t)).edist (continuous_const : Continuous (fun _ : MeasuredSets P => s))).tendsto s :
        Tendsto (fun t : MeasuredSets P => edist t s) (𝓝 s) (𝓝 (edist s s)))
  have hall : ∀ s : MeasuredSets P,I s∈V :=
    hC.induction hc (hV.preimage hi)
  apply Lp.induction hp (fun f => f∈V) _ _ hV
  · intro c s hs hPs
    have hmem := V.smul_mem c (hall ⟨s,hs⟩)
    have he : c • I ⟨s,hs⟩=indicatorConstLp p hs hPs.ne c := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_smul c (I ⟨s,hs⟩),
        (indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := measure_ne_top P s) (c := (1:ℝ))),
        (indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hPs.ne) (c := c))] with w h1 h2 h3
      rw [h1,Pi.smul_apply,h3]
      change c*(I ⟨s,hs⟩ w)=_
      rw [h2]
      by_cases hw : w∈s <;> simp [hw]
    rw [he] at hmem
    exact hmem
  · intro f g hf hg _ hv hw
    exact V.add_mem hv hw

/-- Here the density of sets is supplied by the monotone-class theorem
inside `dense_of_generateFrom_isSetRing`, before applying simple-function
approximation. This is the route used in the manuscript. -/
theorem lp_closed_subspace_of_generating_ring {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    (C : Set (Set Ω)) (hC : IsSetRing C)
    (hcover : ∃ A : Set (Set Ω),A.Countable ∧ A⊆C ∧ P (⋃₀ A)ᶜ=0)
    (hgen : m=generateFrom C)
    (V : Submodule ℝ (Lp ℝ p P)) (hV : IsClosed (V : Set (Lp ℝ p P)))
    (hc : ∀ s∈C,∀ hs : MeasurableSet s,indicatorConstLp p hs (measure_ne_top P s) (1:ℝ)∈V) :
    ∀ f : Lp ℝ p P,f∈V := by
  apply lp_closed_subspace_of_dense_sets P p hp
    ((SetLike.coe : MeasuredSets P → Set Ω) ⁻¹' C)
    (dense_of_generateFrom_isSetRing hC hcover hgen) V hV
  intro s hs
  exact hc s hs s.property

end Asakura.Chapter12

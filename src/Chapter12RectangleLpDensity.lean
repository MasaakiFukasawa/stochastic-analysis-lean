import Chapter12PiSystemLpDensity
import Chapter12SmoothRectangleIndicator
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi

open Set Filter MeasureTheory MeasurableSpace
open scoped Topology ENNReal ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Finite-dimensional rectangle density, obtained from the monotone-class
theorem rather than assumed as an approximation hypothesis. -/
theorem rectangle_indicators_Lp_dense {ι : Type*} [Fintype ι]
    (P : Measure (ι → ℝ)) [IsFiniteMeasure P] (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    (V : Submodule ℝ (Lp ℝ p P)) (hV : IsClosed (V : Set (Lp ℝ p P)))
    (hu : indicatorConstLp p MeasurableSet.univ (measure_ne_top P _) (1:ℝ)∈V)
    (hr : ∀ a b : ι → ℝ,∀ hs : MeasurableSet (Set.pi univ (fun i => Ioo (a i) (b i))),
      indicatorConstLp p hs (measure_ne_top P _) (1:ℝ)∈V) :
    ∀ f : Lp ℝ p P,f∈V := by
  classical
  let C : Set (Set ℝ) := ⋃ (a : ℚ) (b : ℚ) (_ : a<b),{Ioo (a:ℝ) (b:ℝ)}
  have hgen : MeasurableSpace.pi=generateFrom (Set.pi univ '' Set.pi univ (fun _ : ι => C)) :=
    (generateFrom_eq_pi (fun _ => Real.borel_eq_generateFrom_Ioo_rat.symm)
      (fun _ => (Real.finiteSpanningSetsInIooRat volume).isCountablySpanning)).symm
  apply lp_closed_subspace_of_generating_pi P p hp _
    (IsPiSystem.pi (fun _ => Real.isPiSystem_Ioo_rat)) hgen V hV hu
  rintro s ⟨S,hS,rfl⟩ hs
  have hrep : ∀ i,∃ a b : ℚ,a<b ∧ S i=Ioo (a:ℝ) (b:ℝ) := by
    intro i
    have hi := mem_univ_pi.mp hS i
    simpa only [C,mem_iUnion,mem_singleton_iff,exists_prop] using hi
  choose a b hab he using hrep
  have hSval : S=fun i => Ioo (a i:ℝ) (b i:ℝ) := funext he
  subst S
  exact hr _ _ hs

/-- Smoothing each rectangle boundary and using dominated convergence
supplies the finite-dimensional step of cylinder density. Constants and
smooth compactly supported functions suffice. -/
theorem smooth_rectangles_Lp_dense {ι : Type*} [Fintype ι]
    (P : Measure (ι → ℝ)) [IsFiniteMeasure P] (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    (V : Submodule ℝ (Lp ℝ p P)) (hV : IsClosed (V : Set (Lp ℝ p P)))
    (hu : indicatorConstLp p MeasurableSet.univ (measure_ne_top P _) (1:ℝ)∈V)
    (hg : ∀ g : (ι → ℝ) → ℝ,ContDiff ℝ ∞ g → HasCompactSupport g →
      ∀ hi : MemLp g p P,hi.toLp g∈V) :
    ∀ f : Lp ℝ p P,f∈V := by
  apply rectangle_indicators_Lp_dense P p hp V hV hu
  intro a b hs
  have hi : ∀ n,MemLp (smoothRectangleIndicator a b n) p P := fun n =>
    MemLp.of_bound (smooth_rectangle_contDiff a b n).continuous.aestronglyMeasurable 1
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (smooth_rectangle_bounds a b n x).1]
        exact (smooth_rectangle_bounds a b n x).2))
  have hiR := (memLp_const (1:ℝ) (p := p) (μ := P)).indicator hs
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hi _ hiR).mpr
    (smooth_rectangle_Lp_limit P a b p Fact.out hp)
  exact hV.mem_of_tendsto ht (Filter.Eventually.of_forall (fun n =>
    hg _ (smooth_rectangle_contDiff a b n) (smooth_rectangle_compact a b n) (hi n)))

end Asakura.Chapter12

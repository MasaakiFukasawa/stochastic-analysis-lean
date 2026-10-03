import GaussianCopies
import L2Moments

open MeasureTheory ProbabilityTheory
namespace Asakura

def PositiveSupported (f : Lp ℝ 2 (volume : Measure ℝ)) : Prop :=
  ∀ᵐ r ∂volume, r ≤ 0 → f r = 0

lemma positiveSupported_sub {f g : Lp ℝ 2 (volume : Measure ℝ)}
    (hf : PositiveSupported f) (hg : PositiveSupported g) : PositiveSupported (f-g) := by
  filter_upwards [hf,hg,Lp.coeFn_sub f g] with r hfr hgr hsub
  intro hr
  rw [hsub]
  change f r-g r = 0
  rw [hfr hr,hgr hr,sub_self]

/-- Standard deterministic Itô-integral properties for two independent Brownian
motions. This is an explicit interface to the stochastic integration theory in
Chapter 2, not an axiom or a proof of that theory's construction. -/
structure IndependentWienerIntegrals {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) where
  first : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 P
  second : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 P
  inner_sum : ∀ f g f' g',
    PositiveSupported f → PositiveSupported g → PositiveSupported f' → PositiveSupported g' →
    inner ℝ (first f + second g) (first f' + second g') = inner ℝ f f' + inner ℝ g g'
  mean_first : ∀ f, (∫ ω, first f ω ∂P) = 0
  mean_second : ∀ f, (∫ ω, second f ω ∂P) = 0
  gaussian : IsGaussianProcess
    (fun q : Sum (Lp ℝ 2 (volume : Measure ℝ)) (Lp ℝ 2 (volume : Measure ℝ)) =>
      Sum.elim (fun f => (first f : Ω → ℝ)) (fun g => (second g : Ω → ℝ)) q) P

lemma L2_difference_square_integral {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℝ (hf.toLp f-hg.toLp g) (hf.toLp f-hg.toLp g) = ∫ r, (f r-g r)^2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),hf.coeFn_toLp,hg.coeFn_toLp] with r hsub hfr hgr
  change (hf.toLp f-hg.toLp g : Lp ℝ 2 volume) r *
    (hf.toLp f-hg.toLp g : Lp ℝ 2 volume) r = (f r-g r)^2
  rw [hsub]
  simp only [Pi.sub_apply,hfr,hgr,pow_two]
end Asakura

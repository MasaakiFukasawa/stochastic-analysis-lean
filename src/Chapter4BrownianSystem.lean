import Chapter4BrownianGridLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete

/-- A packaged actual Brownian driver: each coordinate is a constructed
continuous local martingale with the full identity covariance matrix. -/
structure BrownianSystem {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (noise : ℕ) where
  F : HalfClosedTime → MeasurableSpace Ω
  mono : Monotone F
  le : ∀ t,F t≤m
  null : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E
  W : Fin noise → HalfClosedTime → Ω → ℝ
  C : Fin noise → Fin noise → HalfClosedTime → Ω → ℝ
  martingale : ∀ j,LocalMProcessWitness P F (W j)
  cov : ∀ j k,LocalCovarianceWitness P F (W j) (W k) (C j k)
  clock : ∀ j k w (r : ℝ),0≤r → C j k (realTimeClamp r) w=if j=k then r else 0

namespace BrownianSystem
variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {noise : ℕ}

noncomputable def shift (B : BrownianSystem P noise) (s : ℝ) (hs : 0≤s) : BrownianSystem P noise where
  F := fun t => B.F (deterministicTimeShift s hs t)
  mono := B.mono.comp (deterministic_shift_mono s hs)
  le := fun t => B.le _
  null := fun t E hm hz => B.null _ E hm hz
  W := fun j t w => B.W j (deterministicTimeShift s hs t) w-B.W j (deterministicTimeShift s hs ⊥) w
  C := fun j k t w => B.C j k (deterministicTimeShift s hs t) w-B.C j k (deterministicTimeShift s hs ⊥) w
  martingale := fun j => local_martingale_shifted_future P B.F B.mono B.le (B.W j) (B.martingale j) s hs
  cov := fun j k => covariance_shifted_future P B.F B.mono B.le B.null _ _ _ (B.martingale j) (B.martingale k) (B.cov j k) s hs
  clock := by
    intro j k w r hr
    rw [deterministic_shift_real s hs r hr,deterministic_shift_bot s hs,
      B.clock j k w (s+r) (add_nonneg hs hr),B.clock j k w s hs]
    split_ifs <;> ring

lemma diagonal_clock (B : BrownianSystem P noise) (j : Fin noise) (w : Ω) (r : ℝ) (hr : 0≤r) :
    B.C j j (realTimeClamp r) w=r := by simpa using B.clock j j w r hr

lemma grid_law (B : BrownianSystem P noise) (h : ℝ) (hh : 0≤h) (n : ℕ) :
    let Z := finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h n
    Measurable[m] Z ∧ charFunDual (@Measure.map Ω _ m _ Z P)=gridNoiseCharacteristic n noise h ∧
      Indep (MeasurableSpace.comap Z inferInstance) (B.F ⊥) P :=
  brownian_finite_grid_law P B.F B.mono B.le B.null B.W B.C B.martingale B.cov B.clock h hh n

end BrownianSystem
end Asakura.Chapter4

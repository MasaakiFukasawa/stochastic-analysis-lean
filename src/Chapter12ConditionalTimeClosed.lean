import Chapter12RandomSections

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem conditional_L2_coe_iff {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : MeasurableSpace Ω) (hle : F ≤ m)
    (U Q : Lp ℝ 2 P) (u q : Ω → ℝ) (hu : (U : Ω → ℝ) =ᵐ[P] u)
    (hq : (Q : Ω → ℝ) =ᵐ[P] q) :
    Q = (condExpL2 ℝ ℝ hle U : Lp ℝ 2 P) ↔ q =ᵐ[P] P[u|F] := by
  have he := (Lp.memLp U).condExpL2_ae_eq_condExp (𝕜 := ℝ) hle
  have hto : (Lp.memLp U).toLp (U : Ω → ℝ)=U := Lp.ext (Lp.memLp U).coeFn_toLp
  rw [hto] at he
  have hh := he.trans (condExp_congr_ae (m := F) hu)
  constructor
  · intro h
    rw [h] at hq
    exact hq.symm.trans hh
  · intro h
    apply Lp.ext
    exact (hq.trans h).trans hh.symm

/-- Timewise conditional expectation is closed under joint L2 convergence.
This completes the limit step after constructing the cylindrical approximants. -/
theorem conditional_time_identity_closed {Ω S : Type*} [m : MeasurableSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure S) [SigmaFinite ν] (F : S → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (u q : ℕ → Lp ℝ 2 (P.prod ν)) (U Q : Lp ℝ 2 (P.prod ν))
    (hu : Tendsto u atTop (𝓝 U)) (hq : Tendsto q atTop (𝓝 Q))
    (he : ∀ n,∀ᵐ t ∂ν,(fun w => q n (w,t)) =ᵐ[P] P[(fun w => u n (w,t))|F t]) :
    ∀ᵐ t ∂ν,(fun w => Q (w,t)) =ᵐ[P] P[(fun w => U (w,t))|F t] := by
  let J := randomSectionsIsometry P ν
  let A : S → Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P := fun t =>
    (lpMeas ℝ ℝ (F t) 2 P).subtypeL.comp (condExpL2 ℝ ℝ (hle t))
  have hn : ∀ n,∀ᵐ t ∂ν,J (q n) t=A t (J (u n) t) := by
    intro n
    filter_upwards [randomSectionsIsometry_coe P ν (u n),randomSectionsIsometry_coe P ν (q n),he n]
      with t hut hqt het
    exact (conditional_L2_coe_iff P (F t) (hle t) _ _ _ _ hut hqt).mpr het
  have hlim := fiberwise_linear_identity_limit ν A (fun n => J (u n)) (fun n => J (q n))
    (J U) (J Q) (J.continuous.continuousAt.tendsto.comp hu)
    (J.continuous.continuousAt.tendsto.comp hq) hn
  filter_upwards [randomSectionsIsometry_coe P ν U,randomSectionsIsometry_coe P ν Q,hlim]
    with t hut hqt het
  exact (conditional_L2_coe_iff P (F t) (hle t) _ _ _ _ hut hqt).mp het

end Asakura.Chapter12

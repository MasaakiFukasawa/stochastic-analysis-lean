import FullAuditContinuousGridMax

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written

/-- Apply the finite theorem to precisely the cumulative grid maximum. -/
theorem cumulative_grid_strong {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} (hT : 0 ≤ T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : ∀ t, Measurable[F t] (X t))
    (hY : Integrable (X ⟨T,hT,le_rfl⟩) P) (hpos : ∀ t, 0 ≤ᵐ[P] X t)
    (hdom : ∀ t, X t ≤ᵐ[P] P[X ⟨T,hT,le_rfl⟩ | F t])
    (n : ℕ) (p : ℝ) (hp : 1 < p) :
    (∫⁻ ω, ENNReal.ofReal (cumulativeMax hT X n ω) ^ p ∂P) ^ (1/p) ≤
      ENNReal.ofReal (p/(p-1)) * (∫⁻ ω, ENNReal.ofReal (X ⟨T,hT,le_rfl⟩ ω) ^ p ∂P) ^ (1/p) := by
  classical
  let D := cumulativeGrid hT n
  letI : Fintype D := (cumulative_grid_finite hT n).fintype
  letI : OrderTop D := { top := ⟨⟨T,hT,le_rfl⟩,Or.inl rfl⟩, le_top := fun t => t.val.property.2 }
  have he (ω : Ω) : Finset.univ.sup' Finset.univ_nonempty (fun t : D => X t.val ω) =
      cumulativeMax hT X n ω := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro t ht
      exact (cumulative_max_level hT X n ω _).mpr ⟨t.val,t.property,le_rfl⟩
    · obtain ⟨t,ht,he⟩ := (cumulative_max_level hT X n ω (cumulativeMax hT X n ω)).mp le_rfl
      exact (Finset.le_sup'_iff Finset.univ_nonempty).mpr ⟨⟨t,ht⟩,Finset.mem_univ _,he⟩
  have h := doob_process_strong_written P (fun t : D => F t) (fun _ _ h => hF h) (fun t => hle t)
    (fun t : D => X t) (fun t => hX t) hY (fun t => hpos t) (fun t => hdom t) p hp
  change (∫⁻ ω, ENNReal.ofReal (Finset.univ.sup' Finset.univ_nonempty (fun t : D => X t.val ω)) ^ p ∂P) ^ (1/p) ≤
    ENNReal.ofReal (p/(p-1)) * (∫⁻ ω, ENNReal.ofReal (X ⟨T,hT,le_rfl⟩ ω) ^ p ∂P) ^ (1/p) at h
  simpa only [he] using h

/-- The whole continuous-time Lp bound follows by monotone convergence of
 the grid maxima; the supremum may take the value infinity. -/
theorem continuous_doob_strong_written {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} (hT : 0 ≤ T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : ∀ t, Measurable[F t] (X t))
    (hr : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (hY : Integrable (X ⟨T,hT,le_rfl⟩) P) (hpos : ∀ t, 0 ≤ᵐ[P] X t)
    (hdom : ∀ t, X t ≤ᵐ[P] P[X ⟨T,hT,le_rfl⟩ | F t]) (p : ℝ) (hp : 1 < p) :
    (∫⁻ ω, (⨆ t, ENNReal.ofReal (X t ω)) ^ p ∂P) ^ (1/p) ≤
      ENNReal.ofReal (p/(p-1)) * (∫⁻ ω, ENNReal.ofReal (X ⟨T,hT,le_rfl⟩ ω) ^ p ∂P) ^ (1/p) := by
  have hm (n : ℕ) : Measurable[m] (fun ω => ENNReal.ofReal (cumulativeMax hT X n ω)^p) :=
    (cumulative_max_measurable hT X (fun t => (hX t).mono (hle t) le_rfl) n).ennreal_ofReal.pow_const p
  have hmono (ω : Ω) : Monotone (fun n => ENNReal.ofReal (cumulativeMax hT X n ω)^p) :=
    fun n k hnk => ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (cumulative_max_mono hT X ω hnk)) (by linarith)
  have ht (ω : Ω) : Tendsto (fun n => ENNReal.ofReal (cumulativeMax hT X n ω)^p) atTop
      (𝓝 ((⨆ t, ENNReal.ofReal (X t ω))^p)) := by
    have h := tendsto_atTop_iSup (fun n k hnk =>
      ENNReal.ofReal_le_ofReal (cumulative_max_mono hT X ω hnk))
    rw [cumulative_max_supremum hT X hr ω] at h
    exact ENNReal.continuous_rpow_const.continuousAt.tendsto.comp h
  have hi := lintegral_tendsto_of_tendsto_of_monotone (μ := P) (fun n => (hm n).aemeasurable)
    (Eventually.of_forall hmono) (Eventually.of_forall ht)
  have hroot := (ENNReal.continuous_rpow_const (y := 1/p)).continuousAt.tendsto.comp hi
  exact le_of_tendsto hroot (Eventually.of_forall fun n => cumulative_grid_strong P hT F hF hle X hX hY hpos hdom n p hp)

end Asakura.FullAudit

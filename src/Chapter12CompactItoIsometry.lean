import Chapter12CompactItoTerminal

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

/-- The finite-horizon Ito operator is the existing Brownian Ito isometry,
composed with the proved zero extension, and taking values in F_T. -/
noncomputable def compactItoIsometry {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (c : ℕ → ℝ)
    (I : progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hI : ∀ H : progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : HalfClosedTime → Ω → ℝ,∃ hN : ContinuousM2Witness P B.F N,
        ItoCovarianceFormula P B.F (B.W i) H.val N ∧
        I ⟨progressiveEnergyToLp B.F c _ H,LinearMap.mem_range_self _ H⟩ = (hN.moment ⊤).toLp (N ⊤))
    (T : ℝ) (hT : 0≤T) [Fact (0≤T)] :
    let Fc := fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val)
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace Fc
    Lp ℝ 2 ((P.prod (compactTimeMeasure T hT)).trim
      (progressive_space_le_product Fc (fun _ => B.le _))) →ₗᵢ[ℝ]
      Lp ℝ 2 (P.trim (B.le (realTimeClamp T))) := by
  dsimp only
  let A := I.comp (compactEnergyIsometry P T hT B.F B.mono B.le c)
  have hm U : A U∈lpMeas ℝ ℝ (B.F (realTimeClamp T)) 2 P :=
    mem_lpMeas_iff_aestronglyMeasurable.mpr (compact_ito_terminal_measurable P B i c I hI T hT U)
  let J : _ →ₗᵢ[ℝ] lpMeas ℝ ℝ (B.F (realTimeClamp T)) 2 P :=
    { toLinearMap := A.toLinearMap.codRestrict _ hm
      norm_map' := A.norm_map }
  exact (lpMeasToLpTrimLie ℝ ℝ 2 P (B.le (realTimeClamp T))).toLinearIsometry.comp J

theorem compactItoIsometry_coe {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (i : Fin d) (c : ℕ → ℝ)
    (I : progressiveEnergyRange B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hI : ∀ H : progressiveEnergyIntegrands B.F c (P.prod (volume.restrict (Ioi (0:ℝ)))),
      ∃ N : HalfClosedTime → Ω → ℝ,∃ hN : ContinuousM2Witness P B.F N,
        ItoCovarianceFormula P B.F (B.W i) H.val N ∧
        I ⟨progressiveEnergyToLp B.F c _ H,LinearMap.mem_range_self _ H⟩ = (hN.moment ⊤).toLp (N ⊤))
    (T : ℝ) (hT : 0≤T) [Fact (0≤T)] :
    let Fc := fun t : Icc (0:ℝ) T => B.F (realTimeClamp t.val)
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace Fc
    ∀ U : Lp ℝ 2 ((P.prod (compactTimeMeasure T hT)).trim
      (progressive_space_le_product Fc (fun _ => B.le _))),
    (compactItoIsometry P B i c I hI T hT U : Ω → ℝ)=ᵐ[P]
      (I (compactEnergyIsometry P T hT B.F B.mono B.le c U) : Ω → ℝ) := by
  dsimp only
  intro U
  exact lpMeasToLpTrim_ae_eq (B.le (realTimeClamp T)) _

end Asakura.Chapter12

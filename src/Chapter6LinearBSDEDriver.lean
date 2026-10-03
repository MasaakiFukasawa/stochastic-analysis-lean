import Chapter5NonlinearBSDEDriverData

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 1800000

noncomputable def linearBSDEDriver {Ω : Type*} (φ α β : Ω × ℝ → ℝ)
    (z : (Ω × ℝ) × (ℝ × ℝ)) : ℝ := φ z.1+α z.1*z.2.1+β z.1*z.2.2

lemma linear_bsde_lipschitz {Ω : Type*} (φ α β : Ω × ℝ → ℝ) (K : ℝ)
    (hα : ∀ z,|α z|≤K) (hβ : ∀ z,|β z|≤K) (z : Ω × ℝ) (y₁ z₁ y₂ z₂ : ℝ) :
    |linearBSDEDriver φ α β (z,y₁,z₁)-linearBSDEDriver φ α β (z,y₂,z₂)|≤
      K*(|y₁-y₂|+|z₁-z₂|) := by
  have he : linearBSDEDriver φ α β (z,y₁,z₁)-linearBSDEDriver φ α β (z,y₂,z₂)=
      α z*(y₁-y₂)+β z*(z₁-z₂) := by dsimp [linearBSDEDriver]; ring
  rw [he]
  calc
    _ ≤ |α z*(y₁-y₂)|+|β z*(z₁-z₂)| := abs_add_le _ _
    _ ≤ K*|y₁-y₂|+K*|z₁-z₂| := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right (hα z) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (hβ z) (abs_nonneg _))
    _ = _ := by ring

lemma linear_bsde_driver_measurable {Ω : Type*} [MeasurableSpace Ω]
    (φ α β : Ω × ℝ → ℝ) (hφ : Measurable φ) (hα : Measurable α) (hβ : Measurable β) :
    Measurable (linearBSDEDriver φ α β) :=
  ((hφ.comp measurable_fst).add ((hα.comp measurable_fst).mul measurable_snd.fst)).add
    ((hβ.comp measurable_fst).mul measurable_snd.snd)

lemma linear_bsde_driver_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (φ α β : Ω × ℝ → ℝ)
    (hφ : Measurable φ) (K R : ℝ) (hb : ∀ z,|φ z|≤K) :
    MemLp (fun z => linearBSDEDriver φ α β (z,0,0)) 2 (P.prod (volume.restrict (Ioc 0 R))) := by
  simp only [linearBSDEDriver,mul_zero,add_zero]
  exact MemLp.of_bound hφ.aestronglyMeasurable K (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb z))

end Asakura.Chapter6

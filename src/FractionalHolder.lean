import FractionalMoments
import PowerMomentHolder
import BrownianCube

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace Asakura
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma fractional_cube_holder (X : UnitCube 1 → Ω → ℝ)
    (hX : ∀ t, Measurable (X t)) (hcont : ∀ ω, Continuous (fun t => X t ω))
    (hG : IsGaussianProcess X P) (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (hm : ∀ t, (∫ ω, X t ω ∂P) = 0)
    (hc : ∀ s t, (∫ ω, X s ω * X t ω ∂P) =
      ((a*s.val 0)^(2*H)+(a*t.val 0)^(2*H)-|a*s.val 0-a*t.val 0|^(2*H))/2) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, 0 ≤ α → α < H →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s t,
        dist (X s ω) (X t ω) ≤ C * (dist s t)^α := by
  apply power_moment_holder P X hX hcont H
  intro p hp
  let C := eLpNorm id p (gaussianReal 0 1)
  have hC : C ≠ ∞ := (memLp_id_gaussianReal p).eLpNorm_ne_top
  refine ⟨C.toReal*a^H,by positivity,?_⟩
  intro s t
  rw [fractional_increment_norm X hG (fun s => a*s.val 0) H hH hm hc p s t]
  rw [← mul_sub, abs_mul, abs_of_nonneg ha, ← unitCube_one_distance,
    Real.mul_rpow ha dist_nonneg]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC]
  exact le_of_eq (by ring)

noncomputable def scaledTime (N : ℕ) (s : UnitCube 1) : ℝ≥0 :=
  ⟨((N:ℝ)+1)*s.val 0, mul_nonneg (by positivity) (s.property 0).1⟩

noncomputable def inverseScaledTime (N : ℕ) (s : ℝ≥0) (hs : s ≤ N) : UnitCube 1 :=
  ⟨fun _ => (s:ℝ)/((N:ℝ)+1), fun _ => ⟨by positivity,
    (div_le_one (by positivity)).mpr (by exact_mod_cast (show s ≤ (N:ℝ≥0)+1 by
      exact hs.trans (le_add_of_nonneg_right zero_le_one)))⟩⟩

lemma scaledTime_inverse (N : ℕ) (s : ℝ≥0) (hs : s ≤ N) :
    scaledTime N (inverseScaledTime N s hs) = s := by
  apply NNReal.coe_injective
  change ((N:ℝ)+1)*((s:ℝ)/((N:ℝ)+1)) = s
  field_simp

lemma inverseScaledTime_distance (N : ℕ) (s t : ℝ≥0) (hs : s ≤ N) (ht : t ≤ N) :
    dist (inverseScaledTime N s hs) (inverseScaledTime N t ht) ≤ dist s t := by
  rw [unitCube_one_distance]
  change |(s:ℝ)/((N:ℝ)+1)-(t:ℝ)/((N:ℝ)+1)| ≤ dist (s:ℝ) (t:ℝ)
  rw [← sub_div, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ)+1), Real.dist_eq]
  exact div_le_self (abs_nonneg _) (by linarith [Nat.cast_nonneg (α := ℝ) N])

/-- The local Holder assertion for fractional Brownian motion, from its defining
Gaussian covariance and continuous paths, on a common full event for all exponents. -/
theorem fractional_brownian_local_holder (X : ℝ≥0 → Ω → ℝ)
    (hX : ∀ t, Measurable (X t)) (hcont : ∀ ω, Continuous (fun t => X t ω))
    (hG : IsGaussianProcess X P) (H : ℝ) (hH : 0 < H)
    (hm : ∀ t, (∫ ω, X t ω ∂P) = 0)
    (hc : ∀ s t, (∫ ω, X s ω * X t ω ∂P) =
      ((s:ℝ)^(2*H)+(t:ℝ)^(2*H)-|(s:ℝ)-(t:ℝ)|^(2*H))/2) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, 0 ≤ α → α < H → ∀ N : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ≥0, s ≤ N → t ≤ N →
        dist (X s ω) (X t ω) ≤ C * (dist s t)^α := by
  have hN (N : ℕ) : ∀ᵐ ω ∂P, ∀ α : ℝ, 0 ≤ α → α < H →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : UnitCube 1,
        dist (X (scaledTime N s) ω) (X (scaledTime N t) ω) ≤ C * (dist s t)^α := by
    apply fractional_cube_holder (fun s => X (scaledTime N s)) (fun s => hX _) _
      (hG.comp_right (scaledTime N)) ((N:ℝ)+1) H (by positivity) hH
      (fun s => hm _) (fun s t => hc _ _)
    intro ω
    apply (hcont ω).comp
    exact (continuous_const.mul ((continuous_apply 0).comp continuous_subtype_val)).subtype_mk _
  filter_upwards [ae_all_iff.mpr hN] with ω hω
  intro α hα hαH N
  obtain ⟨C,hC,hbound⟩ := hω N α hα hαH
  refine ⟨C,hC,?_⟩
  intro s t hs ht
  have hh := hbound (inverseScaledTime N s hs) (inverseScaledTime N t ht)
  rw [scaledTime_inverse,scaledTime_inverse] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow dist_nonneg (inverseScaledTime_distance N s t hs ht) hα) hC)
end Asakura

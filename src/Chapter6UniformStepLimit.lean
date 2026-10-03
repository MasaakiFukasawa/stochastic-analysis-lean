import Chapter4EulerCellCover
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def uniformLeftStep (R : ℝ) (n : ℕ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∑ k∈range (n+1),(Ioc ((k:ℝ)*(R/(n+1))) (((k:ℝ)+1)*(R/(n+1)))).indicator
    (fun _ => f ((k:ℝ)*(R/(n+1)))) r

lemma uniform_left_step_pointwise (R : ℝ) (hR : 0<R) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 R)) (r : ℝ) (hr : r∈Ioc 0 R) :
    Tendsto (fun n => uniformLeftStep R n f r) atTop (𝓝 (f r)) := by
  let h := fun n : ℕ => R/((n:ℝ)+1)
  have hh n : 0<h n := div_pos hR (by positivity)
  have hend n : ((n+1:ℕ):ℝ)*h n=R := by dsimp [h]; push_cast; field_simp
  have hc n : ∃ k∈range (n+1),r∈Ioc ((k:ℝ)*h n) (((k:ℝ)+1)*h n) :=
    uniform_grid_interval_cover (h n) (hh n).le (n+1) r (by rwa [hend])
  choose k hk hkr using hc
  let x := fun n => (k n:ℝ)*h n
  have hx n : x n∈Icc 0 R := ⟨mul_nonneg (Nat.cast_nonneg _) (hh n).le,(hkr n).1.le.trans hr.2⟩
  have hlim : Tendsto h atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hxl : Tendsto x atTop (𝓝 r) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (show Tendsto (fun n => r-h n) atTop (𝓝 r) by simpa using tendsto_const_nhds.sub hlim) tendsto_const_nhds
    · intro n
      have hh := (hkr n).2
      dsimp [x]
      nlinarith
    · exact fun n => (hkr n).1.le
  have hfx := (hf r ⟨hr.1.le,hr.2⟩).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hxl,Eventually.of_forall hx⟩)
  apply hfx.congr'
  exact Eventually.of_forall (fun n => by
    simpa [uniformLeftStep,h,x,Nat.cast_add,Nat.cast_one] using
      (uniform_grid_step_on_cell (h n) (hh n).le (n+1) (k n) (mem_range.mp (hk n)) (fun j => f ((j:ℝ)*h n)) r (hkr n)).symm)

lemma uniform_left_step_abs_le (R : ℝ) (hR : 0<R) (n : ℕ) (f : ℝ → ℝ)
    (K : ℝ) (hb : ∀ r∈Icc 0 R,|f r|≤K) (r : ℝ) (hr : r∈Ioc 0 R) :
    |uniformLeftStep R n f r|≤K := by
  let h := R/((n:ℝ)+1)
  have hh : 0<h := div_pos hR (by positivity)
  have hend : ((n+1:ℕ):ℝ)*h=R := by dsimp [h]; push_cast; field_simp
  obtain ⟨k,hk,hkr⟩ := uniform_grid_interval_cover h hh.le (n+1) r (by rwa [hend])
  have he := uniform_grid_step_on_cell h hh.le (n+1) k (mem_range.mp hk) (fun j => f ((j:ℝ)*h)) r hkr
  have he' : uniformLeftStep R n f r=f ((k:ℝ)*h) := by simpa [uniformLeftStep,h] using he
  rw [he']
  exact hb _ ⟨mul_nonneg (Nat.cast_nonneg _) hh.le,hkr.1.le.trans hr.2⟩

end Asakura.Chapter6

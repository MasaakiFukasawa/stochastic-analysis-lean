import Chapter4PositiveTimeExtension
import Mathlib.Topology.Compactness.SigmaCompact

open Set Filter Function
open scoped Topology
namespace Asakura.Chapter4
set_option maxHeartbeats 2800000

/-- Compactly supported smooth cutoffs exhaust any open subset of a
finite-dimensional space. Outside the open set they vanish, and at each
point inside it they are eventually exactly one. -/
theorem smooth_open_cutoffs {dim : ℕ} (O : Set (Fin dim → ℝ)) (hO : IsOpen O) :
    ∃ χ : ℕ → (Fin dim → ℝ) → ℝ,
      (∀ n,ContDiff ℝ (⊤:ℕ∞) (χ n)) ∧ (∀ n,HasCompactSupport (χ n)) ∧
      (∀ n x,χ n x∈Icc 0 1) ∧ (∀ n x,x∉O → χ n x=0) ∧
      ∀ x∈O,∀ᶠ n in atTop,χ n x=1 := by
  classical
  letI : LocallyCompactSpace O := hO.locallyCompactSpace
  let K : CompactExhaustion O := default
  have hcut n : ∃ f : (Fin dim → ℝ) → ℝ,ContDiff ℝ (⊤:ℕ∞) f ∧ HasCompactSupport f ∧
      (∀ x,f x∈Icc 0 1) ∧ (∀ x,x∉O → f x=0) ∧ ∀ x∈K n,f x.val=1 := by
    let L : Set (Fin dim → ℝ) := Subtype.val '' K n
    have hL : IsCompact L := (K.isCompact n).image continuous_subtype_val
    have hLO : L⊆O := by rintro x ⟨y,_,rfl⟩;exact y.property
    obtain ⟨V,hVo,hLV,hVO,hVc⟩ := exists_open_between_and_isCompact_closure hL hO hLO
    obtain ⟨f,hf,hfb,hfs,hf1⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤:ℕ∞)) hVo hL.isClosed hLV
    refine ⟨f,hf,?_,fun x => hfb (mem_range_self x),?_,?_⟩
    · change IsCompact (closure (support f))
      rwa [hfs]
    · intro x hx
      apply notMem_support.mp
      rw [hfs]
      exact fun h => hx (hVO (subset_closure h))
    · intro x hx
      exact (hf1 x.val).mp ⟨x,hx,rfl⟩
  choose χ hχ hχc hχb hχ0 hχ1 using hcut
  refine ⟨χ,hχ,hχc,hχb,hχ0,?_⟩
  intro x hx
  obtain ⟨n,hn⟩ := K.exists_mem ⟨x,hx⟩
  filter_upwards [eventually_ge_atTop n] with k hk
  exact hχ1 k ⟨x,hx⟩ (K.subset hk hn)

/-- The manuscript's successive-union construction makes the smooth
cutoffs monotone while retaining compact support and the [0,1] bounds. -/
theorem smooth_monotone_open_approximation {dim : ℕ} (O : Set (Fin dim → ℝ)) (hO : IsOpen O) :
    ∃ f : ℕ → (Fin dim → ℝ) → ℝ,
      (∀ n,ContDiff ℝ (⊤:ℕ∞) (f n)) ∧ (∀ n,HasCompactSupport (f n)) ∧
      (∀ n x,f n x∈Icc 0 1) ∧ (∀ x,Monotone (fun n => f n x)) ∧
      ∀ x,Tendsto (fun n => f n x) atTop (𝓝 (O.indicator (fun _ => (1:ℝ)) x)) := by
  classical
  obtain ⟨χ,hχ,hχc,hχb,hχ0,hχlim⟩ := smooth_open_cutoffs O hO
  let f : ℕ → (Fin dim → ℝ) → ℝ := fun n => Nat.rec (fun _ => 0)
    (fun n g x => g x+(1-g x)*χ n x) n
  have hz x : f 0 x=0 := rfl
  have hs n x : f (n+1) x=f n x+(1-f n x)*χ n x := rfl
  have hfb n x : f n x∈Icc 0 1 := by
    induction n with
    | zero => simp only [hz,mem_Icc];norm_num
    | succ n ih =>
      rw [hs]
      have hb := hχb n x
      constructor
      · exact add_nonneg ih.1 (mul_nonneg (sub_nonneg.mpr ih.2) hb.1)
      · nlinarith [mul_nonneg (sub_nonneg.mpr ih.2) (sub_nonneg.mpr hb.2)]
  have hfc n : ContDiff ℝ (⊤:ℕ∞) (f n) := by
    induction n with
    | zero => exact contDiff_const
    | succ n ih => exact ih.add ((contDiff_const.sub ih).mul (hχ n))
  have hfcomp n : HasCompactSupport (f n) := by
    induction n with
    | zero => change IsCompact (tsupport (fun _ : Fin dim → ℝ => (0:ℝ)));simp
    | succ n ih => exact ih.add ((hχc n).mul_left (f := fun x => 1-f n x))
  have hmono x : Monotone (fun n => f n x) := monotone_nat_of_le_succ fun n => by
    rw [hs]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr (hfb n x).2) (hχb n x).1)
  refine ⟨f,hfc,hfcomp,hfb,hmono,?_⟩
  intro x
  by_cases hx : x∈O
  · rw [indicator_of_mem hx]
    apply tendsto_const_nhds.congr'
    obtain ⟨n,hn⟩ := eventually_atTop.mp (hχlim x hx)
    filter_upwards [eventually_ge_atTop (n+1)] with k hk
    obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [show n+1+l=(n+l)+1 by omega,hs,hn (n+l) (by omega)]
    ring
  · rw [indicator_of_notMem hx]
    have he n : f n x=0 := by
      induction n with
      | zero => rfl
      | succ n ih => rw [hs,ih,hχ0 n x hx];ring
    simpa only [he] using (tendsto_const_nhds (x := (0:ℝ)))

end Asakura.Chapter4

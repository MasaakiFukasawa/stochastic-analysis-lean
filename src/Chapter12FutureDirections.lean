import Chapter12WienerFiniteFamilies
import Chapter12FinitePastFuture

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

noncomputable def finiteFuturePart {d : ℕ} (T a : ℝ) (u : FiniteWienerHilbert d T) :
    FiniteWienerHilbert d T :=
  WithLp.toLp 2 (fun i => ((Lp.memLp (u i)).indicator (s := Ioi a) measurableSet_Ioi).toLp
    ((Ioi a).indicator (u i)))

theorem finite_future_part_vanishes {d : ℕ} (T a : ℝ) (u : FiniteWienerHilbert d T)
    (i : Fin (d+1)) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))).restrict (Iic T),t≤a → finiteFuturePart T a u i t=0 := by
  have hh := ((Lp.memLp (u i)).indicator (s := Ioi a) measurableSet_Ioi).coeFn_toLp
  filter_upwards [hh] with t ht
  intro hta
  change ((Lp.memLp (u i)).indicator (s := Ioi a) measurableSet_Ioi).toLp _ t=0
  rw [ht]
  exact indicator_of_notMem (not_lt.mpr hta) _

theorem finite_future_part_past_orthogonal {d : ℕ} (T a : ℝ)
    (u : FiniteWienerHilbert d T) (z : BrownianTimeCoordinates d T) (hza : z.2.val≤a) :
    inner ℝ (finiteFuturePart T a u) (brownianTimeDirection z)=0 := by
  rw [real_inner_comm,PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hiz : i=z.1
  · subst i
    simp only [brownianTimeDirection, PiLp.toLp_apply, Pi.single_eq_same]
    change inner ℝ (finiteTimeIntervalVector T 0 z.2.val) (finiteFuturePart T a u z.1)=0
    apply past_future_time_orthogonal _ a
    · have hh : (finiteTimeIntervalVector T 0 z.2.val : ℝ → ℝ) =ᵐ[(volume.restrict (Ioi (0:ℝ))).restrict (Iic T)]
          (Ioc 0 z.2.val).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
      filter_upwards [hh] with t ht
      intro hat
      rw [ht]
      exact indicator_of_notMem (fun hs => (not_lt_of_ge (hs.2.trans hza)) hat) _
    · exact finite_future_part_vanishes T a u z.1
  · change inner ℝ ((Pi.single (M := fun _ : Fin (d+1) => Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)))
      z.1 (finiteTimeIntervalVector T 0 z.2.val)) i) (finiteFuturePart T a u i)=0
    simp [Pi.single_eq_of_ne hiz]

end Asakura.Chapter12

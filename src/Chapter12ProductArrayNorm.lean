import Chapter12BanachArrayNorm

namespace Asakura.Chapter12
set_option maxHeartbeats 1600000

theorem product_array_norm_le {I E F:Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (a:I → E) (b:I → F) :
    Real.sqrt (∑i,‖(a i,b i)‖^2)≤Real.sqrt (∑i,‖a i‖^2)+Real.sqrt (∑i,‖b i‖^2) := by
  let u : PiLp 2 (fun _:I => E×F) := WithLp.toLp 2 (fun i => (a i,0))
  let v : PiLp 2 (fun _:I => E×F) := WithLp.toLp 2 (fun i => (0,b i))
  have he : WithLp.toLp 2 (fun i => (a i,b i))=u+v := by ext i <;> simp [u,v]
  rw [←banach_array_norm,he]
  simpa only [u,v,banach_array_norm,Prod.norm_mk,max_eq_left (norm_nonneg _),
    max_eq_right (norm_nonneg _),norm_zero] using norm_add_le u v
end Asakura.Chapter12
#print axioms Asakura.Chapter12.product_array_norm_le

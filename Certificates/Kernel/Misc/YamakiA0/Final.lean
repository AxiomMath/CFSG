module

public import CFSG.Certificates.Kernel.Misc.YamakiA0Sound
public import Certificates.Kernel.Misc.YamakiA0.Checks
public import Certificates.Kernel.Misc.YamakiS0.Final

public section

namespace CFSG.KD.YamakiA0

open CFSG.KC.YamakiA0 CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec
  CFSG.KC.Misc.Spec

theorem ya0_hdr : ∀ j < 9, REC j = CFSG.KD.YamakiS0.REC j := by decide +kernel

theorem ya0_gens_hi : ∀ j : Fin 3, yamakiMat6 ⟨j.val + 9, by omega⟩ = pkMat 6 (REC (j.val + 9)) := by
  decide +kernel

theorem ya0_gens : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (REC j.val) := by
  intro j
  by_cases hj : j.val < 9
  · rw [ya0_hdr j.val hj]
    exact CFSG.KD.YamakiS0.ys0_gens ⟨j.val, hj⟩
  · have := ya0_gens_hi ⟨j.val - 9, by omega⟩
    simp only [Nat.sub_add_cancel (by omega : 9 ≤ j.val)] at this
    exact this

theorem cert550821_ok :
    (a0EnumCheck () = true) ∧ (a0AbelCheck () = true) ∧ (hhatAlphaCheck () = true) ∧
      (fourCheck () = true) :=
  cert550821_of ya0_gens ya0_tab_ok ya0_gen_ok ya0_hhat_ok ya0_four_ok
    CFSG.KD.YamakiS0.ys0_gens CFSG.KD.YamakiS0.ys0_tab_ok

end CFSG.KD.YamakiA0

end

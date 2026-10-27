module

public import CFSG.Certificates.Kernel.Misc.YamakiS0Sound
public import Certificates.Kernel.Misc.YamakiS0.Checks

public section

namespace CFSG.KD.YamakiS0

open CFSG.KC.YamakiS0 CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KC.Misc.Spec

theorem ys0_gens : ∀ j : Fin 9, yamakiMat6 ⟨j.val, by omega⟩ = pkMat 6 (REC j.val) := by
  decide +kernel

theorem ys0_gens_lt : ∀ j < 9, REC j < 2 ^ 36 := by decide +kernel

theorem cert550801_ok :
    (enumOK (enumS0 ()) (gS0 ()) = true)
    ∧ (sqCount (enumS0 ()) (idA ()) = 144)
    ∧ (sqCount (enumS0 ()) (genA ())[5]! = 0)
    ∧ (sqCount (enumS0 ()) (genA ())[4]! = 48)
    ∧ (sqCount (enumS0 ()) (compA (genA ())[5]! (genA ())[4]!) = 32)
    ∧ (commOK (gS0 ()) (genA ())[5]! = true)
    ∧ (commOK (gS0 ()) (genA ())[4]! = true)
    ∧ (centerOK (enumS0 ()) (gS0 ()) (genA ())[5]! (genA ())[4]! = true) :=
  cert550801_of ys0_gens ys0_gens_lt ys0_tab_ok ys0_sq1_ok ys0_sqa_ok ys0_sqb_ok ys0_sqc_ok
    ys0_comma_ok ys0_commb_ok ys0_cent_ok

end CFSG.KD.YamakiS0

end

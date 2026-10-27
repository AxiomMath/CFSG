module

public import Certificates.Kernel.Misc.T46

public section

namespace CFSG.KD.Misc.T46

open CFSG.KC.Misc.T46 CFSG.F4.Native

theorem t46Simple : t46SimpleCertificate () = true := by
  rw [t46_eq]
  exact t46_sound CFSG.KD.Misc.Unitary.hU bWS bTW (BL := [0, 1, 3, 9, 45]) rfl pts genAll letters
    trees xy tvAll

end CFSG.KD.Misc.T46

end

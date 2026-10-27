module

public import Certificates.Kernel.Misc.Xi
public import Certificates.Kernel.Misc.TvTabs
public import CFSG.Certificates.Kernel.Misc.XiSound
public import Certificates.Kernel.Misc.Lines
public import Certificates.Kernel.Misc.T46

public section

namespace CFSG.KD.Misc.Xi

open CFSG.KC.Misc.T46 CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KD.Misc.T46 CFSG.KD.Misc.Lines
  CFSG.Fischer.Native CFSG.KC.Misc.O73

theorem paAcycAll : ∀ k < 1408, 0 < k → at' 12 PA k / 2 < k := by
  decide +kernel

theorem paAcyc : ∀ k, 0 < k → k < 1408 → at' 12 PA k / 2 < k :=
  fun k h0 hk => paAcycAll k hk h0

theorem xi_true : xiCertificate () = true := by
  rw [xi_eq]
  exact xi_sound_acyc CFSG.KD.Misc.Unitary.hU pts pos genAll xy xP yP perpAll tabAll memAll
    distinct orb0 orb1 orb2 conjAll pa row0 rowsAll symAll inter diamAll muAll paAcyc

end CFSG.KD.Misc.Xi

end

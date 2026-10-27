module

public import Certificates.Kernel.SporSch.HN.FixK.Tab

public section

namespace CFSG.KD.HNXK

open CFSG.KC.LL.HNX CFSG.KD.LgHNX

theorem fixOk_spec {G : Nat} {V : Nat → Nat} {m k : Nat} (h : fixOk G V m k = true) :
    Nat.beq (fixSum TX CM3 M G (2227 * k) (fixLen k)) (V (8 * m + k)) = true := h

end CFSG.KD.HNXK

end

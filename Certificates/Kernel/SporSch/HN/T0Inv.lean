module

public import Certificates.Kernel.SporSch.HN.T0Data
public import Certificates.Data.Kernel.SporSch.HNT0P
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSporSch.HNT0

open CFSG.KD.HNT0 CFSG.KS.HNT0 CFSG.KS.EnumBase CFSG.KC.Enum

#kc_each CertificateChecks.KernelSporSch.HNT0 ch10509v
  (fun s => strictB (maskL INV) fun IM => sliceK 16384 1024 (censK 8 255 BP T IM) s) 0 16

theorem inv_len : Nat.beq (lenK INV) 687 = true := by quickRfl

theorem inv_list : invLK 8 255 BP 16384 24 T IL KB INV 0 0 = true := by quickRfl

theorem zp : bAnd(Nat.blt ZP 687, Nat.beq (IL ZP) GT4) = true := by quickRfl

theorem neg_cens : Bool.not (censK 8 255 BP T (Nat.lor (maskL INV) 1) 0) = true := by quickRfl
theorem neg_cens2 : Bool.not (strictB (maskL INV.tail) fun IM =>
    censK 8 255 BP T IM (INV.getD 0 0)) = true := by quickRfl
theorem neg_invl : Bool.not (invLK 8 255 BP 16384 24 T (fun a => IL (Nat.succ a)) KB INV 0 0) =
    true := by quickRfl
theorem neg_kb : Bool.not (invLK 8 255 BP 16384 24 T IL (Nat.shiftRight KB 24) INV 0 0) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.HNT0

end

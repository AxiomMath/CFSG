
module

public import Certificates.Kernel.SporSch.Co2M.ThEQR
public import Certificates.Kernel.SporSch.Co2M.ThEQD
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.Co2LE

theorem te_qconj0 : allN 5 (fun i => allN 1024 (fun k =>
    conjK TQR (TGM i) (TGMI i) (Co2EQ.S i) 11 1024 k)) = true := by
  quickRfl

theorem te_qconj1 : allN 5 (fun i => allN 1024 (fun k =>
    conjK TQR (TGM (Nat.add 5 i)) (TGMI (Nat.add 5 i)) (Co2EQ.S (Nat.add 5 i)) 11 1024 k)) =
    true := by
  quickRfl

theorem te_qconj2 : allN 5 (fun i => allN 1024 (fun k =>
    conjK TQR (TGM (Nat.add 10 i)) (TGMI (Nat.add 10 i)) (Co2EQ.S (Nat.add 10 i)) 11 1024 k)) =
    true := by
  quickRfl

end CertificateChecks.KernelSporSch.Co2M

end

module

public import Certificates.Kernel.He589208.D
public import Certificates.Kernel.SporSch.HeT.Tab
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.He589208

open CertificateChecks.KernelSpor

@[expose] noncomputable def t0 (x : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 (HeC.S 0) x

theorem comm_ok : [S.TF 0, S.TF 1].all (fun c => [0, 1, 2, 3, 4].all fun x =>
    CFSG.KC.LQT.PW.imgW 14 c (t0 x) == t0 (CFSG.KC.LQT.PW.imgW 14 c x)) = true := by
  quickRfl

end CFSG.KD.He589208

end

module

public import Certificates.Data.Kernel.PermCent.U43P1Chk
public import Certificates.Kernel.PermCent.U43P1A6
public import Certificates.Kernel.PermCent.U43P1Cen
public import Certificates.Kernel.PermCent.U43P1S

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.KC.Enum CFSG.KS

theorem bindsS :
    (gensOK sylM1 SM1.G && gensOK sylF SF.G && gensOK sylI SI.G && gensOK cgIn CgIn.G &&
      gensOK gsIn KIn.G && gensOK gsFb FFb.G && gensOK cgM1a CgM1a.G &&
      gensOK (lM1a.map (·, false)) LM1a.G && gensOK cgIa CgIa.G &&
      gensOK (lIa.map (·, false)) LIa.G &&
      ([SM1.T 0, SF.T 0, SI.T 0, CgIn.T 0, KIn.T 0, FFb.T 0, CgM1a.T 0, LM1a.T 0, CgIa.T 0,
        LIa.T 0].all fun p => Nat.beq p (pidn 820 10))) = true ∧
    SM1.N = 256 ∧ SF.N = 256 ∧ SI.N = 256 ∧ CgIn.N = 1152 ∧ KIn.N = 288 ∧ FFb.N = 960 ∧
    CgM1a.N = 720 ∧ LM1a.N = 360 ∧ CgIa.N = 720 ∧ LIa.N = 360 ∧
    SM1.ng = 4 ∧ SF.ng = 4 ∧ SI.ng = 3 ∧ CgIn.ng = 2 ∧ KIn.ng = 2 ∧ FFb.ng = 2 ∧ CgM1a.ng = 2 ∧
    LM1a.ng = 2 ∧ CgIa.ng = 2 ∧ LIa.ng = 2 := by
  decide +kernel

end CertificateChecks.KernelPermCent.U43P1

end

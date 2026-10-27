module

public import Certificates.Kernel.Sporadic.OddCore.HeL2
public import Certificates.Data.HeInvPerfect
meta import Certificates.Data.HeInvPerfect
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.He7200

meta def cM : Array (Array Nat) := CFSG.Quasithin.E6.HeInvPerfect.heX1CommGens

end CertificateChecks.KernelSpor.He7200

#kpenum CertificateChecks.KernelSpor.HCE 42 6 false CertificateChecks.KernelSpor.He7200.cM
  CertificateChecks.KernelSpor.He7200.cM CertificateChecks.KernelSpor.He2276.id42 10752

namespace CertificateChecks.KernelSpor.He7200

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

@[expose] noncomputable def commP (a b : Nat) : Nat :=
  pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (HXE.G a) (HXE.G b)) (HXI a))
    (HXI b)

theorem c_gens : bAnd(Nat.beq HCE.k 2, bAnd(Nat.beq (HCE.G 0) (commP 2 8),
    Nat.beq (HCE.G 1) (commP 3 8))) = true := by
  quickRfl

theorem c_hd : penumHdK (pidn 42 6) HCE.cnt 10752 HCE.T HCE.PL = true := by
  quickRfl

theorem c_sl0 : penumSlK 42 6 (mask 6) (42 * 6) false HCE.G HCE.GI HCE.k HCE.cnt HCE.T HCE.PL
    HCE.POS HCE.SRT HCE.SRI 0 2688 = true := by
  quickRfl

theorem c_sl1 : penumSlK 42 6 (mask 6) (42 * 6) false HCE.G HCE.GI HCE.k HCE.cnt HCE.T HCE.PL
    HCE.POS HCE.SRT HCE.SRI 2688 2688 = true := by
  quickRfl

theorem c_sl2 : penumSlK 42 6 (mask 6) (42 * 6) false HCE.G HCE.GI HCE.k HCE.cnt HCE.T HCE.PL
    HCE.POS HCE.SRT HCE.SRI 5376 2688 = true := by
  quickRfl

theorem c_sl3 : penumSlK 42 6 (mask 6) (42 * 6) false HCE.G HCE.GI HCE.k HCE.cnt HCE.T HCE.PL
    HCE.POS HCE.SRT HCE.SRI 8064 2688 = true := by
  quickRfl

end CertificateChecks.KernelSpor.He7200

end

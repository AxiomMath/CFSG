module

public import Certificates.Kernel.SporSch.PairJ3.ClFns
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.PairClTSound
public import CFSG.Certificates.Kernel.SporSch.PairKSound

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PJ3Cl CertificateChecks.KernelSporSch.PJ3Cl.recB 0 52 8
#kss_b2all CertificateChecks.KernelSporSch.PJ3Cl CertificateChecks.KernelSporSch.PJ3Cl.recB 52 8
#kss_b2 CertificateChecks.KernelSporSch.PJ3Cl CertificateChecks.KernelSporSch.PJ3Cl.srtB 0 52 8
#kss_b2all CertificateChecks.KernelSporSch.PJ3Cl CertificateChecks.KernelSporSch.PJ3Cl.srtB 52 8

namespace CertificateChecks.KernelSporSch.PJ3Cl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] noncomputable def RP0 : List Nat := [PJ3.S 0]

theorem canon0 : canonL 6156 13 RP0 = true := by quickRfl
theorem ltbs : ltL 6156 CFSG.Sporadic.Schreier.PairJ3.bs = true := by quickRfl
theorem st0 : startNFT 6156 13 5 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT PJ3T.QT 4
    (wordKey 6156 13 CFSG.Sporadic.Schreier.PairJ3.bs RP0) (X 0) = true := by quickRfl
theorem k0 : Nat.beq (K 0) (wordKey 6156 13 CFSG.Sporadic.Schreier.PairJ3.bs RP0) = true := by
  quickRfl
theorem c00 : Nat.beq (PJ3T.C 0) 1 = true := by quickRfl
theorem c0N : Nat.beq (PJ3T.C (Nat.mul 103 8)) PJ3T.c = true := by quickRfl
theorem cSz : Nat.beq PJ3T.c 26163 = true := by quickRfl

end CertificateChecks.KernelSporSch.PJ3Cl

end

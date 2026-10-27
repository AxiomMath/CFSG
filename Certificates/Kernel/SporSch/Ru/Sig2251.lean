module

public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Kernel.VecCert.Ru
public import CFSG.Certificates.Kernel.SporSch.RuEnumSound
public import CFSG.Sporadic.Schreier.RuCheckIsoInputs
meta import CFSG.Sporadic.Schreier.RuCheckIsoInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.RuSig CFSG.Sporadic.RuSchreier.ruSigmaText

namespace CertificateChecks.KernelSporSch.RuSig

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

meta def sigM : Array Nat := ruSigmaA

meta def sigiM : Array Nat := ruInv ruSigmaA

end CertificateChecks.KernelSporSch.RuSig

#ks_perm CertificateChecks.KernelSporSch.RuSig.SIG 12 CertificateChecks.KernelSporSch.RuSig.sigM
#ks_perm CertificateChecks.KernelSporSch.RuSig.SIGI 12 CertificateChecks.KernelSporSch.RuSig.sigiM

namespace CertificateChecks.KernelSporSch.RuSig

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.VecK
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelVec.Ru

theorem sigK : hexPackK 3 4060 4060 0 4060 12 SIG chars = true := by quickRfl
theorem pSig : pk SIG SIGI = true := by quickRfl
theorem sigLt : allN 4060 (fun i => Nat.blt (pg 12 (mask 12) SIG i) 4060) = true := by quickRfl
theorem a0Lt : allN 4060 (fun i => Nat.blt (pg 12 (mask 12) A0 i) 4060) = true := by quickRfl
theorem a1Lt : allN 4060 (fun i => Nat.blt (pg 12 (mask 12) A1 i) 4060) = true := by quickRfl
theorem eqA0 : allN 4060 (fun i => Nat.beq (pg 12 (mask 12) SIG (pg 12 (mask 12) A0 i))
    (lk AT 32 (pg 12 (mask 12) SIG i))) = true := by quickRfl
theorem eqA1 : allN 4060 (fun i => Nat.beq (pg 12 (mask 12) SIG (pg 12 (mask 12) A1 i))
    (lk BT 32 (pg 12 (mask 12) SIG i))) = true := by quickRfl
theorem seed : seedK csA csB 28 MA MB NA NB 2 4 = true := by quickRfl
theorem p0 : Nat.beq (lk Pt 32 0) 1 = true := by quickRfl

end CertificateChecks.KernelSporSch.RuSig

end

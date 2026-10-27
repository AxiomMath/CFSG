module

public import Certificates.Kernel.SporSch.GenSetReplay
public import Certificates.Kernel.Sporadic.McLK.Data
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLCheckInputs
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_setreplay CertificateChecks.KernelSpor.McLCOZ 275 9 CFSG.ClassicalInvolution.McLProof.abArr
  CFSG.ClassicalInvolution.McLProof.fixZ 22275 16 64 64

namespace CertificateChecks.KernelSpor.McLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.McLK

@[expose] noncomputable def fixL : List Nat :=
  (List.range 275).filter fun p => Nat.beq (r32 AL p) p

theorem permZ : allN 2 (fun k => permOK 275 9 (mask 9) (275 * 9) (McLCOZ.G k)
    (McLCOZ.GI k)) = true := by quickRfl

theorem gensZ : allN 275 (fun x => bAnd(Nat.beq (pg 9 (mask 9) (McLCOZ.G 0) x) (r32 AL x),
    Nat.beq (pg 9 (mask 9) (McLCOZ.G 1) x) (r32 BE x))) = true := by quickRfl

theorem startZ : startK 9 35 (rowGet McLCOZ.XT 343 0) fixL = true := by quickRfl

theorem cntZ : bAnd(Nat.beq (McLCOZ.C 0) 1, Nat.beq (McLCOZ.C (McLCOZ.nS * 64)) 22275) = true := by
  quickRfl

end CertificateChecks.KernelSpor.McLC

end

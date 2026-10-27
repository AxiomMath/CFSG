module

public import Certificates.Kernel.Sporadic.Co3.C
public import CFSG.Sporadic.Schreier.Co3StabItInputs
meta import CFSG.Sporadic.Schreier.Co3StabItInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.Co3SI CFSG.Sporadic.Schreier.Co3.co3StabItText

#ks_hexlines CertificateChecks.KernelSporSch.Co3SI CFSG.Sporadic.Schreier.Co3.co3StabItText 3 276 9

#ks_rawchain CertificateChecks.KernelSporSch.Co3SIC 276 9 16 CFSG.Sporadic.Schreier.Co3.co3StabItArrs
  CFSG.Sporadic.Schreier.Co3.co3StabItBaseArr 8 CFSG.Sporadic.Schreier.Co3.co3StabItDerivations

namespace CertificateChecks.KernelSporSch.Co3SIC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSpor

theorem lines : allN 8 (fun j => Nat.beq (S j) (Co3SI.L j)) = true := by quickRfl

theorem perm : allN 8 (fun j => permOK 276 9 (mask 9) (276 * 9) (S j) (SI j)) = true := by
  quickRfl

theorem sift : allN 8 (fun j => bAnd(Co3C.sift (S j), Co3Text.hiOK (S j))) = true := by quickRfl

theorem lev5a : Nat.beq (rpt 9 (mask 9) (LR 5) 1) 109 = true := by quickRfl

theorem lev5b : Nat.beq (rpt 9 (mask 9) (LR 5) 2) 70 = true := by quickRfl

end CertificateChecks.KernelSporSch.Co3SIC

end

module

public import Certificates.Kernel.Sporadic.ONPar.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.ON5.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPar

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.ONSchreier
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
open CertificateChecks.KernelSpor.ON3 (siftT blkK)
open CertificateChecks.KernelSpor.ON8 (onP)

theorem neg_sift : Bool.not (siftT xK) = true := by quickRfl

theorem neg_rel : Bool.not (onP (fun y => xK (xK y)) (fun y => y)) = true := by quickRfl

theorem neg_r : Bool.not (allN 32 fun k => strictB (nIf(Nat.beq k 5, 5, onpV32[k]!)) fun t =>
    bAnd(Nat.blt t 32, Nat.beq Data.TPoints[t]! (vK Data.TPoints[k]!))) = true := by quickRfl

theorem neg_b : Bool.not (blkK vK fun i => nIf(Nat.beq i 0, 0, onpVB[i]!)) = true := by quickRfl

end CertificateChecks.KernelSpor.ONPar

end

module

public import Certificates.Kernel.TitsOver.Five.LEnum
public import Certificates.Kernel.TitsOver.Five.LData
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.Kernel.MaxD2.Pair
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row

theorem l_srt : allN LE.cnt (sortK 11 3 33 LE.cnt (r32 LPT) LE.T LFS LKS) = true := by quickRfl
theorem l_lab : labK 1755 11 LE.k LE.G (r32 LL) = true := by quickRfl
theorem l_t1 : repK 1755 11 3 33 LE.cnt (r32 LPT) LE.T LFS LKS LREP LREPI LRB LH 1 = true := by
  quickRfl
theorem l_t2 : repK 1755 11 3 33 LE.cnt (r32 LPT) LE.T LFS LKS LREP LREPI LRB LH 2 = true := by
  quickRfl
theorem l_t3 : repK 1755 11 3 33 LE.cnt (r32 LPT) LE.T LFS LKS LREP LREPI LRB LH 3 = true := by
  quickRfl
theorem l_t4 : repK 1755 11 3 33 LE.cnt (r32 LPT) LE.T LFS LKS LREP LREPI LRB LH 4 = true := by
  quickRfl
theorem l_t5 : repK 1755 11 3 33 LE.cnt (r32 LPT) LE.T LFS LKS LREP LREPI LRB LH 5 = true := by
  quickRfl
theorem l_t6 : repK 1755 11 3 33 LE.cnt (r32 LPT) LE.T LFS LKS LREP LREPI LRB LH 6 = true := by
  quickRfl
theorem l_pk : allN 7 (fun i => allN 7 (fun j => bIf(Nat.blt i j,
    bIf(Nat.beq (rg 128 (mask 128) LMK 0 i) (rg 128 (mask 128) LMK 0 j),
      pairK 1755 11 3 33 LE.cnt (r32 LPT) LE.T LFS LKS LREP LREPI LRB2 LH2
        (r32 LPQ (Nat.add (Nat.mul 7 i) j)) i j, true), true))) = true := by quickRfl

end CertificateChecks.KernelTitsOver.Five

end

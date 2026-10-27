
module

public import Certificates.Kernel.SporSch.Co2M.ThED
public import Certificates.Kernel.SporSch.Co2M.ThEMD
public import Certificates.Kernel.Sporadic.Co2.ChainA
import CFSG.Certificates.Kernel.Common.Harness
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import Init.Data.Array.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.Sporadic.Co2Schreier
open CFSG.Sporadic.SmallF2.Native

theorem te_rows : allN 15 (fun j => allN 22 fun k => Nat.beq (pg 22 M22 (TGM j) k)
    ((transposeRows 22 ((oddMats witRec).getD j []).toArray)[k]?.getD 0)) = true := by
  quickRfl

theorem te_bind0 : allN 5 (fun j => bindK (PV 0) (Co2E.S j) (TGM j) (TGMI j)) = true := by
  quickRfl

theorem te_bind1 : allN 5 (fun j => bindK (PV 0) (Co2E.S (Nat.add 5 j)) (TGM (Nat.add 5 j))
    (TGMI (Nat.add 5 j))) = true := by quickRfl

theorem te_bind2 : allN 5 (fun j => bindK (PV 0) (Co2E.S (Nat.add 10 j)) (TGM (Nat.add 10 j))
    (TGMI (Nat.add 10 j))) = true := by quickRfl

theorem te_sift : allN 15 (fun j => siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12)
    CertificateChecks.KernelSpor.Co2A.LR CertificateChecks.KernelSpor.Co2A.TRI
    CertificateChecks.KernelSpor.Co2A.BP 6 0 (Co2E.S j)) = true := by quickRfl

theorem te_comm : allN 15 (fun j => Nat.beq (cmpP (teGT.getD j (0, 0)) teU).1
    (cmpP teU (teGT.getD j (0, 0))).1) = true := by quickRfl

end CertificateChecks.KernelSporSch.Co2M

end

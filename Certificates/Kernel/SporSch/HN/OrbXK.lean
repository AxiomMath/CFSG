module

public import Certificates.Kernel.SporSch.HN.GenHNX
public import CFSG.Certificates.Kernel.Orders.HN.Data.Sel
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import Certificates.Kernel.SporSch.HN.X.Base
public import Certificates.Kernel.SporSch.HN.X.All
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Sporadic.HNSchreier.Data

public section

set_option maxRecDepth 400000

#kc_repo #kc_nat_items_gz CertificateChecks.KernelSporSch.HNX
  "Certificates/Kernel/SporSch/HN/data/hnx_qg.items.gz" 28746 12855385252245474925 QG
#kss_strlits CertificateChecks.KernelSporSch.HNXRoot CFSG.Sporadic.HNSchreier.Data.rootDigits

namespace CertificateChecks.KernelSporSch.HNXOrb

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KD.LgHNX CFSG.KD.OrdHN
open CertificateChecks.KernelSporSch

theorem sum_ok : Nat.beq (sumK HNX.CNT) 1139999 = true := by quickRfl
theorem link_ok : linkK HNX.SGT = true := by quickRfl
theorem root_ok : rootK V0C (HNXRoot.c0 ++ HNXRoot.c1) = true := by quickRfl
theorem basis_ok : qBasisK TX CM3 CFSG.Sporadic.HNSchreier.Data.checkPts.toList HNX.QG = true := by
  quickRfl

theorem neg_root : Bool.not (rootK V0C (HNXRoot.c1 ++ HNXRoot.c0)) = true := by quickRfl
theorem neg_sum : Bool.not (Nat.beq (sumK fun b => Nat.succ (HNX.CNT b)) 1139999) = true := by
  quickRfl
theorem neg_link :
    Bool.not (linkK fun m => Nat.add (HNX.SGT m) (nIf(Nat.beq m 5000, 1, 0))) = true := by
  quickRfl
theorem neg_basis :
    Bool.not (qBasisK TX CM3 CFSG.Sporadic.HNSchreier.Data.checkPts.toList (Nat.xor HNX.QG 1)) =
      true := by
  quickRfl
theorem neg_basisQ :
    Bool.not (qBasisK TX CM3 (CFSG.Sporadic.HNSchreier.Data.checkPts.toList.map Nat.succ) HNX.QG) =
      true := by
  quickRfl
theorem neg_canon :
    Bool.not (qBasisK TX CM3 CFSG.Sporadic.HNSchreier.Data.checkPts.toList (Nat.add HNX.QG 5)) =
      true := by
  quickRfl
theorem neg_core : Bool.not (Nat.beq (coreLeaf TX 464 1140000 MS CM3 M GA GB 5 (hnxC 5))
    (Nat.succ (HNX.CNT 5))) = true := by quickRfl
theorem neg_sort : Bool.not (sortChunk TX 464 1140000
    (Nat.lor (Nat.shiftLeft (HNX.SGT 5) 21) (Nat.land (HNX.SGT 5) 2097151)) (hnxS 5)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.HNXOrb

end

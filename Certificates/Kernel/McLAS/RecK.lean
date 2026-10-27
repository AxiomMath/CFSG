module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.Kernel.McLAS.Slices
public import Certificates.Data.Kernel.McLAS.Pair
meta import Certificates.Kernel.McLAS.Meta
import Certificates.Kernel.McLAS.Meta

namespace CertificateChecks.KernelMcLAS.M

meta def kR : Array (Array Nat) := mulRec kgM 30000
meta def poR : Array (Array Nat) := conjRec kgM kgiM pairM 200

end CertificateChecks.KernelMcLAS.M

public section

#kmulh CertificateChecks.KernelMcLAS.RK 275 9 CertificateChecks.KernelMcLAS.M.ids3M
  CertificateChecks.KernelMcLAS.M.kgM CertificateChecks.KernelMcLAS.M.idM 30000
#kmulh CertificateChecks.KernelMcLAS.PO 275 9 CertificateChecks.KernelMcLAS.M.kgM
  CertificateChecks.KernelMcLAS.M.kgiM CertificateChecks.KernelMcLAS.M.pairM 200
#kfind CertificateChecks.KernelMcLAS.KinPO CertificateChecks.KernelMcLAS.M.poR
  CertificateChecks.KernelMcLAS.M.kR

namespace CertificateChecks.KernelMcLAS

open CFSG.KS.McLAS in
@[expose] noncomputable def selK (q : Nat) : Bool :=
  CFSG.KC.Enum.strictB (RK.T q) fun x => bIf(pairSelK (RK.GI 0) x, atK PO.cnt PO.T KinPO q x, true)

@[expose] noncomputable def cK (i : Nat) : Bool :=
  bAnd(CFSG.KS.McLAS.recSlK true RK.G RK.GI 3 RK.cnt RK.T RK.PL RK.POS RK.SRT RK.SRI RK.HS RK.HSI
    (Nat.mul i 200) 200, CFSG.KS.MulH.slK RK.cnt selK (Nat.mul i 200) 200)

end CertificateChecks.KernelMcLAS

end

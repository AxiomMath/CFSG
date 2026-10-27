module

public import Certificates.Kernel.Sp6Insp443.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS6I

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.Sp6I CertificateChecks.KernelLC.Sp6J

@[expose] noncomputable def ch725106i (k : Nat) : Bool :=
  bAnd(allN (D.nU.getD k 0) (fun j => permOK 36 6 (mask 6) (36 * 6)
      (laneK (36 * 6) (D.uT.getD k 0) j) (laneK (36 * 6) (D.uT.getD k 0) j)),
    allN (D.nW.getD k 0) (fun j => permOK 36 6 (mask 6) (36 * 6)
      (laneK (36 * 6) (D.wT.getD k 0) j) (laneK (36 * 6) (D.wT.getD k 0) j)))

#kc_each ch725106i 0 12

theorem ch725106n_inv : notB (allN 1 (fun j => permOK 36 6 (mask 6) (36 * 6)
    (laneK (36 * 6) (XQ.S 1) j) (laneK (36 * 6) (XQ.S 1) j))) = true := by
  quickRfl

end CertificateChecks.KernelS6I

end

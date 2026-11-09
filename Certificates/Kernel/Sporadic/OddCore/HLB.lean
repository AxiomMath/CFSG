module

public import Certificates.Kernel.Sporadic.OddCore.HL
public import Certificates.Data.Kernel.Spor.PEnumBC
meta import CFSG.Sporadic.SmallOddCore.HeLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HeL

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore

meta def dsortM : Array Nat :=
  let key := fun (t : Array Nat) => [0, 1, 2].foldr (fun b a => a * 4096 + t[b]!) 0
  ((heDEnum.tabs.mapIdx fun i t => (key t, i)).qsort fun a b => a.1 < b.1).map (·.2)

meta def dsortRowsM : Array (Array Nat) := dsortM.map fun s => #[s]

meta def dsortInvM : Array (Array Nat) :=
  (dsortM.zipIdx.qsort fun a b => a.1 < b.1).map fun p => #[p.2]

end CertificateChecks.KernelSpor.HeL

#kmisc_packarrs CertificateChecks.KernelSpor.HDBS CertificateChecks.KernelSpor.HeL.dsortRowsM 32
#kmisc_packarrs CertificateChecks.KernelSpor.HDBSI CertificateChecks.KernelSpor.HeL.dsortInvM 32

namespace CertificateChecks.KernelSpor.HeL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.PEnumB

theorem dsort_ok : allN 20160 (bsortLK 7 (mask 7) [0, 1, 2] HDE.cnt HDE.T HDBS HDBSI) = true := by
  quickRfl

theorem dinv_ok : allN 5 (fun j => strictB (CFSG.KS.Mathieu.nget [6, 2, 17, 23, 29] j) (fun a =>
    bAnd(Nat.blt a HDE.cnt, Nat.beq (HDE.T a) (HDI j)))) = true := by
  quickRfl

theorem drep_ok : allN 10 (fun l => strictB (CFSG.KS.Mathieu.nget [0, 2, 8, 24, 59, 1, 46, 68, 10, 33] l)
    (fun a => bAnd(Nat.blt a HDE.cnt, Nat.beq (HDE.T a) (HOF.R l)))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.HeL

end

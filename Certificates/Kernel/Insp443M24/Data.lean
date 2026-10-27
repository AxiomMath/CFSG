module

public import Certificates.Kernel.KGC31M24.Data7217
public import Certificates.Data.Insp443M24
public meta import Certificates.Kernel.KGC31M24.Data7217
public meta import Certificates.Data.Insp443M24

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelInsp443M24

open CFSG.KS.SporSch.MOCG CFSG.SectionRank.QTK.Insp443.M24

meta def base4 : Array Nat := #[0, 1, 2, 3]

meta def SCB : Array (Array Nat) :=
  strongOf 24 (cjW.map fun w => CertificateChecks.KernelKGC31M24.gcj w xW).toArray cbChainW

end CertificateChecks.KernelInsp443M24

#ks_rawchain CertificateChecks.KernelInsp443M24.CCB 24 5 16 CertificateChecks.KernelInsp443M24.SCB
  CertificateChecks.KernelInsp443M24.base4 3 CFSG.SectionRank.QTK.Insp443.M24.cbChainW

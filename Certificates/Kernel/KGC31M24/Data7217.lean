module

public import Certificates.Kernel.KGC31M24.Data
public meta import Certificates.Kernel.KGC31M24.Data

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M24

open CFSG.KS.SporSch.MOCG CFSG.Quasithin.KGC31.M24

meta def gcj (g y : List Int) : Array Nat := comp (comp (gw g) (gw y)) (invA (gw g))

meta def base5 : Array Nat := #[0, 1, 2, 3, 4]

meta def base6 : Array Nat := #[0, 1, 2, 3, 4, 5]

meta def SMO : Array (Array Nat) := strongOf 24 (moGenW.map gw).toArray moChainW
meta def SNS : Array (Array Nat) := strongOf 24 (nsGenW.map gw).toArray nsChainW
meta def SLS : Array (Array Nat) := strongOf 24 (njW.map fun w => gcj w y5W).toArray lsChainW
meta def SNQ : Array (Array Nat) := strongOf 24 (nqGenW.map gw).toArray nqChainW
meta def SLQ : Array (Array Nat) := strongOf 24 (mjW.map fun w => gcj w y7W).toArray lqChainW
meta def SNT : Array (Array Nat) := strongOf 24 (ntGenW.map gw).toArray ntChainW
meta def SKQ : Array (Array Nat) := strongOf 24 (kqGenW.map gw).toArray kqChainW

end CertificateChecks.KernelKGC31M24

#ks_rawchain CertificateChecks.KernelKGC31M24.CMO 24 5 16 CertificateChecks.KernelKGC31M24.SMO
  CertificateChecks.KernelKGC31M24.base5 2 CFSG.Quasithin.KGC31.M24.moChainW

#ks_rawchain CertificateChecks.KernelKGC31M24.CNS 24 5 16 CertificateChecks.KernelKGC31M24.SNS
  CertificateChecks.KernelKGC31M24.base6 2 CFSG.Quasithin.KGC31.M24.nsChainW

#ks_rawchain CertificateChecks.KernelKGC31M24.CLS 24 5 16 CertificateChecks.KernelKGC31M24.SLS
  CertificateChecks.KernelKGC31M24.base5 3 CFSG.Quasithin.KGC31.M24.lsChainW

#ks_rawchain CertificateChecks.KernelKGC31M24.CNQ 24 5 16 CertificateChecks.KernelKGC31M24.SNQ
  CertificateChecks.KernelKGC31M24.base5 2 CFSG.Quasithin.KGC31.M24.nqChainW

#ks_rawchain CertificateChecks.KernelKGC31M24.CLQ 24 5 16 CertificateChecks.KernelKGC31M24.SLQ
  CertificateChecks.KernelKGC31M24.base5 3 CFSG.Quasithin.KGC31.M24.lqChainW

#ks_rawchain CertificateChecks.KernelKGC31M24.CNT 24 5 16 CertificateChecks.KernelKGC31M24.SNT
  CertificateChecks.KernelKGC31M24.base5 2 CFSG.Quasithin.KGC31.M24.ntChainW

#ks_rawchain CertificateChecks.KernelKGC31M24.CKQ 24 5 16 CertificateChecks.KernelKGC31M24.SKQ
  CertificateChecks.KernelKGC31M24.base5 2 CFSG.Quasithin.KGC31.M24.kqChainW

end

module

public import Certificates.Kernel.KGC31M23.Defs
public meta import Certificates.Kernel.SporSch.Mathieu.M23Data
public meta import CFSG.Quasithin.Vol2.KGFactC31M23Data
public meta import CFSG.Quasithin.Vol2.KGFactC31CosetCheck
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M23

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M23OC CFSG.Quasithin.KGC31.M23

meta def gw (wd : List Int) : Array Nat :=
  wd.foldr (fun l acc => comp (if l = 1 then tAM else tBM) acc) (idA 23)

meta def baseW : Array Nat := #[0, 1, 2, 3, 5]
meta def baseT : Array Nat := #[1, 2, 3]
meta def baseE : Array Nat := #[0, 1, 2]

meta def SW : Array (Array Nat) := strongOf 23 (wGenW.map gw).toArray wChainW
meta def ST : Array (Array Nat) := strongOf 23 (tGenW.map gw).toArray tChainW
meta def SE : Array (Array Nat) := strongOf 23 (eGenW.map gw).toArray eChainW

end CertificateChecks.KernelKGC31M23

#ks_rawchain CertificateChecks.KernelKGC31M23.CW 23 5 16 CertificateChecks.KernelKGC31M23.SW
  CertificateChecks.KernelKGC31M23.baseW 2 CFSG.Quasithin.KGC31.M23.wChainW

#ks_rawchain CertificateChecks.KernelKGC31M23.CT 23 5 16 CertificateChecks.KernelKGC31M23.ST
  CertificateChecks.KernelKGC31M23.baseT 2 CFSG.Quasithin.KGC31.M23.tChainW

#ks_rawchain CertificateChecks.KernelKGC31M23.CE 23 5 16 CertificateChecks.KernelKGC31M23.SE
  CertificateChecks.KernelKGC31M23.baseE 2 CFSG.Quasithin.KGC31.M23.eChainW

end

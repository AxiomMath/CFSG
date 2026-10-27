module

public import Certificates.Kernel.SporSch.Mathieu.M22Data
public import CFSG.Quasithin.Vol2.KGFactC31M22Data
public meta import Certificates.Kernel.SporSch.Mathieu.M22Data
public meta import CFSG.Quasithin.Vol2.KGFactC31M22Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Quasithin.Vol2.KGFactC31OrbCheck
public import CFSG.Quasithin.Vol2.KGFactC31OrbCheck

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelKGC31M22.W
  "Certificates/Kernel/KGC31M22/data/conj.json.gz" 1332 10439404847872790791
  (hexR0 : List Nat) (hexRs : List (List Nat)) (duadR0 : List Nat) (duadRs : List (List Nat))
  (e8R0 : List Nat) (e8Rs : List (List Nat))

namespace CertificateChecks.KernelKGC31M22

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M22OC

meta def gw (wd : List Int) : Array Nat :=
  wd.foldr (fun l acc => comp (if l = 1 then tAM else tBM) acc) (idA 22)

meta def SHX : Array (Array Nat) :=
  strongOf 22 (CFSG.Quasithin.KGC31.M22.hexGenW.map gw).toArray CFSG.Quasithin.KGC31.M22.hexChainW

meta def SDU : Array (Array Nat) :=
  strongOf 22 (CFSG.Quasithin.KGC31.M22.duadGenW.map gw).toArray
    CFSG.Quasithin.KGC31.M22.duadChainW

meta def baseHX : Array Nat := #[0, 1, 2, 3]

meta def baseDU : Array Nat := #[2, 3, 4]

end CertificateChecks.KernelKGC31M22

#ks_rawchain CertificateChecks.KernelKGC31M22.CHX 22 5 16 CertificateChecks.KernelKGC31M22.SHX
  CertificateChecks.KernelKGC31M22.baseHX 2 CFSG.Quasithin.KGC31.M22.hexChainW

#ks_rawchain CertificateChecks.KernelKGC31M22.CDU 22 5 16 CertificateChecks.KernelKGC31M22.SDU
  CertificateChecks.KernelKGC31M22.baseDU 2 CFSG.Quasithin.KGC31.M22.duadChainW

end

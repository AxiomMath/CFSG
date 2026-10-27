module

public import Certificates.Kernel.SporSch.Mathieu.M24Data
public import Certificates.Kernel.LocalComp.Child3Gen
public import CFSG.Quasithin.Vol2.KGFactC31M24Data
public meta import Certificates.Kernel.SporSch.Mathieu.M24Data
public meta import CFSG.Quasithin.Vol2.KGFactC31M24Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck
public meta import CFSG.Quasithin.Vol2.KGFactC31CosetCheck
public import CFSG.Quasithin.Vol2.KGFactC31FrameCheck
public meta import CFSG.Quasithin.Vol2.KGFactC31FrameCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M24

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M24OC

meta def GM : Array (Array Nat) := #[tAM, tBM]

meta def gw (wd : List Int) : Array Nat :=
  wd.foldr (fun l acc => comp (if l = 1 then tAM else tBM) acc) (idA 24)

meta def repsL : List (Array Nat) := repsM.toList

meta def qGM : Array (Array Nat) := (CFSG.Quasithin.KGC31.M24.qGenW.map gw).toArray

meta def SQ : Array (Array Nat) := strongOf 24 qGM CFSG.Quasithin.KGC31.M24.qChainW

meta def baseQ : Array Nat := #[1, 0]

end CertificateChecks.KernelKGC31M24

#lc_reps CertificateChecks.KernelKGC31M24.RI 5 CertificateChecks.KernelKGC31M24.GM
  CertificateChecks.KernelKGC31M24.repsL

#ks_rawchain CertificateChecks.KernelKGC31M24.QQ 24 5 16 CertificateChecks.KernelKGC31M24.SQ
  CertificateChecks.KernelKGC31M24.baseQ 4 CFSG.Quasithin.KGC31.M24.qChainW

end

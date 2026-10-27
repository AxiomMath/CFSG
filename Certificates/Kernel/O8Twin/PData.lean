module

public import Certificates.Kernel.O8Twin.Chain
public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Kernel.SporSch.Mathieu.GenNL
public import Certificates.Kernel.Misc.ArgCharsFun
public import Certificates.Data.S7TwinO8
public meta import Certificates.Kernel.O8Twin.Chain
public meta import Certificates.Data.S7TwinO8
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8Twin

open CFSG.KS.SporSch.MOCG

meta def rootL : List (List Nat) :=
  (List.range 8).map fun i => ((CFSG.EvenSmallLie.OmegaEight.genArrs[i]!).extract 0 120).toList

meta def RSL : List (Array Nat) := Certificates.S7TwinO8.fourWords.map (evalW 120 gensT)

meta def id120 : Array Nat := idA 120

@[expose] noncomputable def One120 : Nat := CFSG.KC.Enum.pidn 120 7

end CertificateChecks.KernelO8Twin

#kss_packs CertificateChecks.KernelO8Twin.GP 7 CertificateChecks.KernelO8Twin.rootL

#kss_cntord CertificateChecks.KernelO8Twin.NS CertificateChecks.KernelO8Twin.ST 120 7
  CertificateChecks.KernelO8Twin.strongT CertificateChecks.KernelO8Twin.baseT
  CertificateChecks.KernelO8Twin.One120 CertificateChecks.KernelO8Twin.id120 4

#lc_reps CertificateChecks.KernelO8Twin.RS 7 CertificateChecks.KernelO8Twin.gensT
  CertificateChecks.KernelO8Twin.RSL

#kc_fun_arg_chars CertificateChecks.KernelO8Twin.CW Certificates.S7TwinO8.candWords

end

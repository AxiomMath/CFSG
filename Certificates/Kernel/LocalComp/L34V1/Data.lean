module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.L34V1Sound
public import Certificates.Data.CFSGNative.PSL3Four.Certificate
meta import Certificates.Data.CFSGNative.PSL3Four.L34Syl
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34V1G

open CFSG.PSL3Four.Native CFSG.YGroups.ModelNative

meta def fM : Array (Array Nat) := fGens ()

meta def idM : Array Nat := idTab 42

meta def yM : Array (Array Nat) := parsePerms (include_str "YP.txt")

meta def yiM : List Nat := (parsePerms (include_str "YI.txt")).toList.flatMap Array.toList

meta def wM : Array (Array Nat) := parsePerms (include_str "WP.txt")

end CertificateChecks.KernelLC.L34V1G

#kpenum CertificateChecks.KernelLC.FE 42 6 false CertificateChecks.KernelLC.L34V1G.fM
  CertificateChecks.KernelLC.L34V1G.fM CertificateChecks.KernelLC.L34V1G.idM 16
#kmisc_packarrs CertificateChecks.KernelLC.L34V1G.YP CertificateChecks.KernelLC.L34V1G.yM 80
#knatlist CertificateChecks.KernelLC.L34V1G.YI CertificateChecks.KernelLC.L34V1G.yiM
#kmisc_packarrs CertificateChecks.KernelLC.L34V1G.WP CertificateChecks.KernelLC.L34V1G.wM 9

end

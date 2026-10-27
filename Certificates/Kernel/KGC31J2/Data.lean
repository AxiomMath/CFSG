module

public import Certificates.Kernel.SporSch.Pair.J2Chain
public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Data.Kernel.J2Enum
public meta import Certificates.Data.CFSGNative.PairSchreier.J2Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31J2

meta def comp (t u : Array Nat) : Array Nat := u.map fun x => t[x]!

meta def a1 : Array Nat := CFSG.Sporadic.Schreier.PairNative.j2Strong 0

meta def a2 : Array Nat := CFSG.Sporadic.Schreier.PairNative.j2Strong 1

meta def GM : Array (Array Nat) := #[a1, a2]

meta def x12 : Array Nat := comp a1 (comp a2 (comp a1 (comp a2 a2)))

meta def repsL : List (Array Nat) :=
  [a1, comp x12 (comp x12 (comp x12 (comp x12 (comp x12 x12))))]

end CertificateChecks.KernelKGC31J2

#lc_reps CertificateChecks.KernelKGC31J2.RJ 9 CertificateChecks.KernelKGC31J2.GM
  CertificateChecks.KernelKGC31J2.repsL

#kc_repo #kc_json_gz CertificateChecks.KernelKGC31J2 "Certificates/Kernel/KGC31J2/data/enum.json.gz" 4957 438796266428538775
  (E0 : List Nat)

end

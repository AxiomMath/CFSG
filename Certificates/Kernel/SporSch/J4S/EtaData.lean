module

public import CFSG.Sporadic.Schreier.J4SNative

public section

namespace CertificateChecks.KernelSporSch.J4Eta

open CFSG.Sporadic.J4Schreier

@[expose] def etaData : Array Pair := #[Dn, Zn] ++ Array.ofFn Cn ++ Array.ofFn Un

end CertificateChecks.KernelSporSch.J4Eta

end

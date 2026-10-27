module

public import Certificates.Data.J2C4725

public section

namespace CertificateChecks.KernelJ2Cover

open CFSG.RankThree.PartTwo.J2Residue.C4725

@[expose] def keptFlat : Array Nat :=
  (keptTri ()).foldl (fun acc t => ((acc.push t.1).push t.2.1).push t.2.2) #[]

end CertificateChecks.KernelJ2Cover

end

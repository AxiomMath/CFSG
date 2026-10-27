module

public import Certificates.Kernel.LocalComp.Sp6J.Data
public meta import Certificates.Kernel.LocalComp.Sp6J.Data
public import Certificates.Kernel.SporSch.Mathieu.GenNL
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Sp6Root

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelLC.Sp6J

meta def tAM : Array Nat := XG[0]!

meta def tBM : Array Nat := XG[1]!

meta def rep1M : Array (Array Nat) := #[XG[0]!]

meta def p1M : Array Nat := evalW 36 CG2 [1, 1, 1, 1]

meta def p2M : Array Nat := evalW 36 CG2 [1, 1, 2, 1, 1, 2]

meta def sylM : List (List Nat) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j =>
    (comp (powA p1M i) (powA p2M j)).toList

end CertificateChecks.KernelLC.Sp6Root

#kss_list CertificateChecks.KernelLC.Sp6Root.tA CertificateChecks.KernelLC.Sp6Root.tAM

#kss_list CertificateChecks.KernelLC.Sp6Root.tB CertificateChecks.KernelLC.Sp6Root.tBM

#kss_classes CertificateChecks.KernelLC.Sp6Root.R1CL 36 6 CertificateChecks.KernelLC.Sp6Root.tAM
  CertificateChecks.KernelLC.Sp6Root.tBM CertificateChecks.KernelLC.Sp6Root.rep1M

#kss_packs CertificateChecks.KernelLC.Sp6Root.SylQ 6 CertificateChecks.KernelLC.Sp6Root.sylM

namespace CertificateChecks.KernelLC.Sp6Root

@[expose] noncomputable def D1 : CFSG.KS.MEnum.ClassDatum :=
  R1CL.getD 0 (0, 0, 0, [], [], [], [])

@[expose] noncomputable def S1 : List Nat := D1.2.2.2.2.2.2

end CertificateChecks.KernelLC.Sp6Root

end

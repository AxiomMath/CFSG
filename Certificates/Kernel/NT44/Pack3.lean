module

public import Certificates.Data.NT44Model.Inputs
public import Certificates.Data.NT44Commutator.Inputs
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Data.NT44Model.Inputs
public meta import Certificates.Data.NT44Commutator.Inputs

public section

namespace CertificateChecks.KernelNT44

open CFSG.GH74.GLS.NT44.PermutationNative

meta def trA : Array (Array Nat) := tr ()
meta def parA : Array (List Int) := parent ()
meta def trfM : Array (Array Nat) := #[trA.flatMap id]
meta def plM : Array (Array Nat) := #[parA.map fun wd =>
  4 * ((parA.findIdx? (· == wd.dropLast)).getD 0) + ((wd.getLastD 0).toNat - 1)]
meta def mulM (i j : Nat) : Nat := parA[j]!.foldl (fun x l => trA[x]![l.toNat - 1]!) i
meta def powM (i : Nat) : Nat → Nat
  | 0 => 0
  | e + 1 => mulM (powM i e) i
meta def o4M : Array (Array Nat) :=
  #[((List.range 256).filter fun i => powM i 4 == 0 && powM i 2 != 0).toArray]
meta def amM : Array (Array Nat) :=
  #[(actorSets ()).map fun L => L.foldl (fun m x => m ||| (1 <<< x.val)) 0]

end CertificateChecks.KernelNT44

end

#kmisc_packarrs CertificateChecks.KernelNT44.nt44TF CertificateChecks.KernelNT44.trfM 8
#kmisc_packarrs CertificateChecks.KernelNT44.nt44PL CertificateChecks.KernelNT44.plM 10
#kmisc_packarrs CertificateChecks.KernelNT44.nt44O4 CertificateChecks.KernelNT44.o4M 8
#kmisc_packarrs CertificateChecks.KernelNT44.nt44AM CertificateChecks.KernelNT44.amM 256

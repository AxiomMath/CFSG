module

public import Certificates.Data.NT44Model.Inputs
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.NT44.Pack
public import Certificates.Data.Kernel.Misc.ConjTab
public meta import Certificates.Data.NT44Model.Inputs
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CertificateChecks.KernelNT44

open CFSG.GH74.GLS.NT44.PermutationNative CFSG.Monster.B.Co2.Native

meta def vM : Array (Array Nat) :=
  (fwd ()).map fun w => wordA 2688 (ks ()) ((ks ()).map (invCand 2688)) w
meta def viM : Array (Array Nat) := vM.map (invCand 2688)
meta def sigM : Array (Array Nat) := Array.ofFn (n := 512) fun q =>
  compA 2688 (compA 2688 (lifts ())[q.val / 2]! (ks ())[q.val % 2]!)
    (invCand 2688 (lifts ())[q.val / 2]!)
meta def trM : Array (Array Nat) := tr ()
meta def ptsM : Array (Array Nat) := #[pts ()]
meta def parM : Array (Array Nat) := #[(parent ()).map fun wd =>
  ((parent ()).findIdx? (· == wd.dropLast)).getD 0]

end CertificateChecks.KernelNT44

end

#kmisc_packarrs CertificateChecks.KernelNT44.nt44V CertificateChecks.KernelNT44.vM 12
#kmisc_packarrs CertificateChecks.KernelNT44.nt44VI CertificateChecks.KernelNT44.viM 12
#kmisc_packarrs CertificateChecks.KernelNT44.nt44Sig CertificateChecks.KernelNT44.sigM 12
#kmisc_packarrs CertificateChecks.KernelNT44.nt44Tr CertificateChecks.KernelNT44.trM 8
#kmisc_packarrs CertificateChecks.KernelNT44.nt44Pts CertificateChecks.KernelNT44.ptsM 12
#kmisc_packarrs CertificateChecks.KernelNT44.nt44Par CertificateChecks.KernelNT44.parM 8

public section

namespace CertificateChecks.KernelNT44

@[expose] noncomputable def nt44TrAt : Nat → Bool :=
  CFSG.KC.Misc.ConjTab.transAt 2688 12 8 4 nt44Sig nt44L nt44LI nt44Tr (fun k => k + 1)

end CertificateChecks.KernelNT44

end

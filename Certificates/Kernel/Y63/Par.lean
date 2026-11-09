module

public import Certificates.Kernel.Y63.Data
meta import Certificates.Data.Y63.Check
public import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelY63

open CFSG.KC.Enum CFSG.KS CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

meta def parM : Array (Array Nat) :=
  let tab := tabRows ()
  let W := bfsWords tab ()
  #[(Array.range 512).map fun y =>
      ((W.getD y []).dropLast).foldl (fun a c => (tab.getD a #[]).getD c 0) 0,
    (Array.range 512).map fun y => ((W.getD y []).getLast?).getD 0]

end CertificateChecks.KernelY63

#kmisc_packarrs CertificateChecks.KernelY63.PART CertificateChecks.KernelY63.parM 9

namespace CertificateChecks.KernelY63

@[expose] noncomputable def parY (y : Nat) : Nat := f9 (PART 0) y

@[expose] noncomputable def letY (y : Nat) : Nat := f9 (PART 1) y

end CertificateChecks.KernelY63

end

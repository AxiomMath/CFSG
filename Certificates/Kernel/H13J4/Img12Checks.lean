module

public import Certificates.Kernel.H13J4.Img12Data

public section

namespace CertificateChecks.KernelH13.Img12

open CFSG.KJ4.S

theorem chain : chainRun (fun _ => 0) ET LET 0 0 0 GM ne LV = 2661120 := by
  decide +kernel

theorem chain_bad_tree :
    chainRun (fun _ => 0) ET LET 0 0 0 GM ne ((LV.headD 0 ^^^ 2 ^ 68) :: LV.tail) = 0 := by
  decide +kernel

theorem chain_bad_et :
    chainRun (fun _ => 0) (fun e => ET e ^^^ (Nat.beq e 3).toNat) LET 0 0 0 GM ne LV = 0 := by
  decide +kernel

theorem chain_bad_gm : chainRun (fun _ => 0) ET LET 0 0 0 1 ne LV = 0 := by
  decide +kernel

end CertificateChecks.KernelH13.Img12

end

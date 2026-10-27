module

public import Certificates.Data.Kernel.LayWords
public import Certificates.Kernel.Fi23U3.Snaps
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

public section

namespace CertificateChecks.KernelFi23U3

open CFSG.KC.LayWords CFSG.SectionRank.Native CertificateChecks.KernelTc.Fi23

theorem rels_length : fi23U3Cover3.relCodes.length = 29 := rfl

@[expose] noncomputable def sq (i : Nat) : Bool := codesOneInv lay X [2 * i, 2 * i]

@[expose] noncomputable def rel (j : Nat) : Bool :=
  codesOneInv lay X (fi23U3Cover3.relCodes.getD j [])

#kc_each sq 0 4
#kc_each rel 0 29

#kc_forall_tree sq_all (fun i => sq i = true) 4 CertificateChecks.KernelFi23U3.sq
#kc_forall_tree rel_all (fun j => rel j = true) 29 CertificateChecks.KernelFi23U3.rel

theorem rel_neg : (!codesOneInv lay X ((fi23U3Cover3.relCodes.getD 1 []).drop 1)) = true := by
  quickRfl

theorem one_neg : (!codesOneInv lay X [0]) = true := by quickRfl

end CertificateChecks.KernelFi23U3

end

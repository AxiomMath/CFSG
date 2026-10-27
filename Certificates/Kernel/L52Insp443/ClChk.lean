module

public import Certificates.Kernel.L52Insp443.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I

@[expose] noncomputable def clK (bs S : List Nat) : Bool :=
  allK (fun b => andB (Nat.beq (mmulK b b) idK) (allK (fun s => memK (mmulK b s) S) S)) bs

@[expose] noncomputable def ch725109zc (z : Nat) : Bool := clK (D.zB.getD z []) (D.zS.getD z [])

@[expose] noncomputable def ch725109ac (k : Nat) : Bool :=
  clK ((D.aB.getD (k / 3) []).getD (k % 3) []) ((D.aS.getD (k / 3) []).getD (k % 3) [])

#kc_each ch725109zc 0 7
#kc_each ch725109ac 0 6

theorem ch725109n_cl : notB (clK (D.zB.getD 0 []) (D.zS.getD 1 [])) = true := by
  quickRfl

end CertificateChecks.KernelL52I

end

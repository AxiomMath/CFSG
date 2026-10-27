
module

public import Certificates.Kernel.SporSch.Ru.Q7305K
public import CFSG.Certificates.Kernel.LieCocycle.Fi22.Core
meta import CFSG.Quasithin.Recognition.RuRank3RuGraphDataInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.Q7046F CFSG.Quasithin.RuRank3.ruFGText
#kmisc_hexflat CertificateChecks.KernelSporSch.Q7046F CFSG.Quasithin.RuRank3.ruFGText 3 4060 12 2

namespace CertificateChecks.KernelSporSch.S7046

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KLC.Fi22

@[expose] noncomputable def sOK (G b : Nat) : Bool :=
  bAnd(permOK 4060 12 (mask 12) (4060 * 12) G (pinvS 4060 12 (mask 12) G),
  bAnd(Nat.beq (Nat.shiftRight G (4060 * 12)) 0,
  bAnd(allN 4060 (fun x => Nat.blt (pg 12 (mask 12) G x) 4060),
  bAnd(siftK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) RuJS.LR RuJS.TRI RuJS.BP 4 0 G,
  bAnd(Nat.beq (pg 12 (mask 12) G 0) 0, Nat.beq (pg 12 (mask 12) G b) b)))))

@[expose] noncomputable def eqB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

end CertificateChecks.KernelSporSch.S7046

end

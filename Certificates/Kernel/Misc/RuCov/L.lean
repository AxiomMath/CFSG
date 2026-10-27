module

public import Certificates.Data.Kernel.Misc.RuCov
public import Certificates.Kernel.Misc.RuCov.Data
public import Certificates.Kernel.SporSch.Ru.LChain
import CFSG.Certificates.Kernel.Common.Each

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuCov

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuCov CertificateChecks.KernelSporSch

@[expose] noncomputable def ch7229l_ (q : Nat) : Bool :=
  strictB (roff (nat_lit 4060) (nat_lit 48720) (RuLS.LR 0)) (fun o0 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (RuLS.LR 1)) (fun o1 =>
  strictB (rcnt (RuLS.LR 0)) (fun n0 =>
  strictB (rcnt (RuLS.LR 1)) (fun n1 =>
    chkCov RuLS.LR RuLS.TR WL (HR 1)
      (k3L RuLS.TR o0 o1 n0 n1 (fun r => HR (Nat.add 7 r)) 6) (Nat.mul 4160 q) 4160))))

end CertificateChecks.KernelMisc.RuCov

#kc_each CertificateChecks.KernelMisc.RuCov.ch7229l_ 0 28

end

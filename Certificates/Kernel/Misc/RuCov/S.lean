module

public import Certificates.Data.Kernel.Misc.RuCov
public import Certificates.Kernel.Misc.RuCov.Data
public import Certificates.Kernel.Misc.RuSq.Chain
public import Certificates.Kernel.SporSch.Ru.CData
import CFSG.Certificates.Kernel.Common.Each

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuCov

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuCov CertificateChecks.KernelSporSch
  CertificateChecks.KernelMisc

@[expose] noncomputable def ch7229s_ (q : Nat) : Bool :=
  strictB (roff (nat_lit 4060) (nat_lit 48720) (RuCS.LR 0)) (fun o0 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (RuCS.LR 1)) (fun o1 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (RuCS.LR 2)) (fun o2 =>
  strictB (rcnt (RuCS.LR 0)) (fun n0 =>
  strictB (rcnt (RuCS.LR 1)) (fun n1 =>
  strictB (rcnt (RuCS.LR 2)) (fun n2 =>
    chkCov RuSqS.LR RuSqS.TR WS (HR 0)
      (k3C RuCS.TR o0 o1 o2 n0 n1 n2 (fun r => HR (Nat.add 2 r)) 5) (Nat.mul 1024 q) 1024))))))

end CertificateChecks.KernelMisc.RuCov

#kc_each CertificateChecks.KernelMisc.RuCov.ch7229s_ 0 16

end

module

public import Certificates.Data.Kernel.Misc.RuCoverK
public import Certificates.Kernel.Misc.Coset.RuRhoA.Data
public import Certificates.Kernel.SporSch.Ru.GensData
public import Certificates.Kernel.SporSch.Ru.Text4060
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuCover

#kc_repo #kc_json_gz CertificateChecks.KernelMisc.RuCover
  "Certificates/Kernel/Misc/RuCover/data/Data.json.gz" 1047 10309285999917947214
  (Q0 : List Nat) (Q0I : List Nat) (Q1 : List Nat) (Q1I : List Nat)

open CFSG.KC.MiscCoset.Act CFSG.KC.Misc.RuCover CertificateChecks.KernelSporSch

@[expose] noncomputable def wW (w : List Int) (x : Nat) : Nat :=
  walkW CFSG.KAct.RuRho.A Q0 Q0I Q1 Q1I w x

@[expose] noncomputable def ch7257e (k : Nat) : Bool :=
  eqOK CFSG.KAct.RuRho.A Q0 Q0I Q1 Q1I RuG.A0I (RuT4060.L 0) RuG.A1I (RuT4060.L 1)
    (eqPair k).1 (eqPair k).2

@[expose] noncomputable def ch7257n (c : Nat) : Bool :=
  notB (Nat.beq (wW (etaW c 3) (nat_lit 0)) (wW [1, 1] (nat_lit 0)))

end CertificateChecks.KernelMisc.RuCover

#kc_each CertificateChecks.KernelMisc.RuCover.ch7257e 0 12

#kc_each CertificateChecks.KernelMisc.RuCover.ch7257n 0 8

namespace CertificateChecks.KernelMisc.RuCover

open CFSG.KC.MiscCoset.Act

theorem ch7257z : notB (Nat.beq (wW [1, 1] (nat_lit 0)) (nat_lit 0)) = true := by quickRfl

end CertificateChecks.KernelMisc.RuCover

end

module

public import Certificates.Kernel.Misc.RuScan.Data
public import Certificates.Kernel.SporSch.Ru.Gens
public import CFSG.Quasithin.Vol2.KGFactC31RuData
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Spor.WordAccC
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Misc.RuInv CertificateChecks.KernelSporSch
  CFSG.Quasithin.KGC31.Ru

@[expose] noncomputable def ch7230h_ (i : Nat) : Bool :=
  wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 RuG.A0 RuG.A1) (gen2 RuG.A0I RuG.A1I) 2
    ((hWordsZ ++ hWordsA).getD i []) (HP (Nat.succ i))

theorem ch7230hz : Nat.beq (HP 0) RuG.Z = true := by quickRfl

@[expose] noncomputable def hWC (i : Nat) : Bool :=
  CFSG.KS.Raw.wordEqC 4060 12 (pidn 4060 12) (gen2 RuG.A0 RuG.A1) (gen2 RuG.A0I RuG.A1I) 2
    ((hWordsZ ++ hWordsA).getD i []) (HP (Nat.succ i))

end CertificateChecks.KernelMisc.RuScan

#kc_each CertificateChecks.KernelMisc.RuScan.hWC 0 9

namespace CertificateChecks.KernelMisc.RuScan

theorem ch7230h_0 : ch7230h_ (nat_lit 0) = true :=
  CFSG.KS.Raw.wordEqK_of_C hWC0

theorem ch7230h_1 : ch7230h_ (nat_lit 1) = true :=
  CFSG.KS.Raw.wordEqK_of_C hWC1

theorem ch7230h_2 : ch7230h_ (nat_lit 2) = true :=
  CFSG.KS.Raw.wordEqK_of_C hWC2

theorem ch7230h_3 : ch7230h_ (nat_lit 3) = true :=
  CFSG.KS.Raw.wordEqK_of_C hWC3

theorem ch7230h_4 : ch7230h_ (nat_lit 4) = true :=
  CFSG.KS.Raw.wordEqK_of_C hWC4

theorem ch7230h_5 : ch7230h_ (nat_lit 5) = true :=
  CFSG.KS.Raw.wordEqK_of_C hWC5

theorem ch7230h_6 : ch7230h_ (nat_lit 6) = true :=
  CFSG.KS.Raw.wordEqK_of_C hWC6

theorem ch7230h_7 : ch7230h_ (nat_lit 7) = true :=
  CFSG.KS.Raw.wordEqK_of_C hWC7

theorem ch7230h_8 : ch7230h_ (nat_lit 8) = true :=
  CFSG.KS.Raw.wordEqK_of_C hWC8

end CertificateChecks.KernelMisc.RuScan

end

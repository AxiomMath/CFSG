module

public import Certificates.Kernel.HS100.FiveData
public import Certificates.Data.Kernel.Misc.ArrEnum
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveData
meta import Certificates.Kernel.HS100.FiveData
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelHS100.S5E

meta def gens : List (Array Nat) := CFSG.EvenSporadicStandard.HSStd.s5cGens.toList

meta def keys : List Nat := CertificateChecks.KernelHS100.FiveE.keyOrder gens

end CertificateChecks.KernelHS100.S5E

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelHS100.SC CFSG.EvenSporadicStandard.HSStd.s5cHex
#kmisc_hexflat CertificateChecks.KernelHS100.SC CFSG.EvenSporadicStandard.HSStd.s5cHex 3 100 7 4

#lc_bfs CertificateChecks.KernelHS100.S5 CertificateChecks.KernelHS100.S5E.gens 100 7
#kss_natlist CertificateChecks.KernelHS100.S5.SKT CertificateChecks.KernelHS100.S5E.keys

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def S5.SK : List Nat := (List.range 600).map S5.SKT

@[expose] noncomputable def cm (p q : Nat) : Nat := pcomp 100 7 (mask 7) p q

@[expose] noncomputable def coxK : Bool :=
  (allN 4 fun i => Nat.beq (cm (SC.F i) (SC.F i)) (pidn 100 7)) &&
    (allN 3 fun i => Nat.beq (cm (cm (SC.F i) (SC.F (i + 1))) (SC.F i))
      (cm (cm (SC.F (i + 1)) (SC.F i)) (SC.F (i + 1)))) &&
    (allN 4 fun i => allN 4 fun j => decide (j < i + 2) ||
      Nat.beq (cm (SC.F i) (SC.F j)) (cm (SC.F j) (SC.F i)))

theorem S5.keys : keysSK 100 7 [0, 1, 3, 2, 4, 5] S5.N S5.T S5.SK = true := by quickRfl

theorem S5.gensF : (Nat.beq (S5.G 0) (FV.F 4) &&
    allN 4 fun k => Nat.beq (S5.G (k + 1)) (SC.F k)) = true := by quickRfl

theorem S5.permS : allN 4
    (fun k => permOK 100 7 (mask 7) (100 * 7) (SC.F k) (pinvS 100 7 (mask 7) (SC.F k))) = true := by
  quickRfl

theorem S5.memS : allN 4 (fun k => memK C2.N C2.T (SC.F k)) = true := by quickRfl

theorem S5.cox : coxK = true := by quickRfl

theorem S5.card : Nat.beq S5.N 600 = true := by quickRfl

end CertificateChecks.KernelHS100

end

module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Misc.SignedWordK
public import CFSG.RankThree.PartOne.KS.RuFiveData
meta import CFSG.RankThree.PartOne.KS.RuFiveData
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.RuFive.RG CFSG.RankThree.PartOne.ruFiveHex
#kmisc_hexflat CertificateChecks.KernelMisc.RuFive.RG CFSG.RankThree.PartOne.ruFiveHex 3 4060 12 75

namespace CertificateChecks.KernelMisc.RuFive

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum CFSG.KC.SignedWordK

@[expose] noncomputable def G (k : Nat) : Nat := RG.F (Nat.add k 64)

@[expose] noncomputable def I : Nat := swK 4060 12 G [(2, true)]

@[expose] noncomputable def J : Nat :=
  swK 4060 12 G [(1, true), (2, false), (1, false), (2, false), (1, true), (0, true)]

theorem permG0 : permB 4060 12 (G 0) = true := by quickRfl

theorem permG1 : permB 4060 12 (G 1) = true := by quickRfl

theorem permG2 : permB 4060 12 (G 2) = true := by quickRfl

theorem kI4 : Nat.beq (ppow 4060 12 (mask 12) (pidn 4060 12) I 4) (pidn 4060 12) = true := by
  quickRfl

theorem kI2 : Nat.beq (ppow 4060 12 (mask 12) (pidn 4060 12) I 2) (pidn 4060 12) = false := by
  apply Bool.eq_false_iff.2
  intro h
  have h' : (!Nat.beq (ppow 4060 12 (mask 12) (pidn 4060 12) I 2) (pidn 4060 12)) = true := by
    quickRfl
  rw [h] at h'
  exact Bool.false_ne_true h'

theorem kIJ : Nat.beq (ppow 4060 12 (mask 12) (pidn 4060 12) I 2)
    (ppow 4060 12 (mask 12) (pidn 4060 12) J 2) = true := by
  quickRfl

theorem kRel : Nat.beq (pcomp 4060 12 (mask 12) (pcomp 4060 12 (mask 12) J I)
    (pinvS 4060 12 (mask 12) J)) (pinvS 4060 12 (mask 12) I) = true := by
  quickRfl

theorem negRel : (!Nat.beq (pcomp 4060 12 (mask 12) (pcomp 4060 12 (mask 12) I I)
    (pinvS 4060 12 (mask 12) I)) (pinvS 4060 12 (mask 12) I)) = true := by
  quickRfl

end CertificateChecks.KernelMisc.RuFive

end

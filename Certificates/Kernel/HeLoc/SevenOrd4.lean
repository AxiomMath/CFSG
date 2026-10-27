module

public import Certificates.Kernel.HeLoc.SevenDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.SporSch.PairHeCnt

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS

theorem ord4 :
    Nat.beq (ppow 8330 14 (mask 14) (pidn 8330 14) (A 67) 4) (pidn 8330 14) = true := by
  quickRfl

theorem ord2 :
    Nat.beq (ppow 8330 14 (mask 14) (pidn 8330 14) (A 67) 2) (pidn 8330 14) = false := by
  apply Bool.eq_false_iff.2
  intro h
  have h' : (!Nat.beq (ppow 8330 14 (mask 14) (pidn 8330 14) (A 67) 2) (pidn 8330 14)) = true := by
    quickRfl
  rw [h] at h'
  exact Bool.false_ne_true h'

end CertificateChecks.KernelHeLoc.Seven

end

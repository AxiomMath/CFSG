module

public import Certificates.Kernel.Misc.Perm.J2C3D
public import Certificates.Data.Kernel.Misc.ConjWit
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VJ2OverInputs
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
meta import CFSG.RankThree.PartTwo.Sec4.Ronan148VJ2OverInputs

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelMisc.Over148004 "Certificates/Kernel/Misc/Perm/data/over148004.json.gz" 9590 6140142810791047752
  (TR : List Nat) (W : List Nat)

#kmisc_packarrs CertificateChecks.KernelMisc.Over148004.MA
  CFSG.RankThree.PartTwo.Sec4.Ronan148V.mArrs 9

public section

namespace CertificateChecks.KernelMisc.Over148004

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ConjWit
open CertificateChecks.KernelMisc.J2C3
open CFSG.RankThree.PartTwo.Sec4.Ronan148V

@[expose] noncomputable def TT (r : ℕ) : ℕ := lget TR r

@[expose] noncomputable def SC (r h : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (MA r) (GC 1) (Nat.beq h 1))
    (GC 0) (Nat.beq h 0)

@[expose] noncomputable def SIC (r h : ℕ) : ℕ := pinvS 315 9 (mask 9) (SC r h)

@[expose] noncomputable def wordsK (r : ℕ) : Bool :=
  Nat.beq (wordK 315 9 (mask 9) (pidn 315 9) (SC r) (SIC r) wordsA[r]!) (AB 0) &&
    Nat.beq (wordK 315 9 (mask 9) (pidn 315 9) (SC r) (SIC r) wordsB[r]!) (AB 1)

theorem wlen : W.length = 560 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem cov : witL 315 9 16384 2048 1080 8 CzP.F TT ZoP.F I Z (cm Z Z) W 0 = true := by
  quickRfl

theorem trK : CFSG.KC.LQT.P.allN 8 (fun r => permB 315 9 (TT r) && cwE 315 9 (MA r) Z (TT r)) =
    true := by
  quickRfl

theorem maK : CFSG.KC.LQT.P.allN 8 (fun r => okK (MA r) && permB 315 9 (MA r)) = true := by
  quickRfl

theorem maA : CFSG.KC.LQT.P.allN 8
    (fun r => CFSG.KC.Misc.ArrEnum.arrBind mArrs[r]! 315 9 (MA r)) = true := by
  quickRfl

theorem wK : CFSG.KC.LQT.P.allN 8 wordsK = true := by
  quickRfl

theorem lK : CFSG.KC.LQT.P.allN 8 (fun r => CFSG.Monster.B.Co2.Native.lettersOK 3 wordsA[r]! &&
    CFSG.Monster.B.Co2.Native.lettersOK 3 wordsB[r]!) = true := by
  quickRfl

theorem sizes : (mArrs.size == 8 && wordsA.size == 8 && wordsB.size == 8) = true := by
  quickRfl

end CertificateChecks.KernelMisc.Over148004

end

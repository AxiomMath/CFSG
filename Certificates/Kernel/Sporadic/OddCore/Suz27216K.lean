module

public import Certificates.Kernel.Sporadic.OddCore.Suz27216D
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Kernel.Sporadic.SuzInv.Full1
public import Certificates.Data.Kernel.Spor.Suz27216
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 200

namespace CertificateChecks.KernelSpor.N27216

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Suz27216 CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.OddCore

@[expose] noncomputable def Gi (j : Nat) : Nat := SuzInvT0.F (Nat.add 32 j)

@[expose] noncomputable def GiI (j : Nat) : Nat := pinvS 1782 11 (mask 11) (Gi j)

@[expose] def F1 : List Nat := [1, 78, 161, 419, 821, 1108, 1217]

@[expose] def F2 : List Nat := [2, 211, 274, 316, 338, 348, 419, 423, 437, 727, 821, 828, 862, 890,
  912, 1108, 1154, 1533, 1543, 1634, 1673, 1770]

@[expose] def W1 : List (List Nat) := [[2, 1, 0], [1, 0, 1], [4, 0, 2]]

@[expose] def W2 : List (List Nat) := [[2, 1, 0], [2, 0, 2]]

@[expose] noncomputable def SV : List Nat :=
  [code3 0 1 2, code3 218 1 211, code3 1047 1217 1154, code3 876 161 1543, code3 619 78 890,
   code3 683 161 274, code3 262 1217 1770, code3 1586 78 348, code3 308 1217 828,
   code3 1532 1 437, code3 1443 161 862, code3 1209 78 316]

theorem k_words : wordsK 1782 11 Gi GiI OW = true := by quickRfl

theorem k_ek : Nat.beq RE.k 4 = true := by quickRfl
theorem k_ecnt : Nat.beq RE.cnt 64 = true := by quickRfl
theorem k_eh : penumHdK (pidn 1782 11) RE.cnt 64 RE.T RE.PL = true := by quickRfl
theorem k_esl : penumSlK 1782 11 (mask 11) (1782 * 11) false RE.G RE.GI RE.k RE.cnt RE.T RE.PL
    RE.POS RE.SRT RE.SRI 0 64 = true := by quickRfl
theorem k_r : rK 1782 11 OW RE.G 64 RE.T = true := by quickRfl

theorem k_h : hK 1782 11 msift (OW 10) (SuzTP 1) OW RE.G GN = true := by quickRfl

theorem k_fix1 : fixOK 1782 11 GN W1 1 F1 = true := by quickRfl
theorem k_fix2 : fixOK 1782 11 GN W2 2 F2 = true := by quickRfl

theorem k_chain : chainK 1782 11 SuzInvF1.LR SuzInvF1.TR = true := by quickRfl

theorem k_cent0 : centK 1782 11 SuzInvF1.LR SuzInvF1.TR SuzInvF1.TRI GN 5 SV F1 F2 0 432 = true := by
  quickRfl
theorem k_cent1 : centK 1782 11 SuzInvF1.LR SuzInvF1.TR SuzInvF1.TRI GN 5 SV F1 F2 432 432 =
    true := by
  quickRfl
theorem k_cent2 : centK 1782 11 SuzInvF1.LR SuzInvF1.TR SuzInvF1.TRI GN 5 SV F1 F2 864 432 =
    true := by
  quickRfl
theorem k_cent3 : centK 1782 11 SuzInvF1.LR SuzInvF1.TR SuzInvF1.TRI GN 5 SV F1 F2 1296 432 =
    true := by
  quickRfl
theorem k_lr0 : Nat.beq (rcnt (SuzInvF1.LR 0)) 1728 = true := by quickRfl

theorem k_surv : survK 1782 11 msift SuzInvF1.LR SuzInvF1.TR SuzInvF1.TRI (SuzTP 1) SV 12 = true := by
  quickRfl

end CertificateChecks.KernelSpor.N27216

end

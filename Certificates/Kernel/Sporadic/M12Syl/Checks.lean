module

public import Certificates.Data.Kernel.Spor.MSylow
public import CFSG.Sporadic.Schreier.MathieuSylowAutM12Derivs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.M12Syl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt CFSG.KS.MSyl CFSG.Sporadic.Schreier

set_option maxRecDepth 100000

@[expose] def I : Nat := 205163983024656
@[expose] def A : Nat := 92532767328531
@[expose] def B : Nat := 180734465348391
@[expose] def Bi : Nat := 82837192188216
@[expose] def Z : Nat := 198556746646131
@[expose] def ZB : Nat := 83035200032871

@[expose] def ES : List (List Int) :=
  [[-2, 4, 3, 7, 6, -9, 10, 10], [2, -9, 3, -11, 8, -10], [-7, 1, 9, 3, 6, 8, 11, 10],
    [2, -9, 3, 9]]

@[expose] def PT : List Nat := [89199016896936, 96937490913591, 91403475503466, 198290160882231]

@[expose] def L0 : List Nat :=
  [205163983024656, 92532767328531, 180734465348391, 82837192188216, 170632702883361,
    100227680373366, 126617155668756, 100615955284761, 63390608590866, 133197198789141,
    128196357267771, 153059824574826]
@[expose] def L1 : List Nat :=
  [205163983024656, 188645501188176, 24779717685936, 80986228089456, 107212948781376,
    204807546824736, 100649489803056, 110649213795216, 47569029192096, 80755671382656,
    167479214749536]
@[expose] def L2 : List Nat :=
  [205163983024656, 188327658087696, 77182615132176, 199592603363856, 196028861469456,
    115690651232016, 148045696824336, 110481644345616, 167912872977936, 128859866704656]
@[expose] def L3 : List Nat :=
  [205163983024656, 165718535651856, 203016183042576, 203728942031376, 179995509363216,
    201645637214736, 181744066327056, 78865151459856, 99537633128976]
@[expose] def L4 : List Nat :=
  [205163983024656, 115129136591376, 77702494630416, 163253510812176, 151008003699216,
    129075471987216, 100371917058576, 184195388879376]

@[expose] noncomputable def cnt (t : Nat) : Nat :=
  pcnt 12 4 (mask 4) (survF 12 4 (mask 4) I A A B ZB m12Derivs ES PT 11 6 3) [[t], L1, L2, L3, L4] I 0

theorem syl : sylowAutP 12 4 (mask 4) I A A B Bi m12Derivs ES Z Z 80 95040 6 = true := by quickRfl

theorem pt : (exprsV 12 4 (mask 4) I (slpP 12 4 (mask 4) I A A B Bi m12Derivs) ES == PT) = true := by
  quickRfl

theorem surv0 : Nat.beq (cnt 205163983024656) 0 = true := by quickRfl
theorem surv1 : Nat.beq (cnt 92532767328531) 0 = true := by quickRfl
theorem surv2 : Nat.beq (cnt 180734465348391) 0 = true := by quickRfl
theorem surv3 : Nat.beq (cnt 82837192188216) 0 = true := by quickRfl
theorem surv4 : Nat.beq (cnt 170632702883361) 0 = true := by quickRfl
theorem surv5 : Nat.beq (cnt 100227680373366) 0 = true := by quickRfl
theorem surv6 : Nat.beq (cnt 126617155668756) 0 = true := by quickRfl
theorem surv7 : Nat.beq (cnt 100615955284761) 0 = true := by quickRfl
theorem surv8 : Nat.beq (cnt 63390608590866) 0 = true := by quickRfl
theorem surv9 : Nat.beq (cnt 133197198789141) 0 = true := by quickRfl
theorem surv10 : Nat.beq (cnt 128196357267771) 0 = true := by quickRfl
theorem surv11 : Nat.beq (cnt 153059824574826) 0 = true := by quickRfl

end CertificateChecks.KernelSpor.M12Syl

end

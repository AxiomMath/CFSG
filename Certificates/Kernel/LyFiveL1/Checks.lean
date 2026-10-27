
module

public import Certificates.Kernel.LyFiveL1.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LyFive

open CFSG.KC.LyFive CFSG.KC.LyOm CFSG.KC.Loop CFSG.KC.LL CFSG.KC.Ord CFSG.KD.LyOm
  CFSG.RankThree.Native
open CertificateChecks.KernelSporSch.LySv (AF AI)

@[expose] noncomputable def R0 : List Nat := ((List.replicate 65 BC.ONEF).set 1 (AF 0)).set 2 (AF 1)

theorem slp : (Nat.beq ((slpF BC R0 lyFiveProg).getD 1 0) (AB.getD 0 0) &&
    Nat.beq ((slpF BC R0 lyFiveProg).getD 2 0) (AB.getD 1 0)) = true := by quickRfl

theorem vld : allL (fVld BC) (LT ++ AB) = true := by quickRfl

theorem inv : (Nat.beq (fMul BC (GA 0) (GA 2)) BC.ONEF && Nat.beq (fMul BC (GA 1) (GA 3)) BC.ONEF)
    = true := by quickRfl

theorem pwA : (Nat.beq (UG 0) (GA 0) && Nat.beq (UG 1) (fMul BC (UG 0) (GA 0)) &&
    Nat.beq (UG 2) (fMul BC (UG 1) (GA 0)) && Nat.beq (UG 3) (fMul BC (UG 2) (GA 0)) &&
    Nat.beq (UG 20) (fMul BC (UG 3) (GA 0)) && Nat.beq (UG 21) (fMul BC (UG 20) (UG 20)) &&
    Nat.beq (UG 22) (fMul BC (UG 21) (UG 20)) && Nat.beq (UG 23) (fMul BC (UG 22) (UG 20))) =
    true := by quickRfl

@[expose] noncomputable def vOK (i : Fin 4) : Bool :=
  Nat.beq (UG (4 + 4 * i.val)) (wordF BC GA ((lyFiveVWords i).map abL)) &&
  Nat.beq (UG (5 + 4 * i.val)) (fMul BC (UG (4 + 4 * i.val)) (UG (4 + 4 * i.val))) &&
  Nat.beq (UG (6 + 4 * i.val)) (fMul BC (UG (5 + 4 * i.val)) (UG (4 + 4 * i.val))) &&
    Nat.beq (UG (7 + 4 * i.val)) (fMul BC (UG (6 + 4 * i.val)) (UG (4 + 4 * i.val)))

theorem pwV0 : vOK 0 = true := by quickRfl
theorem pwV1 : vOK 1 = true := by quickRfl
theorem pwV2 : vOK 2 = true := by quickRfl
theorem pwV3 : vOK 3 = true := by quickRfl

theorem lifts : (Nat.beq (UG 24) (wordF BC GA (TG.getD 0 [])) &&
    Nat.beq (UG 25) (wordF BC GA (TG.getD 1 [])) && Nat.beq (UG 26) (wordF BC GA (TG.getD 2 [])))
    = true := by quickRfl

@[expose] noncomputable def xvOK (i : Nat) : Bool :=
  Nat.beq (fMul BC (UG 20) (UG (4 + 4 * i))) (fMul BC (UG (4 + 4 * i)) (UG 20))

theorem rel : (xvOK 0 && xvOK 1 && xvOK 2 && xvOK 3 &&
    Nat.beq (fMul BC (UG 23) (UG 20)) BC.ONEF &&
      Nat.beq (pow5F BC (fMul BC (UG 4) (UG 8))) BC.ONEF) = true := by quickRfl

@[expose] noncomputable def bridgeOK (j : Nat) : Bool :=
  letB (wordF BC UG (BW.getD j [])) (fun β => Nat.beq (fMul BC β (elF BC UG (RT.getD j 0)))
    (fMul BC (nIf(Nat.beq (BT.getD j 0) 0, UG 20, fMul BC (UG 4) (UG 8))) β))

theorem bridges : (List.range 17).all bridgeOK = true := by quickRfl

theorem pos : posOK TB PB NT = true := by quickRfl

end CFSG.KD.LyFive

end

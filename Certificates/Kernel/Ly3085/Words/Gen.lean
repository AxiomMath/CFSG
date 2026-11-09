module

public import Certificates.Kernel.Ly3085.Omega.Data
public import Certificates.Kernel.SporSch.Ly.BSData
public import Certificates.Kernel.SporSch.Ly.SevA
public import Certificates.Data.Kernel.LyOmega.Words
public import Certificates.Data.GH74.LyGen
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Ly3085.Words.GenRec

#kc_repo #kc_json CFSG.KD.LyOm "Certificates/Kernel/Ly3085/Words/data/genzt.json" 1456
  12184509501438770427 (ztExt : List (List Nat))

public section

namespace CFSG.KD.LyOm

open CFSG.KC.LyOm CFSG.KC.Ord CertificateChecks.KernelSporSch

@[expose] noncomputable def genExt : List (List Int) :=
  (CFSG.Sporadic.Ly.Gen.genWords.toList.take 6) ++ decWords ztExt

@[expose] noncomputable def genVals : List (Nat × Nat) := slpVals BC LyBS.A LyBS.B LyBS.B4 genExt

@[expose] noncomputable def genChecksOf (U Z T : Nat) (V : List (Nat × Nat)) : Bool :=
  (fun U7 => Nat.beq (fPow BC U 21) BC.ONEF && notB (Nat.beq U7 BC.ONEF) &&
    notB (Nat.beq (fPow BC U 3) BC.ONEF) && Nat.beq (fMul BC LyBS.A U) (fMul BC U LyBS.A) &&
    Nat.beq (fMul BC LyBS.A Z) (fMul BC Z LyBS.A) && Nat.beq (fMul BC U7 T) (fMul BC T U7) &&
    Nat.beq (fPow BC Z 22) BC.ONEF && notB (Nat.beq (fPow BC Z 2) BC.ONEF) &&
    Nat.beq (V.getD 8 (0, 0)).1 (LySv.AF 2) && Nat.beq (V.getD 9 (0, 0)).1 (LySv.AF 3) &&
    Nat.beq (V.getD 10 (0, 0)).1 (LySv.AF 4) && Nat.beq (V.getD 11 (0, 0)).1 (LySv.AF 5) &&
    Nat.beq (V.getD 12 (0, 0)).1 (LySv.AF 6))
  (fPow BC U 7)

end CFSG.KD.LyOm

#lyom_genvals CFSG.KD.LyOm.GV

namespace CFSG.KD.LyOm

open CFSG.KC.LyOm CFSG.KC.Ord CertificateChecks.KernelSporSch

theorem gw0 : pairB (wordLanes BC LyBS.A LyBS.B LyBS.B4 (GV.take 0) 0 (genExt.getD 0 []))
    (GV.getD 0 (0, 0)) = true := by quickRfl

theorem gw1 : pairB (wordLanes BC LyBS.A LyBS.B LyBS.B4 (GV.take 1) 1 (genExt.getD 1 []))
    (GV.getD 1 (0, 0)) = true := by quickRfl

theorem gw2 : pairB (wordLanes BC LyBS.A LyBS.B LyBS.B4 (GV.take 2) 2 (genExt.getD 2 []))
    (GV.getD 2 (0, 0)) = true := by quickRfl

theorem gw3 : pairB (wordLanes BC LyBS.A LyBS.B LyBS.B4 (GV.take 3) 3 (genExt.getD 3 []))
    (GV.getD 3 (0, 0)) = true := by quickRfl

theorem gw4 : pairB (wordLanes BC LyBS.A LyBS.B LyBS.B4 (GV.take 4) 4 (genExt.getD 4 []))
    (GV.getD 4 (0, 0)) = true := by quickRfl

theorem gw5 : pairB (wordLanes BC LyBS.A LyBS.B LyBS.B4 (GV.take 5) 5 (genExt.getD 5 []))
    (GV.getD 5 (0, 0)) = true := by quickRfl

theorem gw6 : pairB (wordLanes BC LyBS.A LyBS.B LyBS.B4 (GV.take 6) 6 (genExt.getD 6 []))
    (GV.getD 6 (0, 0)) = true := by quickRfl

theorem gw7 : pairB (wordLanes BC LyBS.A LyBS.B LyBS.B4 (GV.take 7) 7 (genExt.getD 7 []))
    (GV.getD 7 (0, 0)) = true := by quickRfl

theorem gw8 : pairB (wordLanes BC LyBS.A LyBS.B LyBS.B4 (GV.take 8) 8 (genExt.getD 8 []))
    (GV.getD 8 (0, 0)) = true := by quickRfl

theorem gw9 : pairB (wordLanes BC LyBS.A LyBS.B LyBS.B4 (GV.take 9) 9 (genExt.getD 9 []))
    (GV.getD 9 (0, 0)) = true := by quickRfl

theorem gw10 : pairB (wordLanes BC LyBS.A LyBS.B LyBS.B4 (GV.take 10) 10 (genExt.getD 10 []))
    (GV.getD 10 (0, 0)) = true := by quickRfl

theorem gw11 : pairB (wordLanes BC LyBS.A LyBS.B LyBS.B4 (GV.take 11) 11 (genExt.getD 11 []))
    (GV.getD 11 (0, 0)) = true := by quickRfl

theorem gw12 : pairB (wordLanes BC LyBS.A LyBS.B LyBS.B4 (GV.take 12) 12 (genExt.getD 12 []))
    (GV.getD 12 (0, 0)) = true := by quickRfl

theorem gv_len : Nat.beq GV.length genExt.length = true := by quickRfl

theorem genExt_len : Nat.beq genExt.length 13 = true := by quickRfl

theorem genVals_eq : genVals = GV := by
  refine slpVals_of BC LyBS.A LyBS.B LyBS.B4 genExt GV (Nat.eq_of_beq_eq_true gv_len) ?_
  intro j hj
  rw [Nat.eq_of_beq_eq_true genExt_len] at hj
  match j, hj with
  | 0, _ => exact eq_of_pairB gw0
  | 1, _ => exact eq_of_pairB gw1
  | 2, _ => exact eq_of_pairB gw2
  | 3, _ => exact eq_of_pairB gw3
  | 4, _ => exact eq_of_pairB gw4
  | 5, _ => exact eq_of_pairB gw5
  | 6, _ => exact eq_of_pairB gw6
  | 7, _ => exact eq_of_pairB gw7
  | 8, _ => exact eq_of_pairB gw8
  | 9, _ => exact eq_of_pairB gw9
  | 10, _ => exact eq_of_pairB gw10
  | 11, _ => exact eq_of_pairB gw11
  | 12, _ => exact eq_of_pairB gw12
  | n + 13, h => exact absurd h (by omega)

theorem gen_checks : genChecksOf (genVals.getD 2 (0, 0)).1 (genVals.getD 4 (0, 0)).1
    (genVals.getD 5 (0, 0)).1 genVals = true := by
  rw [genVals_eq]
  quickRfl

theorem neg_z11 : notB (Nat.beq (fPow BC (genVals.getD 4 (0, 0)).1 11) BC.ONEF) = true := by
  rw [genVals_eq]
  quickRfl

theorem neg_a3 : notB (Nat.beq (genVals.getD 8 (0, 0)).1 (LySv.AF 3)) = true := by
  rw [genVals_eq]
  quickRfl

end CFSG.KD.LyOm

end

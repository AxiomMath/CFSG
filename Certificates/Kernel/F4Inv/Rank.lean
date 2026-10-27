module

public import Certificates.Data.Kernel.F4Rank
public import Certificates.Data.Kernel.F4Syl3PhiInv
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.F4Inv "Certificates/Kernel/F4Inv/data/rank.json.gz" 2182
  159259345398260215 (u26 : Nat) (kT : List Nat) (kU : List Nat) (kTU : List Nat)
  (iV : List Nat) (kRA : List Nat) (kRB : List Nat) (iZ : List Nat) (kRAU : List Nat)
  (iRBU : List Nat)

namespace CFSG.KD.F4Inv

open CFSG.KC.F4Rank CFSG.KC.F4Syl3 CFSG.LieType.Simplicity.TitsBits CFSG.RankThree.PartOne.SEITZX

@[expose] def zBits : Nat :=
  mul (mul (mul (sBits 0) (sBits 0)) (mul (sBits 1) (sBits 1))) (mul (sBits 2) (sBits 2))

theorem kT_ok : fixChk (invT 0) kT = true := by decide +kernel

theorem kU_ok : fixChk (invT 1) kU = true := by decide +kernel

theorem kTU_ok : fixChk (invT 2) kTU = true := by decide +kernel

theorem iV_ok : rankChk (invT 3) iV = true := by decide +kernel

theorem kRA_ok : fixChk (sBits 3) kRA = true := by decide +kernel

theorem kRB_ok : fixChk rBBits kRB = true := by decide +kernel

theorem iZ_ok : rankChk zBits iZ = true := by decide +kernel

theorem kRAU_ok : fixSubChk u26 (sBits 3) kRAU = true := by decide +kernel

theorem iRBU_ok : rankSubChk u26 rBBits iRBU = true := by decide +kernel

theorem stab_ok : allN 8 (fun c => stabChk u26 (letterOfCode c).bits) = true := by decide +kernel

theorem kT_neg : fixChk (invT 0) (kT ++ [kT.getD 0 0]) = false := by decide +kernel

theorem kTU_neg : fixChk (invT 2) kT = false := by decide +kernel

theorem iV_neg : rankChk (invT 3) (iV ++ [iV.getD 0 0]) = false := by decide +kernel

theorem iRBU_neg : rankSubChk u26 rBBits iV = false := by decide +kernel

theorem stab_neg : allN 8 (fun c => stabChk (u26 ^^^ 4) (letterOfCode c).bits) = false := by
  decide +kernel

end CFSG.KD.F4Inv

end

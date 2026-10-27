module

public import Certificates.Kernel.Ly3085.Omega.Data
public import Certificates.Kernel.SporSch.Ly.BSData
public import Certificates.Kernel.SporSch.Ly.SevA
public import Certificates.Data.Kernel.LyOmega.Words
public import Certificates.Data.GH74.LyGen
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.LyOm "Certificates/Kernel/Ly3085/Words/data/genzt.json.gz" 1456
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

theorem gen_checks : genChecksOf (genVals.getD 2 (0, 0)).1 (genVals.getD 4 (0, 0)).1
    (genVals.getD 5 (0, 0)).1 genVals = true := by quickRfl

theorem neg_z11 : notB (Nat.beq (fPow BC (genVals.getD 4 (0, 0)).1 11) BC.ONEF) = true := by
  quickRfl

theorem neg_a3 : notB (Nat.beq (genVals.getD 8 (0, 0)).1 (LySv.AF 3)) = true := by quickRfl

end CFSG.KD.LyOm

end

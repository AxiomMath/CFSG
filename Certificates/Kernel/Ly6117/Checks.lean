module

public import Certificates.Kernel.Ly6117.Data
public import Certificates.Kernel.SporSch.Ly.BSData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLitToList

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLy6117

open CFSG.KD.Ly6117 CFSG.KD.LyS0 CFSG.KS.SporSch.LyM CertificateChecks.KernelLyE81
open CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.KC.StrLitToList

theorem v0 : vld (GD 0) = true := by quickRfl

theorem v1 : vld (GD 1) = true := by quickRfl

theorem v2 : vld (GD 2) = true := by quickRfl

theorem v3 : vld (GD 3) = true := by quickRfl

theorem v4 : vld (GD 4) = true := by quickRfl

theorem payK : Nat.beq (payRunP 5 111 12 1332 LyK.chars 0 0 0) (GD 3) = true := by quickRfl

theorem dd : Nat.beq (mul D D) (GD 4) = true := by quickRfl

theorem wa : Nat.beq (wordK CDx CDIx aWord) (GD 0) = true := by
  simp only [aWord, parseWord, strLitToList]
  quickRfl

theorem wb : Nat.beq (wordK CDx CDIx bWord) (GD 1) = true := by
  simp only [bWord, parseWord, strLitToList]
  quickRfl

theorem we : Nat.beq (wordK CDx CDIx eWord) (GD 2) = true := by
  simp only [eWord, parseWord, strLitToList]
  quickRfl

theorem inv : (List.finRange 6).all (fun i => Nat.beq (mul (G i.val) (GI i.val))
    CFSG.KD.OrdLy.ONE) = true := by quickRfl

theorem wA : Nat.beq (wordK G GI wordA) CertificateChecks.KernelSporSch.LyBS.A = true := by
  simp only [wordA, parseWord, strLitToList]
  quickRfl

theorem wB : Nat.beq (wordK G GI wordB) CertificateChecks.KernelSporSch.LyBS.B = true := by
  simp only [wordB, parseWord, strLitToList]
  quickRfl

end CertificateChecks.KernelLy6117

end

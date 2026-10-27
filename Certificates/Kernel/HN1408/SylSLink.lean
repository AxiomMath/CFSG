module

public import Certificates.Kernel.HN1408.SylSFam
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.BaseMask

@[expose] noncomputable def famGenOK (k : Nat) : Bool :=
  allN (famCnt k) (fun h => allN k (fun j =>
    strictB (r32 SylS.FG (Nat.add (Nat.add (famGOff k) (Nat.mul h k)) j)) (fun t =>
      bAnd(Nat.blt t nGD, Nat.beq (r32 SylS.GD t)
        (r32 SylS.FM (Nat.add (Nat.add (famOff k) (Nat.mul h (Nat.shiftLeft 1 k)))
          (Nat.shiftLeft 1 j)))))))

theorem fam_gen : allN 5 (fun d => famGenOK (Nat.add d 2)) = true := by quickRfl

theorem fam_gen_neg : (!allN 2 (fun j => strictB (r32 SylS.FG j) (fun t =>
    Nat.beq (r32 SylS.GD t) (r32 SylS.FM (Nat.add (Nat.shiftLeft 1 j) 1))))) = true := by
  quickRfl

theorem sylS_cent : allN 2048 (fun i =>
    bAnd(commKeyK 11 (mask 11) 2 0 SylS.T (r32 SylS.FM 1) i,
      commKeyK 11 (mask 11) 2 0 SylS.T (r32 SylS.FM 2) i)) = true := by
  quickRfl

theorem sylS_cent_neg : (!allN 2048 (fun i => allN nIV (fun t =>
    commKeyK 11 (mask 11) 2 0 SylS.T (r32 SylS.IV t) i))) = true := by
  quickRfl

end CFSG.KD.HN1408

end

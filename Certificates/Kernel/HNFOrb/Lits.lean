module

public import Certificates.Kernel.HNFOrb.Data
public import Certificates.Kernel.HNFWords.Lits
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFConst
public import CFSG.Certificates.Kernel.HNF26720Sound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNFOrb

open CFSG.EvenSporadicStandard.Solomon78 CFSG.KD.HNF26729 CFSG.KC.HNF26720

#kc_natval BT1 := wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
  CFSG.KD.FamHNSeed.ONE (hnfRepWords[1]! ++ 1 :: invW hnfRepWords[1]!)

theorem BT1_eq : wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE (hnfRepWords[1]! ++ 1 :: invW hnfRepWords[1]!) = BT1 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

#kc_natval BT2 := wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
  CFSG.KD.FamHNSeed.ONE (hnfRepWords[2]! ++ 1 :: invW hnfRepWords[2]!)

theorem BT2_eq : wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE (hnfRepWords[2]! ++ 1 :: invW hnfRepWords[2]!) = BT2 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

#kc_natval BT3 := wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
  CFSG.KD.FamHNSeed.ONE (hnfRepWords[3]! ++ 1 :: invW hnfRepWords[3]!)

theorem BT3_eq : wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE (hnfRepWords[3]! ++ 1 :: invW hnfRepWords[3]!) = BT3 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

@[expose] noncomputable def chunkL (bt u : Nat) (ms K : List Nat) : Bool :=
  CFSG.KC.Ord.andB (vldV u)
    (CFSG.KC.HNFOrb.walk mul vec bt CFSG.KD.FamHNSeed.ONE u
      [(HNFWords.G1, HNFWords.G1i), (HNFWords.G2, HNFWords.G2i),
        (CFSG.KD.FamHNSeed.RW 1, CFSG.KD.FamHNSeed.RW 1)] ms [] K)

theorem chunkW_eq {i bt : Nat} (h : wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE (hnfRepWords[i]! ++ 1 :: invW hnfRepWords[i]!) = bt) (u : Nat)
    (ms K : List Nat) : chunkW hnfW1 hnfW2 hnfRepWords[i]! u ms K = chunkL bt u ms K := by
  unfold chunkW CFSG.KC.HNFOrb.chunk
  simp only [CFSG.KS.HNF26720.strictB_eq]
  rw [HNFWords.G1_eq, HNFWords.G1i_eq, HNFWords.G2_eq, HNFWords.G2i_eq, h]
  rfl

end CFSG.KD.HNFOrb

end

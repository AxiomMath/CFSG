module

public import Certificates.Kernel.HNFO4.Data
public import Certificates.Kernel.HNFWords.Lits
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFConst
public import CFSG.Certificates.Kernel.HNFFibSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.HNFO4

open CFSG.EvenSporadicStandard.Solomon78 CFSG.KD.HNF26729 CFSG.KC.HNF26720 CFSG.KC.HNF26729
  CFSG.KC.HNFFib

#kc_natval BT := wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
  CFSG.KD.FamHNSeed.ONE (hnfRepWords[4]! ++ 1 :: invW hnfRepWords[4]!)

theorem BT_eq : wprod mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE (hnfRepWords[4]! ++ 1 :: invW hnfRepWords[4]!) = BT :=
  Nat.eq_of_beq_eq_true (by quickRfl)

@[expose] noncomputable def RL : Int → Nat :=
  ltr3 (CFSG.KD.FamHNSeed.RW 1) HNFWords.G1 HNFWords.G1i HNFWords.G2 HNFWords.G2i

@[expose] noncomputable def LL : List (Nat × Nat) :=
  us.map fun s =>
    (wgoR mul RL (decW s) CFSG.KD.FamHNSeed.ONE, wgoR mul RL (invW (decW s)) CFSG.KD.FamHNSeed.ONE)

@[expose] noncomputable def chkL (i : Nat) : Bool :=
  CFSG.KC.Ord.andB (okWs us) (CFSG.KC.Ord.andB (vldV u)
    (CFSG.KC.HNFDfs.walk mul vec u BT CFSG.KD.FamHNSeed.ONE LL (CFSG.KC.HNFDfs.getC codes i) []))

theorem chkW_eq (i : Nat) : chkW hnfW1 hnfW2 hnfRepWords[4]! i = chkL i := by
  unfold chkW CFSG.KC.HNFDfs.chunk
  simp only [CFSG.KS.HNF26720.strictB_eq, CFSG.KS.HNFFib.regs_eq]
  rw [HNFWords.G1_eq, HNFWords.G1i_eq, HNFWords.G2_eq, HNFWords.G2i_eq, BT_eq]
  rfl

end CFSG.KD.HNFO4

end

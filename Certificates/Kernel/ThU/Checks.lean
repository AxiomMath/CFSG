module

public import Certificates.Data.Kernel.ThU.Defs
public import Certificates.Kernel.ThU.Data
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3DataTh
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

set_option maxRecDepth 100000

namespace CFSG.KD.ThU

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThU
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

@[expose] noncomputable def blockAt (b : Nat) : Bool :=
  andB (Nat.beq (bitsN BL (10 * b) 5) (blocks.getD b (0, 0, 0, 0)).2.1)
    (andB (Nat.beq (bitsN BL (10 * b + 5) 5) (blocks.getD b (0, 0, 0, 0)).2.2.1)
      (blockB RB (PT (blocks.getD b (0, 0, 0, 0)).1) CFSG.KD.ThS.rm PR 12
        (blocks.getD b (0, 0, 0, 0)).2.1 (blocks.getD b (0, 0, 0, 0)).2.2.1
        (blocks.getD b (0, 0, 0, 0)).2.2.2 (TC b) (SC b)))

theorem chk_s1 : Nat.beq (runSlp RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE slp1.c0 3) n1 =
    true := by quickRfl

theorem chk_s2 : Nat.beq (runSlp RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE slp2.c0 n1)
    nend = true := by quickRfl

theorem chk_n : andB (Nat.blt 3 n1) (andB (Nat.blt 0 nend) (Nat.blt nend 2048)) = true := by
  quickRfl

theorem chk_A : Nat.beq (RB 1) CFSG.KD.ThSeed.SA = true := by quickRfl

theorem chk_B : Nat.beq (RB 2) CFSG.KD.ThSeed.SB = true := by quickRfl

theorem chk_gr : regsIn GR 3 n1 = true := by quickRfl

theorem chk_M : Nat.beq M (gmask3 GR) = true := by quickRfl

theorem chk_mk : allMarked PR 12 (runMarked slp2.c0 (n1 + 2048 * M) / 2048) = true := by quickRfl

theorem chk_rels :
    thULocal3.rels.all (relOKR RB CFSG.KD.ThS.c CFSG.KD.ThS.rm CFSG.KD.ThS.ONE GR) = true := by
  quickRfl

theorem chk_sq : (List.range 3).all (fun i => Nat.beq
    (mulB CFSG.KD.ThS.c CFSG.KD.ThS.rm (RB (regAt GR i)) (RB (regAt GR i))) CFSG.KD.ThS.ONE) =
    true := by quickRfl

theorem chk_blocks : (List.range 9).all blockAt = true := by quickRfl

end CFSG.KD.ThU

end

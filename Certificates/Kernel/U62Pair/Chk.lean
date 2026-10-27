module

public import Certificates.Data.Kernel.U62.Pair
public import Certificates.Kernel.U62Pair.Data
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU62Words
import CFSG.Certificates.Kernel.BabyMonster.Load

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU62P

open CFSG.KC.U62P CFSG.ComponentClassification.RankTwoHypIICover.U62

@[expose] noncomputable def SWN : List (List Nat) := u62SbWords.map (List.map fun z => z.natAbs - 1)

@[expose] noncomputable def RWN : List (List Nat) := u62RWords.map (List.map fun z => z.natAbs - 1)

@[expose] noncomputable def WT0 : WTab :=
  ⟨D.PV, D.G1, D.G2, D.GG, D.NG, D.GL, D.GT, D.NE, D.NS, D.NC, D.WM, D.WS, D.WC⟩

@[expose] noncomputable def ET0 : ETab := ⟨WT0, D.LV, D.RV, D.EI, D.ES, D.EC, D.WJ⟩

@[expose] noncomputable def gen : Nat → Bool := genAt D.TV D.GV SWN

@[expose] noncomputable def rep : Nat → Bool := repAt D.GV D.RV RWN

@[expose] noncomputable def lst (i : Nat) : Bool :=
  bAnd(treeAt D.GV D.LV D.PT D.LB i, bAnd(sortAt D.LV D.SO 32768 i,
    bAnd(phiAt D.LV D.UP D.XP D.NXP i, scanAt D.LV D.PO D.EI D.NO i)))

@[expose] noncomputable def nrm : Nat → Bool := normAt D.GV D.LV D.NI 32768

@[expose] noncomputable def fix : Nat → Bool := fixAt D.GV D.UP

@[expose] noncomputable def pool : Nat → Bool := poolAt D.PV

@[expose] noncomputable def rec : Nat → Bool := recAt D.PV D.NP D.G1 D.G2 D.GG

@[expose] noncomputable def ent : Nat → Bool := entAt ET0

end CertificateChecks.KernelU62P

#bm_bool CertificateChecks.KernelU62P kNO (Nat.beq D.NO 512)
#bm_bool CertificateChecks.KernelU62P kNG (Nat.beq D.NG 896)
#bm_bool CertificateChecks.KernelU62P kNP (Nat.beq D.NP 1771)
#bm_bool CertificateChecks.KernelU62P kGen (CFSG.KC.Enum.allBlk 0 gen 13)
#bm_bool CertificateChecks.KernelU62P kRep (CFSG.KC.Enum.allBlk 0 rep 43)
#bm_bool CertificateChecks.KernelU62P kNorm (CFSG.KC.Enum.allBlk 0 nrm 13)
#bm_bool CertificateChecks.KernelU62P kFix (CFSG.KC.Enum.allBlk 0 fix 693)
#bm_bool CertificateChecks.KernelU62P kLst_0 (CFSG.KC.Enum.allBlk 0 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_1 (CFSG.KC.Enum.allBlk 2048 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_2 (CFSG.KC.Enum.allBlk 4096 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_3 (CFSG.KC.Enum.allBlk 6144 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_4 (CFSG.KC.Enum.allBlk 8192 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_5 (CFSG.KC.Enum.allBlk 10240 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_6 (CFSG.KC.Enum.allBlk 12288 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_7 (CFSG.KC.Enum.allBlk 14336 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_8 (CFSG.KC.Enum.allBlk 16384 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_9 (CFSG.KC.Enum.allBlk 18432 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_10 (CFSG.KC.Enum.allBlk 20480 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_11 (CFSG.KC.Enum.allBlk 22528 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_12 (CFSG.KC.Enum.allBlk 24576 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_13 (CFSG.KC.Enum.allBlk 26624 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_14 (CFSG.KC.Enum.allBlk 28672 lst 2048)
#bm_bool CertificateChecks.KernelU62P kLst_15 (CFSG.KC.Enum.allBlk 30720 lst 2048)
#bm_bool CertificateChecks.KernelU62P kPool_0 (CFSG.KC.Enum.allBlk 0 pool 256)
#bm_bool CertificateChecks.KernelU62P kPool_1 (CFSG.KC.Enum.allBlk 256 pool 256)
#bm_bool CertificateChecks.KernelU62P kPool_2 (CFSG.KC.Enum.allBlk 512 pool 256)
#bm_bool CertificateChecks.KernelU62P kPool_3 (CFSG.KC.Enum.allBlk 768 pool 256)
#bm_bool CertificateChecks.KernelU62P kPool_4 (CFSG.KC.Enum.allBlk 1024 pool 256)
#bm_bool CertificateChecks.KernelU62P kPool_5 (CFSG.KC.Enum.allBlk 1280 pool 256)
#bm_bool CertificateChecks.KernelU62P kPool_6 (CFSG.KC.Enum.allBlk 1536 pool 235)
#bm_bool CertificateChecks.KernelU62P kRec_0 (CFSG.KC.Enum.allBlk 0 rec 448)
#bm_bool CertificateChecks.KernelU62P kRec_1 (CFSG.KC.Enum.allBlk 448 rec 448)
#bm_bool CertificateChecks.KernelU62P kEnt_0 (CFSG.KC.Enum.allBlk 0 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_1 (CFSG.KC.Enum.allBlk 32 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_2 (CFSG.KC.Enum.allBlk 64 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_3 (CFSG.KC.Enum.allBlk 96 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_4 (CFSG.KC.Enum.allBlk 128 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_5 (CFSG.KC.Enum.allBlk 160 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_6 (CFSG.KC.Enum.allBlk 192 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_7 (CFSG.KC.Enum.allBlk 224 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_8 (CFSG.KC.Enum.allBlk 256 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_9 (CFSG.KC.Enum.allBlk 288 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_10 (CFSG.KC.Enum.allBlk 320 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_11 (CFSG.KC.Enum.allBlk 352 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_12 (CFSG.KC.Enum.allBlk 384 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_13 (CFSG.KC.Enum.allBlk 416 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_14 (CFSG.KC.Enum.allBlk 448 ent 32)
#bm_bool CertificateChecks.KernelU62P kEnt_15 (CFSG.KC.Enum.allBlk 480 ent 32)

end

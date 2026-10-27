module

public import Certificates.Data.Kernel.G24LinQ
public import Certificates.Kernel.G24Lin.Rec
import CFSG.Certificates.Kernel.Common.Harness
meta import Certificates.Kernel.Misc.Perm.CharsCatList
import Certificates.Kernel.Misc.Perm.CharsCatList

public section

open CFSG.Quasithin.St84.G24LE CFSG.Quasithin.St84.G24MF
open CFSG.Quasithin.H.Q13 (om)

#ks_chars_cat_list CFSG.KD.G24Lin.pq1 CFSG.Quasithin.St84.G24LE.pQuad1
#ks_chars_cat_list CFSG.KD.G24Lin.yq1 CFSG.Quasithin.St84.G24LE.yQuad1
#ks_chars_cat_list CFSG.KD.G24Lin.pq2 CFSG.Quasithin.St84.G24LE.pQuad2
#ks_chars_cat_list CFSG.KD.G24Lin.yq2 CFSG.Quasithin.St84.G24LE.yQuad2
#ks_chars_cat_list CFSG.KD.G24Lin.pcm CFSG.Quasithin.St84.G24LE.pComm
#ks_chars_cat_list CFSG.KD.G24Lin.ycm CFSG.Quasithin.St84.G24LE.yComm
#ks_chars_cat_list CFSG.KD.G24Lin.pe2 CFSG.Quasithin.St84.G24LE.pExt2
#ks_chars_cat_list CFSG.KD.G24Lin.ye2 CFSG.Quasithin.St84.G24LE.yExt2

namespace CFSG.KD.G24Lin

theorem lin733012_q1 : spanK DQ1 2 72 216 = true := by quickRfl

theorem lin733012_q2 : spanK DQ2 2 84 252 = true := by quickRfl

theorem lin733012_c : spanK DC 2 16 32 = true := by quickRfl

theorem lin733012_e : spanK DE 10 24 48 = true := by quickRfl

theorem lin733012_m1 : pinM (quadRows 8 2) (quadCols 8 2)
    (fun r u => zB (entryB (CQ1 0) (CQ1 1) (CQ1 2) r u)) quadRowKey quadColKey (2 + (72 + 72))
    DQ1 = true := by quickRfl

theorem lin733012_m2 : pinM (quadRows 6 4) (quadCols 6 4)
    (fun r u => zB (entryB (CQ2 0) (CQ2 1) (CQ2 2) r u)) quadRowKey quadColKey (2 + (84 + 84))
    DQ2 = true := by quickRfl

theorem lin733012_mc : pinM commRows commCols commM commRowKey commColKey (2 + (16 + 16)) DC =
    true := by quickRfl

theorem lin733012_me : pinM ext2Rows ext2Cols ext2M ext2RowKey ext2ColKey (10 + (24 + 24)) DE =
    true := by quickRfl

theorem lin733012_k1 : pinM (quadCols 8 2) (List.finRange 2) (quadK sqV1 cmV1 om) quadColKey
    (fun κ => κ.val) 2 DQ1 = true := by quickRfl

theorem lin733012_k2 : pinM (quadCols 6 4) (List.finRange 2) (quadK sqV2 cmV2 omegaN) quadColKey
    (fun κ => κ.val) 2 DQ2 = true := by quickRfl

theorem lin733012_kc : pinM commCols (List.finRange 2) commK commColKey (fun κ => κ.val) 2 DC =
    true := by quickRfl

theorem lin733012_ke : pinM ext2Cols ext2KList ext2K ext2ColKey ext2KKey 10 DE = true := by
  quickRfl

@[expose] def gjList (n : ℕ) : List (Fin 3 × Fin n) :=
  (List.finRange 3).flatMap fun g => (List.finRange n).map fun j => (g, j)

theorem lin733012_r1 : pinM (gjList 8) (List.finRange 8) (fun p i => matV1 p.1 i p.2)
    (fun p => p.1.val * 8 + p.2.val) (fun i => i.val) 0 (laneK (CQ1 0)) = true := by quickRfl

theorem lin733012_s1 : pinM (gjList 2) (List.finRange 2) (fun p s => matZ1 p.1 p.2 s)
    (fun p => p.1.val * 2 + p.2.val) (fun s => s.val) 0 (laneK (CQ1 1)) = true := by quickRfl

theorem lin733012_t1 : pinM (monoList 8) (List.finRange 8) (fun μ i => testVec μ i) monoKey
    (fun i => i.val) 0 (laneK (CQ1 2)) = true := by quickRfl

theorem lin733012_r2 : pinM (gjList 6) (List.finRange 6) (fun p i => matV2 p.1 i p.2)
    (fun p => p.1.val * 6 + p.2.val) (fun i => i.val) 0 (laneK (CQ2 0)) = true := by quickRfl

theorem lin733012_s2 : pinM (gjList 4) (List.finRange 4) (fun p s => matZ2 p.1 p.2 s)
    (fun p => p.1.val * 4 + p.2.val) (fun s => s.val) 0 (laneK (CQ2 1)) = true := by quickRfl

theorem lin733012_t2 : pinM (monoList 6) (List.finRange 6) (fun μ i => testVec μ i) monoKey
    (fun i => i.val) 0 (laneK (CQ2 2)) = true := by quickRfl

theorem lin733012_p1 : (rowsK DQ1 0 pq1.chars && rowsK DQ1 (2 + 72) yq1.chars) = true := by
  quickRfl

theorem lin733012_p2 : (rowsK DQ2 0 pq2.chars && rowsK DQ2 (2 + 84) yq2.chars) = true := by
  quickRfl

theorem lin733012_pc : (rowsK DC 0 pcm.chars && rowsK DC (2 + 16) ycm.chars) = true := by
  quickRfl

theorem lin733012_pe : (rowsK DE 0 pe2.chars && rowsK DE (10 + 24) ye2.chars) = true := by
  quickRfl

@[expose] noncomputable def flipK (D : Nat → Nat) (i b : Nat) (j : Nat) : Nat :=
  cond (Nat.beq j i) (Nat.xor (D j) (Nat.shiftLeft 1 b)) (D j)

theorem lin733012_negM : (!spanK (flipK DQ1 (2 + 144 + 3) 0) 2 72 216) = true := by quickRfl

theorem lin733012_negP : (!spanK (flipK DC 0 0) 2 16 32) = true := by quickRfl

theorem lin733012_negK : (!spanK (flipK DE (10 + 5) 0) 10 24 48) = true := by quickRfl

end CFSG.KD.G24Lin

end

module

public import Certificates.Kernel.MonsterB.Coset3023Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Coset3023

open CFSG.KLie.CT CFSG.KC.KDense CFSG.KC.SortTree CFSG.Monster.B CFSG.Monster.B.TwoA.Census

set_option maxRecDepth 100000

theorem th_ok : thOK = true := by quickRfl

theorem pp_1 : ∀ i < 24, pe (PP 1) i = (cosetArr 1)[i]! := by decide +kernel
theorem pp_2 : ∀ i < 24, pe (PP 2) i = (cosetArr 2)[i]! := by decide +kernel
theorem pp_6 : ∀ i < 24, pe (PP 6) i = (cosetArr 6)[i]! := by decide +kernel

theorem bt_1 : betaTabT (PP 1) = 0 := by decide +kernel
theorem bt_2 : betaTabT (PP 2) = 0 := by decide +kernel
theorem bt_6 : betaTabT (PP 6) = 79873156457113056204225129793389314108 := by decide +kernel

theorem e_ok : cosetA 1 = 3 ∧ cosetA 2 = 734 ∧ cosetA 6 = 374 := by decide +kernel

theorem pe_ok : Model.pN 3 = false ∧ Model.pN 734 = true ∧ Model.pN 374 = true := by decide +kernel

theorem w_ok : wP 1 = (false, 0, 0) ∧ wP 2 = (true, 63, 0) ∧ wP 6 = (true, 0, 0) := by decide +kernel

theorem ta_1 : tabA T1 3 false (PP 1) 0 = true := by quickRfl
theorem td_1 : tabD T1 3 false (PP 1) 0 = true := by quickRfl
theorem ta_2 : tabA T2 734 true (PP 2) 0 = true := by quickRfl
theorem td_2 : tabD T2 734 true (PP 2) 0 = true := by quickRfl
theorem ta_6 : tabA T6 374 true (PP 6) 79873156457113056204225129793389314108 = true := by quickRfl
theorem td_6 : tabD T6 374 true (PP 6) 79873156457113056204225129793389314108 = true := by quickRfl

theorem sort_1 : sortOK T1 J1 = true := by quickRfl
theorem blk_1_0 : blocksOK T1 (false, 0, 0) J1 0 2048 = true := by quickRfl
theorem blk_1_1 : blocksOK T1 (false, 0, 0) J1 2048 2048 = true := by quickRfl
theorem part_1_0 : partOK T1 (false, 0, 0) J1 0 20480 = true := by quickRfl
theorem part_1_1 : partOK T1 (false, 0, 0) J1 1 0 = true := by quickRfl
theorem part_1_2 : partOK T1 (false, 0, 0) J1 2 16384 = true := by quickRfl
theorem part_1_3 : partOK T1 (false, 0, 0) J1 3 0 = true := by quickRfl
theorem part_1_4 : partOK T1 (false, 0, 0) J1 4 16384 = true := by quickRfl
theorem part_1_5 : partOK T1 (false, 0, 0) J1 5 0 = true := by quickRfl
theorem part_1_6 : partOK T1 (false, 0, 0) J1 6 16384 = true := by quickRfl
theorem part_1_7 : partOK T1 (false, 0, 0) J1 7 0 = true := by quickRfl

theorem sort_2 : sortOK T2 J2 = true := by quickRfl
theorem blk_2_0 : blocksOK T2 (true, 63, 0) J2 0 2048 = true := by quickRfl
theorem blk_2_1 : blocksOK T2 (true, 63, 0) J2 2048 2048 = true := by quickRfl
theorem part_2_0 : partOK T2 (true, 63, 0) J2 0 4096 = true := by quickRfl
theorem part_2_1 : partOK T2 (true, 63, 0) J2 1 4096 = true := by quickRfl
theorem part_2_2 : partOK T2 (true, 63, 0) J2 2 0 = true := by quickRfl
theorem part_2_3 : partOK T2 (true, 63, 0) J2 3 0 = true := by quickRfl
theorem part_2_4 : partOK T2 (true, 63, 0) J2 4 0 = true := by quickRfl
theorem part_2_5 : partOK T2 (true, 63, 0) J2 5 0 = true := by quickRfl
theorem part_2_6 : partOK T2 (true, 63, 0) J2 6 0 = true := by quickRfl
theorem part_2_7 : partOK T2 (true, 63, 0) J2 7 0 = true := by quickRfl

theorem sort_6 : sortOK T6 J6 = true := by quickRfl
theorem blk_6_0 : blocksOK T6 (true, 0, 0) J6 0 2048 = true := by quickRfl
theorem blk_6_1 : blocksOK T6 (true, 0, 0) J6 2048 2048 = true := by quickRfl
theorem part_6_0 : partOK T6 (true, 0, 0) J6 0 0 = true := by quickRfl
theorem part_6_1 : partOK T6 (true, 0, 0) J6 1 0 = true := by quickRfl
theorem part_6_2 : partOK T6 (true, 0, 0) J6 2 0 = true := by quickRfl
theorem part_6_3 : partOK T6 (true, 0, 0) J6 3 0 = true := by quickRfl
theorem part_6_4 : partOK T6 (true, 0, 0) J6 4 0 = true := by quickRfl
theorem part_6_5 : partOK T6 (true, 0, 0) J6 5 0 = true := by quickRfl
theorem part_6_6 : partOK T6 (true, 0, 0) J6 6 0 = true := by quickRfl
theorem part_6_7 : partOK T6 (true, 0, 0) J6 7 0 = true := by quickRfl

theorem imgs_1 : imgs 1 = imgs1L := by decide +kernel
theorem imgs_2 : imgs 2 = imgs2L := by decide +kernel

theorem tr_0 : trees1 0 18 = true := by quickRfl
theorem tr_1 : trees1 18 18 = true := by quickRfl
theorem tr_2 : trees1 36 18 = true := by quickRfl
theorem tr_3 : trees1 54 18 = true := by quickRfl
theorem tr_4 : trees1 72 18 = true := by quickRfl
theorem tr_5 : trees1 90 18 = true := by quickRfl
theorem tr_6 : trees1 108 18 = true := by quickRfl
theorem tr_7 : trees1 126 11 = true := by quickRfl

theorem tree_2 : tree2 = true := by quickRfl

theorem edges_0 : edges 0 = true := by quickRfl
theorem edges_1 : edges 1 = true := by quickRfl

theorem span_1 : spanOK actA (SB 1) (SC 1) 8 = true := by quickRfl
theorem span_2 : spanOK actB (SB 2) (SC 2) 12 = true := by quickRfl

theorem sq_1 : allN 137 (fun k => sqW T1 (false, 0, 0) (classEnc k)) = true := by quickRfl
theorem sq_2 : sqW T2 (true, 63, 0) 734 = true := by quickRfl

theorem mem_17 : Nat.beq (valF 25 (rec1 17 10)) 196668 = true := by quickRfl

end CertificateChecks.Coset3023

end

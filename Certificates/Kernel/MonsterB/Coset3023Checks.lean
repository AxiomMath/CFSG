module

public import Certificates.Kernel.MonsterB.Coset3023Defs
import Certificates.Kernel.MonsterB.Coset3023Sound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Coset3023

open CFSG.KLie.CT CFSG.KC.KDense CFSG.KC.SortTree CFSG.Monster.B CFSG.Monster.B.TwoA.Census

set_option maxRecDepth 100000

theorem c3pb_ok : ∀ n < 12, fget c3PB n 12 = packBetaT n := by decide +kernel

theorem c3th_ok : c3ThOK = true := by quickRfl

theorem th_ok : thOK = true := (c3ThOK_eq c3pb_ok).symm.trans c3th_ok

theorem pp_1 : ∀ i < 24, pe (PP 1) i = (cosetArr 1)[i]! := by decide +kernel
theorem pp_2 : ∀ i < 24, pe (PP 2) i = (cosetArr 2)[i]! := by decide +kernel
theorem pp_6 : ∀ i < 24, pe (PP 6) i = (cosetArr 6)[i]! := by decide +kernel

theorem bt_1 : betaTabT (PP 1) = 0 := by decide +kernel
theorem bt_2 : betaTabT (PP 2) = 0 := by decide +kernel
theorem bt_6 : betaTabT (PP 6) = 79873156457113056204225129793389314108 := by decide +kernel

theorem e_ok : cosetA 1 = 3 ∧ cosetA 2 = 734 ∧ cosetA 6 = 374 := by decide +kernel

theorem pe_ok : Model.pN 3 = false ∧ Model.pN 734 = true ∧ Model.pN 374 = true := by decide +kernel

theorem w_ok : wP 1 = (false, 0, 0) ∧ wP 2 = (true, 63, 0) ∧ wP 6 = (true, 0, 0) := by decide +kernel

theorem c3tl_1 : c3TabL T1 0 = true := by quickRfl
theorem c3tld_1 : c3TabL T1 4096 = true := by quickRfl
theorem c3tl_2 : c3TabL T2 0 = true := by quickRfl
theorem c3tld_2 : c3TabL T2 4096 = true := by quickRfl
theorem c3tl_6 : c3TabL T6 0 = true := by quickRfl
theorem c3tld_6 : c3TabL T6 4096 = true := by quickRfl

theorem ta_1 : c3TabBA T1 3 false (PP 1) 0 = true := by quickRfl
theorem td_1 : c3TabBD T1 3 false (PP 1) 0 = true := by quickRfl
theorem ta_2 : c3TabBA T2 734 true (PP 2) 0 = true := by quickRfl
theorem td_2 : c3TabBD T2 734 true (PP 2) 0 = true := by quickRfl
theorem ta_6 : c3TabBA T6 374 true (PP 6) 79873156457113056204225129793389314108 = true := by
  quickRfl
theorem td_6 : c3TabBD T6 374 true (PP 6) 79873156457113056204225129793389314108 = true := by
  quickRfl

theorem sort_1 : sortOK T1 J1 = true := by quickRfl
theorem blk_1_0 : blocksOK T1 (false, 0, 0) J1 0 2048 = true := c3BlocksOK_of sort_1 (by quickRfl)
theorem blk_1_1 : blocksOK T1 (false, 0, 0) J1 2048 2048 = true :=
  c3BlocksOK_of sort_1 (by quickRfl)
theorem c3bk_1 : ∀ a < 4096, blockOK T1 (false, 0, 0) J1 a = true := c3Blocks_all blk_1_0 blk_1_1
theorem part_1_0 : partOK T1 (false, 0, 0) J1 0 20480 = true :=
  (c3PartK_eq ..).trans ((c3PartS_eq (by decide) c3bk_1).trans (by quickRfl))
theorem part_1_1 : partOK T1 (false, 0, 0) J1 1 0 = true := (c3PartK_eq ..).trans (by quickRfl)
theorem part_1_2 : partOK T1 (false, 0, 0) J1 2 16384 = true :=
  (c3PartK_eq ..).trans ((c3PartS_eq (by decide) c3bk_1).trans (by quickRfl))
theorem part_1_3 : partOK T1 (false, 0, 0) J1 3 0 = true := (c3PartK_eq ..).trans (by quickRfl)
theorem part_1_4 : partOK T1 (false, 0, 0) J1 4 16384 = true :=
  (c3PartK_eq ..).trans ((c3PartS_eq (by decide) c3bk_1).trans (by quickRfl))
theorem part_1_5 : partOK T1 (false, 0, 0) J1 5 0 = true := (c3PartK_eq ..).trans (by quickRfl)
theorem part_1_6 : partOK T1 (false, 0, 0) J1 6 16384 = true :=
  (c3PartK_eq ..).trans ((c3PartS_eq (by decide) c3bk_1).trans (by quickRfl))
theorem part_1_7 : partOK T1 (false, 0, 0) J1 7 0 = true := (c3PartK_eq ..).trans (by quickRfl)

theorem sort_2 : sortOK T2 J2 = true := by quickRfl
theorem blk_2_0 : blocksOK T2 (true, 63, 0) J2 0 2048 = true := c3BlocksOK_of sort_2 (by quickRfl)
theorem blk_2_1 : blocksOK T2 (true, 63, 0) J2 2048 2048 = true :=
  c3BlocksOK_of sort_2 (by quickRfl)
theorem c3bk_2 : ∀ a < 4096, blockOK T2 (true, 63, 0) J2 a = true := c3Blocks_all blk_2_0 blk_2_1
theorem part_2_0 : partOK T2 (true, 63, 0) J2 0 4096 = true :=
  (c3PartK_eq ..).trans ((c3PartS_eq (by decide) c3bk_2).trans (by quickRfl))
theorem part_2_1 : partOK T2 (true, 63, 0) J2 1 4096 = true :=
  (c3PartK_eq ..).trans ((c3PartS_eq (by decide) c3bk_2).trans (by quickRfl))
theorem part_2_2 : partOK T2 (true, 63, 0) J2 2 0 = true := by quickRfl
theorem part_2_3 : partOK T2 (true, 63, 0) J2 3 0 = true := by quickRfl
theorem part_2_4 : partOK T2 (true, 63, 0) J2 4 0 = true := by quickRfl
theorem part_2_5 : partOK T2 (true, 63, 0) J2 5 0 = true := by quickRfl
theorem part_2_6 : partOK T2 (true, 63, 0) J2 6 0 = true := by quickRfl
theorem part_2_7 : partOK T2 (true, 63, 0) J2 7 0 = true := by quickRfl

theorem sort_6 : sortOK T6 J6 = true := by quickRfl
theorem blk_6_0 : blocksOK T6 (true, 0, 0) J6 0 2048 = true := c3BlocksOK_of sort_6 (by quickRfl)
theorem blk_6_1 : blocksOK T6 (true, 0, 0) J6 2048 2048 = true :=
  c3BlocksOK_of sort_6 (by quickRfl)
theorem part_6_0 : partOK T6 (true, 0, 0) J6 0 0 = true := by quickRfl
theorem part_6_1 : partOK T6 (true, 0, 0) J6 1 0 = true := by quickRfl
theorem part_6_2 : partOK T6 (true, 0, 0) J6 2 0 = true := by quickRfl
theorem part_6_3 : partOK T6 (true, 0, 0) J6 3 0 = true := by quickRfl
theorem part_6_4 : partOK T6 (true, 0, 0) J6 4 0 = true := by quickRfl
theorem part_6_5 : partOK T6 (true, 0, 0) J6 5 0 = true := by quickRfl
theorem part_6_6 : partOK T6 (true, 0, 0) J6 6 0 = true := by quickRfl
theorem part_6_7 : partOK T6 (true, 0, 0) J6 7 0 = true := by quickRfl

theorem c3imgsL_1 :
    imgs1L = ((List.range 24).map fun k => alphaW 3 false (PP 1) 0 (c3GenPW k)).toArray := by
  decide +kernel

theorem c3imgsL_2 :
    imgs2L = ((List.range 24).map fun k => alphaW 734 true (PP 2) 0 (c3GenPW k)).toArray := by
  decide +kernel

theorem imgs_1 : imgs 1 = imgs1L := by
  rw [c3imgsL_1, imgs, c3GensImg_eq th_ok pp_1, e_ok.1, pe_ok.1, bt_1]

theorem imgs_2 : imgs 2 = imgs2L := by
  rw [c3imgsL_2, imgs, c3GensImg_eq th_ok pp_2, e_ok.2.1, pe_ok.2.1, bt_2]

theorem c3img1_ok : ∀ k < 24, c3ImgW c3Img1 k = imgs1L[k]! := by decide +kernel
theorem c3img2_ok : ∀ k < 24, c3ImgW c3Img2 k = imgs2L[k]! := by decide +kernel

theorem c3ActK_1 : c3ActK c3Img1 = actA :=
  c3ActK_eq (c3ImgW_eq (by decide +kernel) (by decide +kernel) c3img1_ok)

theorem c3ActK_2 : c3ActK c3Img2 = actB :=
  c3ActK_eq (c3ImgW_eq (by decide +kernel) (by decide +kernel) c3img2_ok)

theorem c3trees1_eq (lo n : ℕ) : trees1 lo n = c3Trees1K lo n := by
  unfold trees1 c3Trees1K c3Tree1K tree1
  rw [c3ActK_1]

theorem c3tree2_eq : tree2 = c3Tree2K := by
  unfold tree2 c3Tree2K
  rw [c3ActK_2]

theorem c3edges_eq (m : ℕ) : edges m = c3EdgesK m := by
  unfold edges c3EdgesK
  rw [c3ActK_1]

theorem c3trK_0 : c3Trees1K 0 18 = true := by quickRfl
theorem c3trK_1 : c3Trees1K 18 18 = true := by quickRfl
theorem c3trK_2 : c3Trees1K 36 18 = true := by quickRfl
theorem c3trK_3 : c3Trees1K 54 18 = true := by quickRfl
theorem c3trK_4 : c3Trees1K 72 18 = true := by quickRfl
theorem c3trK_5 : c3Trees1K 90 18 = true := by quickRfl
theorem c3trK_6 : c3Trees1K 108 18 = true := by quickRfl
theorem c3trK_7 : c3Trees1K 126 11 = true := by quickRfl
theorem c3treeK_2 : c3Tree2K = true := by quickRfl
theorem c3edK_0 : c3EdgesK 0 = true := by quickRfl
theorem c3edK_1 : c3EdgesK 1 = true := by quickRfl

theorem tr_0 : trees1 0 18 = true := (c3trees1_eq 0 18).trans c3trK_0
theorem tr_1 : trees1 18 18 = true := (c3trees1_eq 18 18).trans c3trK_1
theorem tr_2 : trees1 36 18 = true := (c3trees1_eq 36 18).trans c3trK_2
theorem tr_3 : trees1 54 18 = true := (c3trees1_eq 54 18).trans c3trK_3
theorem tr_4 : trees1 72 18 = true := (c3trees1_eq 72 18).trans c3trK_4
theorem tr_5 : trees1 90 18 = true := (c3trees1_eq 90 18).trans c3trK_5
theorem tr_6 : trees1 108 18 = true := (c3trees1_eq 108 18).trans c3trK_6
theorem tr_7 : trees1 126 11 = true := (c3trees1_eq 126 11).trans c3trK_7

theorem tree_2 : tree2 = true := c3tree2_eq.trans c3treeK_2

theorem edges_0 : edges 0 = true := (c3edges_eq 0).trans c3edK_0
theorem edges_1 : edges 1 = true := (c3edges_eq 1).trans c3edK_1

theorem span_1 : spanOK actA (SB 1) (SC 1) 8 = true := by quickRfl
theorem span_2 : spanOK actB (SB 2) (SC 2) 12 = true := by quickRfl

theorem sq_1 : allN 137 (fun k => sqW T1 (false, 0, 0) (classEnc k)) = true := by quickRfl
theorem sq_2 : sqW T2 (true, 63, 0) 734 = true := by quickRfl

theorem mem_17 : Nat.beq (valF 25 (rec1 17 10)) 196668 = true := by quickRfl

end CertificateChecks.Coset3023

end

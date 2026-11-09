module

public import Certificates.Kernel.Sporadic.Fi24ThreeO.Data
public import Certificates.Kernel.Sporadic.Fi24Kit.Split
import CFSG.Certificates.Kernel.Common.SliceRange

set_option Elab.async false

public section

#kc_slice_range CFSG.KD.Fi24ThreeO.fx CFSG.KD.Fi24ThreeO.Ck.fx 0 4
#kc_slice_range CFSG.KD.Fi24ThreeO.cu CFSG.KD.Fi24ThreeO.Ck.cu 0 4

#kn_fixS CFSG.KD.Fi24ThreeO.Ck.GF0 (CFSG.KC.Fi24ThreeO.wkC CFSG.KD.Fi24Net.NW CFSG.KD.Fi24Kit.NT (CFSG.KD.Fi24ThreeO.wr (nat_lit 0))) 10
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GW0 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT) ((CFSG.KD.Fi24ThreeO.wr (nat_lit 0))) 9
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GV0 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT) ((CFSG.KD.Fi24ThreeO.wr (nat_lit 0)) ++ (CFSG.KD.Fi24ThreeO.wr (nat_lit 0))) 9
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GE0_0 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT)
  (CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 0)).getD 0 ([], [])).1 ++ CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 0)).getD 0 ([], [])).2) 9
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GE0_1 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT)
  (CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 0)).getD 1 ([], [])).1 ++ CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 0)).getD 1 ([], [])).2) 9

#kn_fixS CFSG.KD.Fi24ThreeO.Ck.GF1 (CFSG.KC.Fi24ThreeO.wkC CFSG.KD.Fi24Net.NW CFSG.KD.Fi24Kit.NT (CFSG.KD.Fi24ThreeO.wr (nat_lit 1))) 10
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GW1 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT) ((CFSG.KD.Fi24ThreeO.wr (nat_lit 1))) 9
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GV1 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT) ((CFSG.KD.Fi24ThreeO.wr (nat_lit 1)) ++ (CFSG.KD.Fi24ThreeO.wr (nat_lit 1))) 9
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GE1_0 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT)
  (CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 1)).getD 0 ([], [])).1 ++ CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 1)).getD 0 ([], [])).2) 9
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GE1_1 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT)
  (CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 1)).getD 1 ([], [])).1 ++ CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 1)).getD 1 ([], [])).2) 9

#kn_fixS CFSG.KD.Fi24ThreeO.Ck.GF2 (CFSG.KC.Fi24ThreeO.wkC CFSG.KD.Fi24Net.NW CFSG.KD.Fi24Kit.NT (CFSG.KD.Fi24ThreeO.wr (nat_lit 2))) 10
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GW2 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT) ((CFSG.KD.Fi24ThreeO.wr (nat_lit 2))) 9
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GV2 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT) ((CFSG.KD.Fi24ThreeO.wr (nat_lit 2)) ++ (CFSG.KD.Fi24ThreeO.wr (nat_lit 2))) 9
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GE2_0 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT)
  (CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 2)).getD 0 ([], [])).1 ++ CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 2)).getD 0 ([], [])).2) 9
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GE2_1 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT)
  (CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 2)).getD 1 ([], [])).1 ++ CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 2)).getD 1 ([], [])).2) 9

#kn_fixS CFSG.KD.Fi24ThreeO.Ck.GF3 (CFSG.KC.Fi24ThreeO.wkC CFSG.KD.Fi24Net.NW CFSG.KD.Fi24Kit.NT (CFSG.KD.Fi24ThreeO.wr (nat_lit 3))) 10
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GW3 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT) ((CFSG.KD.Fi24ThreeO.wr (nat_lit 3))) 9
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GV3 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT) ((CFSG.KD.Fi24ThreeO.wr (nat_lit 3)) ++ (CFSG.KD.Fi24ThreeO.wr (nat_lit 3))) 9
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GE3_0 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT)
  (CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 3)).getD 0 ([], [])).1 ++ CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 3)).getD 0 ([], [])).2) 9
#kn_pk19 CFSG.KD.Fi24ThreeO.Ck.GE3_1 (CFSG.KD.Fi24Net.NW) (CFSG.KD.Fi24Kit.NT)
  (CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 3)).getD 1 ([], [])).1 ++ CFSG.KC.Fi24ThreeO.dW ((CFSG.KD.Fi24ThreeO.gp (nat_lit 3)).getD 1 ([], [])).2) 9

namespace CFSG.KD.Fi24ThreeO.Ck

open CFSG.KD.Fi24Kit.Split

theorem gn0 : CFSG.KD.Fi24ThreeO.gn (nat_lit 0) = true := by
  unfold CFSG.KD.Fi24ThreeO.gn CFSG.KC.Fi24ThreeO.gensOK CFSG.KC.Fi24ThreeO.fixC
  rw [GF0.eq, letB_eq]
  rw [show CFSG.KD.Fi24ThreeO.gp (nat_lit 0) = [(CFSG.KD.Fi24ThreeO.gp (nat_lit 0)).getD 0 ([], []), (CFSG.KD.Fi24ThreeO.gp (nat_lit 0)).getD 1 ([], [])] from rfl]
  dsimp only
  rw [offS_eq, offS_eq, GE0_0.eq, GE0_1.eq, GW0.eq, GV0.eq]
  quickRfl

theorem gn1 : CFSG.KD.Fi24ThreeO.gn (nat_lit 1) = true := by
  unfold CFSG.KD.Fi24ThreeO.gn CFSG.KC.Fi24ThreeO.gensOK CFSG.KC.Fi24ThreeO.fixC
  rw [GF1.eq, letB_eq]
  rw [show CFSG.KD.Fi24ThreeO.gp (nat_lit 1) = [(CFSG.KD.Fi24ThreeO.gp (nat_lit 1)).getD 0 ([], []), (CFSG.KD.Fi24ThreeO.gp (nat_lit 1)).getD 1 ([], [])] from rfl]
  dsimp only
  rw [offS_eq, offS_eq, GE1_0.eq, GE1_1.eq, GW1.eq, GV1.eq]
  quickRfl

theorem gn2 : CFSG.KD.Fi24ThreeO.gn (nat_lit 2) = true := by
  unfold CFSG.KD.Fi24ThreeO.gn CFSG.KC.Fi24ThreeO.gensOK CFSG.KC.Fi24ThreeO.fixC
  rw [GF2.eq, letB_eq]
  rw [show CFSG.KD.Fi24ThreeO.gp (nat_lit 2) = [(CFSG.KD.Fi24ThreeO.gp (nat_lit 2)).getD 0 ([], []), (CFSG.KD.Fi24ThreeO.gp (nat_lit 2)).getD 1 ([], [])] from rfl]
  dsimp only
  rw [offS_eq, offS_eq, GE2_0.eq, GE2_1.eq, GW2.eq, GV2.eq]
  quickRfl

theorem gn3 : CFSG.KD.Fi24ThreeO.gn (nat_lit 3) = true := by
  unfold CFSG.KD.Fi24ThreeO.gn CFSG.KC.Fi24ThreeO.gensOK CFSG.KC.Fi24ThreeO.fixC
  rw [GF3.eq, letB_eq]
  rw [show CFSG.KD.Fi24ThreeO.gp (nat_lit 3) = [(CFSG.KD.Fi24ThreeO.gp (nat_lit 3)).getD 0 ([], []), (CFSG.KD.Fi24ThreeO.gp (nat_lit 3)).getD 1 ([], [])] from rfl]
  dsimp only
  rw [offS_eq, offS_eq, GE3_0.eq, GE3_1.eq, GW3.eq, GV3.eq]
  quickRfl

theorem lv_t : CFSG.KD.Fi24ThreeO.lv = true := by quickRfl

end CFSG.KD.Fi24ThreeO.Ck

end

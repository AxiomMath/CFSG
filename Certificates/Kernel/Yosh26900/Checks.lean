module

public import Certificates.Kernel.Yosh26900.Tabs
public import Certificates.Data.Kernel.Yosh26900
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Yosh26900

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Yosh26900

@[expose] noncomputable def s0C : Nat := SC (nat_lit 0)

@[expose] noncomputable def eC : Nat := SC (nat_lit 1)

@[expose] noncomputable def gC : Nat := SC (nat_lit 2)

@[expose] noncomputable def cC : Nat := SC (nat_lit 8)

@[expose] noncomputable def u1C : Nat := SC (nat_lit 9)

@[expose] noncomputable def ecC : Nat := mul (nat_lit 14) eC cC

@[expose] noncomputable def YG (l : Nat) : Nat := SC (Nat.add (nat_lit 3) l)

@[expose] noncomputable def SV (s : Nat) : Nat := SC (Nat.add (nat_lit 15) s)

@[expose] noncomputable def PSs (s k : Nat) : Nat := PS (Nat.add (Nat.mul (nat_lit 384) s) k)

@[expose] noncomputable def valsB (s : Nat) : Bool :=
  allN (nat_lit 384) (vAt KP (PSs s) s0C ecC (KE (SV s)))

@[expose] noncomputable def ptB (s : Nat) : Bool :=
  allN (nat_lit 128) (ptAt (PSs s) TE TI fun j => PJ (Nat.add (Nat.mul (nat_lit 128) s) j))

@[expose] noncomputable def badB (s : Nat) : Bool :=
  letB (SC (nat_lit 11)) fun iu => badAt TE TI (PSs s) (KE iu) (PSs s iu)

@[expose] noncomputable def miscB (_ : Nat) : Bool :=
  andB (andB (Nat.blt (SC (nat_lit 10)) (nat_lit 384)) (Nat.beq (KE (SC (nat_lit 10))) cC))
  (andB (andB (Nat.blt (SC (nat_lit 11)) (nat_lit 384))
      (Nat.beq (KE (SC (nat_lit 11))) (mul (nat_lit 14) eC u1C)))
  (andB (andB (Nat.blt (SC (nat_lit 12)) (nat_lit 128)) (Nat.beq (TE (SC (nat_lit 12))) u1C))
  (andB (andB (Nat.blt (SC (nat_lit 13)) (nat_lit 384))
      (Nat.beq (mul (nat_lit 14) (KE (SC (nat_lit 13))) s0C)
        (mul (nat_lit 14) (mul (nat_lit 14) s0C s0C) (KE (SC (nat_lit 13))))))
  (andB (ord8 gC)
  (andB (Nat.beq (cntN (nat_lit 128) fun j =>
      Nat.beq (mul (nat_lit 14) (TE j) (TE j)) (one (nat_lit 14))) (nat_lit 56))
  (andB (Nat.blt (SC (nat_lit 14)) (nat_lit 128))
    (notB (Nat.beq (pow (nat_lit 14) (TE (SC (nat_lit 14))) (nat_lit 4)) (one (nat_lit 14))))))))))

theorem y_tree : allN 384 (treeAt (mul 14) (one 14) SC 8 KE KP) = true := by quickRfl

theorem y_lt3 : allN 384 (fun k => Nat.blt (Nat.shiftRight (KP k) 24) 3) = true := by quickRfl

theorem y_sort : allN 384 (sortAt 384 KE KS) = true := by quickRfl

theorem y_closed : allN 384 (closedAt (mul 14) SC 8 384 KE KC) = true := by quickRfl

theorem y_gw : andB (Nat.beq (wordF YG GW 4) gC) (allN 4 fun i => Nat.blt (GW i) 5) = true := by
  quickRfl

theorem t_tree : allN 128 (treeAt (mul 14) (one 14) YG 4 TE TP) = true := by quickRfl

theorem t_sort : allN 128 (sortAt 128 TE TS) = true := by quickRfl

theorem t_closed : allN 128 (closedAt (mul 14) YG 4 128 TE TC) = true := by quickRfl

theorem t_ti : allN 128 (tiAt KE TE TI) = true := by quickRfl

theorem y_cls0 : allR 0 96 (clsAt KE KP CL SV s0C eC ecC gC) = true := by quickRfl

theorem y_cls1 : allR 96 96 (clsAt KE KP CL SV s0C eC ecC gC) = true := by quickRfl

theorem y_cls2 : allR 192 96 (clsAt KE KP CL SV s0C eC ecC gC) = true := by quickRfl

theorem y_cls3 : allR 288 96 (clsAt KE KP CL SV s0C eC ecC gC) = true := by quickRfl

theorem y_vals : allN 4 valsB = true := by quickRfl

theorem y_cen0 : allN 384 (cenAt KE (PSs 0) cC 0) = true := by quickRfl

theorem y_cen1 : allN 384 (cenAt KE (PSs 1) cC 1) = true := by quickRfl

theorem y_pt : allN 4 ptB = true := by quickRfl

theorem y_bad2 : badB 2 = true := by quickRfl

theorem y_bad3 : badB 3 = true := by quickRfl

theorem y_cn : allN 384 (cnAt KE eC cC) = true := by quickRfl

theorem y_cs : allN 384 (csAt KE s0C eC cC) = true := by quickRfl

theorem y_syl : allN 384 (sylAt KE SY s0C) = true := by quickRfl

theorem y_misc : miscB 0 = true := by quickRfl

end CFSG.KD.Yosh26900

end

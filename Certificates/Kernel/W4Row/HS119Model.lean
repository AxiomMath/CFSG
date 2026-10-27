module

public import Certificates.Kernel.W4Row.HS119Tabs
public import Certificates.Data.Kernel.W4Row.HS119K
public import Certificates.Kernel.LocalQT.SV.C4126T
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS119

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.HS119 CFSG.KD.LQT.C4126

theorem s_om : allN 32 (omAt Om) = true := by quickRfl

theorem s_rho : allN 4 (fun l => allN 32 (rhoAt (fun l => HC.F (Nat.succ l)) Om SG l)) = true := by
  quickRfl

theorem s_perm : allN 4 (fun l => permK 32 (SG l)) = true := by quickRfl

theorem s_tree : allN 1024 (treeAt (mul 32) (one 32) SG 4 SE SPA) = true := by quickRfl

theorem s_sort : allN 1024 (sortAt 1024 SE SSG) = true := by quickRfl

theorem s_inv : allN 1024 (invAt SE IX II) = true := by quickRfl

theorem s_ii : allN 192 (iiAt IX II) = true := by quickRfl

theorem s_pair0 : allR 0 25 (fun a => allN 192 (pairAt SE II PT a)) = true := by quickRfl

theorem s_pair1 : allR 25 29 (fun a => allN 192 (pairAt SE II PT a)) = true := by quickRfl

theorem s_pair2 : allR 54 36 (fun a => allN 192 (pairAt SE II PT a)) = true := by quickRfl

theorem s_pair3 : allR 90 102 (fun a => allN 192 (pairAt SE II PT a)) = true := by quickRfl

theorem s_cm : allN 192 (fun a => allN 192 (cmAt PT IX CM a)) = true := by quickRfl

theorem s_cg : allN 4 (fun l => allN 192 (cgAt SE II SG CG l)) = true := by quickRfl

end CFSG.KD.HS119

end

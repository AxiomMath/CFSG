module

public import Certificates.Kernel.M23Dc.NfWData
public import Certificates.Kernel.M23Dc.Defs
public import Certificates.Data.Kernel.ConjWalkL
public import Certificates.Data.Kernel.ConjCountL
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M23Dc

open CFSG.KC.ConjWalk CFSG.KC.ConjCount

theorem nf2w : walkKL 23 [19, 20, 21, 22] (encL 64 (NFW.t2.getD 1 [])) (encL 64 (NFW.ti2.getD 1 []))
    (encL 64 (NFW.t2.getD 3 [])) (encL 64 (NFW.ti2.getD 3 []))
    (encL 64 (tabW NFW.t2 23 NFW.tw2)) NFW.recs2 = true := by
  quickRfl

theorem nf5w : walkKL 23 [19, 20, 21, 22] (encL 64 (NFW.t5.getD 1 [])) (encL 64 (NFW.ti5.getD 1 []))
    (encL 64 (NFW.t5.getD 3 [])) (encL 64 (NFW.ti5.getD 3 []))
    (encL 64 (tabW NFW.t5 23 NFW.tw5)) NFW.recs5 = true := by
  quickRfl

theorem nf2w_len : (NFW.recs2.length == 2688) = true := by quickRfl

theorem nf5w_len : (NFW.recs5.length == 2688) = true := by quickRfl

theorem nf2w_tabs : (NFW.t2 == (mLet 2).toList.map Array.toList) = true := by quickRfl

theorem nf5w_tabs : (NFW.t5 == (mLet 5).toList.map Array.toList) = true := by quickRfl

theorem nf2w_inv : (Nat.blt 3 NFW.t2.length && invOK 23 (NFW.t2.getD 1 []) (NFW.ti2.getD 1 []) &&
    invOK 23 (NFW.t2.getD 3 []) (NFW.ti2.getD 3 [])) = true := by
  quickRfl

theorem nf5w_inv : (Nat.blt 3 NFW.t5.length && invOK 23 (NFW.t5.getD 1 []) (NFW.ti5.getD 1 []) &&
    invOK 23 (NFW.t5.getD 3 []) (NFW.ti5.getD 3 [])) = true := by
  quickRfl

theorem nf2w_ord : (NFW.tw2.all (· < NFW.t2.length) &&
    tabW NFW.t2 23 (NFW.tw2 ++ NFW.tw2 ++ NFW.tw2 ++ NFW.tw2 ++ NFW.tw2) == List.range 23 &&
    !(tabW NFW.t2 23 NFW.tw2 == List.range 23)) = true := by
  quickRfl

theorem nf5w_ord : (NFW.tw5.all (· < NFW.t5.length) &&
    tabW NFW.t5 23 (NFW.tw5 ++ NFW.tw5 ++ NFW.tw5 ++ NFW.tw5 ++ NFW.tw5) == List.range 23 &&
    !(tabW NFW.t5 23 NFW.tw5 == List.range 23)) = true := by
  quickRfl

end CFSG.KD.M23Dc

end

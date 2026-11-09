module

public import Certificates.Kernel.Sporadic.Fi24ThreeAK.Data
import Certificates.Kernel.Sporadic.Fi24Net.PTabSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24ThreeAK.Ck

theorem d0 : CFSG.KD.Fi24ThreeAK.d4 (nat_lit 0) = true := by
  unfold CFSG.KD.Fi24ThreeAK.d4 CFSG.KC.Fi24ThreeAK.d4At CFSG.KC.Fi24ThreeAK.edgeAt
    CFSG.KC.Fi24ThreeAK.commAt CFSG.KC.Fi24Kit.wP
  rw [← CFSG.KD.Fi24Net.letPT_eq]
  quickRfl

theorem d1 : CFSG.KD.Fi24ThreeAK.d4 (nat_lit 1) = true := by
  unfold CFSG.KD.Fi24ThreeAK.d4 CFSG.KC.Fi24ThreeAK.d4At CFSG.KC.Fi24ThreeAK.edgeAt
    CFSG.KC.Fi24ThreeAK.commAt CFSG.KC.Fi24Kit.wP
  rw [← CFSG.KD.Fi24Net.letPT_eq]
  quickRfl

theorem d2 : CFSG.KD.Fi24ThreeAK.d4 (nat_lit 2) = true := by
  unfold CFSG.KD.Fi24ThreeAK.d4 CFSG.KC.Fi24ThreeAK.d4At CFSG.KC.Fi24ThreeAK.edgeAt
    CFSG.KC.Fi24ThreeAK.commAt CFSG.KC.Fi24Kit.wP
  rw [← CFSG.KD.Fi24Net.letPT_eq]
  quickRfl

end CFSG.KD.Fi24ThreeAK.Ck

end

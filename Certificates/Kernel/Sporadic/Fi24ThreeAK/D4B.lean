module

public import Certificates.Kernel.Sporadic.Fi24ThreeAK.Data
import Certificates.Kernel.Sporadic.Fi24Net.PTabSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Fi24ThreeAK.Ck

theorem d3 : CFSG.KD.Fi24ThreeAK.d4 (nat_lit 3) = true := by
  unfold CFSG.KD.Fi24ThreeAK.d4 CFSG.KC.Fi24ThreeAK.d4At CFSG.KC.Fi24ThreeAK.edgeAt
    CFSG.KC.Fi24ThreeAK.commAt CFSG.KC.Fi24Kit.wP
  rw [← CFSG.KD.Fi24Net.letPT_eq]
  quickRfl

theorem d4 : CFSG.KD.Fi24ThreeAK.d4 (nat_lit 4) = true := by
  unfold CFSG.KD.Fi24ThreeAK.d4 CFSG.KC.Fi24ThreeAK.d4At CFSG.KC.Fi24ThreeAK.edgeAt
    CFSG.KC.Fi24ThreeAK.commAt CFSG.KC.Fi24Kit.wP
  rw [← CFSG.KD.Fi24Net.letPT_eq]
  quickRfl

theorem d5 : CFSG.KD.Fi24ThreeAK.d4 (nat_lit 5) = true := by
  unfold CFSG.KD.Fi24ThreeAK.d4 CFSG.KC.Fi24ThreeAK.d4At CFSG.KC.Fi24ThreeAK.edgeAt
    CFSG.KC.Fi24ThreeAK.commAt CFSG.KC.Fi24Kit.wP
  rw [← CFSG.KD.Fi24Net.letPT_eq]
  quickRfl

end CFSG.KD.Fi24ThreeAK.Ck

end

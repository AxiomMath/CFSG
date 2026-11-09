module

public import Certificates.Kernel.Sporadic.Fi24KPerm.Data
public import Certificates.Kernel.Sporadic.Fi24Sev.DataT
public import CFSG.Certificates.Kernel.Spor.Fi24SevBSound

public section

namespace CFSG.KD.Fi24KPerm.Ck

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KS.Fi24Sev
  CFSG.KS.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

theorem fqP_all {i : Nat} (h : allL (fun b => Nat.beq (CFSG.KD.Fi24Sev.ptCT NT (fq i).1 b)
    (CFSG.KD.Fi24Sev.ptCT NT (fq i).2 b)) cb = true) {b : Nat} (hb : b ∈ cb) : fqP i b = true := by
  have e := CFSG.KS.Fi24ThreeO.allL_spec h b hb
  unfold fqP
  rwa [ptCB_eq, ← CFSG.KD.Fi24Sev.ptCT_eq]

end CFSG.KD.Fi24KPerm.Ck

end

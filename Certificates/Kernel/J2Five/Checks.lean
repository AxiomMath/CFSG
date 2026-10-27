module

public import Certificates.Kernel.J2Five.Data
public import Certificates.Data.Kernel.J2Five
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.J2Five

@[expose] noncomputable def G0 : List Nat := [getN gen 0, getN gen 1, getN gen 2]

@[expose] noncomputable def Gi0 : List Nat := [getN gen 0, getN gen 3, getN gen 2]

theorem gens_ok : bAnd(gensOK G0, eq (getN gen 3) (pm (getN gen 1) (getN gen 1))) = true := by
  quickRfl

theorem ck3_ok : ck3 G0 s3 pts3 x3 c3 k3 id3 = true := by
  quickRfl

theorem ck5_ok : ck5 G0 s5 pts5 x5 c5 id5 zA zC h5 t3 = true := by
  quickRfl

theorem orbA_ok : orbOK G0 Gi0 (zval G0 s5 x5 zA) ptsA rA 2017 = true := by
  quickRfl

theorem orbC_ok : orbOK G0 Gi0 (zval G0 s5 x5 zC) ptsC rC 6049 = true := by
  quickRfl

end CFSG.KD.J2Five

end

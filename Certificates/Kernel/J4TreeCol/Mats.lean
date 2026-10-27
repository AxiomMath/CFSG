module

public import Certificates.Data.Kernel.J4TreeCol
public import Certificates.Kernel.J4Q.MatData
public import Certificates.Kernel.J4Q.QTData
public import Certificates.Kernel.J4Q.MaskData

public section

namespace CFSG.KC.J4TreeCol

open CFSG.KD.J4Q

@[expose] noncomputable def colMats : Mats :=
  ⟨c, rm, one, pad, [U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10], [mkKM_0, mkKM_1, mkKM_2, mkKM_3],
    [L0, L1, L2, A, B], [L0i, L1i, L2i, Ai, Bi]⟩

end CFSG.KC.J4TreeCol

end

module

public import Certificates.Data.Kernel.WrTwin
public import Certificates.Data.Holder272.E29Data
public import Certificates.Kernel.WrTwin.Data

public section

namespace CFSG.KD.WrTwin

open CFSG.KC.WrTwin CFSG.ClassicalInvolution.Q3.E29Data

theorem e29_rowsB : (e29ConjData.drop 1568).all (rowPiOK 16 id16 pi8 56 g29 i29) = true := by
  decide +kernel

end CFSG.KD.WrTwin

end

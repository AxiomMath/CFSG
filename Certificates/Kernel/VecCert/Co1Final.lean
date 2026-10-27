
module

public import Certificates.Kernel.VecCert.Co1.Ok
public import Certificates.Kernel.VecCert.Co1Bound
public import CFSG.Sporadic.Co1.Module.OrbitsInputs
public import CFSG.Sporadic.Co1.CertificateBase
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.HS.Simple

public section

namespace CertificateChecks.KernelVec.Co1

theorem vecCert_co1 :
    CFSG.Sporadic.SmallF2.Native.vecCert CFSG.Sporadic.Co1.Native.co1Data 3 = true :=
  ok Co1Bound.card_J_le

theorem orbit_v₂ :
    CFSG.Sporadic.SmallF2.Native.vOrbitOK 24 98280 CFSG.Sporadic.Co1.Module.dat.colsA
      CFSG.Sporadic.Co1.Module.dat.colsB (CFSG.Sporadic.Co1.Module.orbitOf 2 98280) = true :=
  (CFSG.Sporadic.SmallF2.facts_of_vecCert _ vecCert_co1).orbit

end CertificateChecks.KernelVec.Co1

end

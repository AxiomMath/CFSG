module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Data.Kernel.L34TwoSigK
public import Certificates.Data.L34TwoSig
meta import Certificates.Data.L34TwoSig
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

namespace CertificateChecks.KernelLC.L34Two

meta def bM : Array (Array Nat) := Certificates.L34TwoSig.bGens

meta def id42 : Array Nat := CFSG.PSL3Four.Native.idTab 42

end CertificateChecks.KernelLC.L34Two

public section

set_option maxRecDepth 400000

#kpenum CertificateChecks.KernelLC.L34TwoB 42 6 false CertificateChecks.KernelLC.L34Two.bM
  CertificateChecks.KernelLC.L34Two.bM CertificateChecks.KernelLC.L34Two.id42 9

#kc_repo #kc_ktree CertificateChecks.KernelLC.L34TwoW WL "Certificates/Kernel/LocalComp/L34Two/w.bin" 64 4 967680 16073729437599541424

namespace CertificateChecks.KernelLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KLie.CT (fget)

@[expose] noncomputable def L34TwoB.BTI (j : Nat) : Nat := pinvS 42 6 (mask 6) (L34TwoB.T j)

@[expose] noncomputable def L34TwoW.W (k : Nat) : Nat :=
  fget (L34TwoW.WL (Nat.shiftRight k (nat_lit 4))) (Nat.land k (nat_lit 15)) (nat_lit 32)

@[expose] noncomputable def L34TwoW.sig (s : Nat) : Bool :=
  CFSG.KC.L34Two.sigSl 42 6 (L34TwoB.G 0) (L34TwoB.G 1) L34TwoB.T L34TwoB.BTI 9 L34R.T L34TwoW.W
    1344 s

end CertificateChecks.KernelLC

end

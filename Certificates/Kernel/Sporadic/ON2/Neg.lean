module

public import Certificates.Kernel.Sporadic.ON.GenTab
public import Certificates.Kernel.Sporadic.ON2.Data
public import Certificates.Data.Kernel.Spor.ONNegK
public meta import Certificates.Data.CFSGNative.ON.Certificate

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2

meta def negM : Array Nat :=
  let O := CFSG.Sporadic.ON.Native.orbitData ()
  let idx := CFSG.Sporadic.ON.Native.indexOf O.keys
  (CFSG.Sporadic.ON.Native.negTable O fun x => idx.getD x CFSG.Sporadic.ON.Native.nPts).map (·.toNat)

end CertificateChecks.KernelSpor.ON2

#kon_table CertificateChecks.KernelSpor.ONW2.NEG CertificateChecks.KernelSpor.ON2.negM

namespace CertificateChecks.KernelSpor.ON2

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

@[expose] noncomputable def negS (s : Nat) : Bool :=
  negRange ONW.K ONW2.NEG (nat_lit 245520) (Nat.mul s (nat_lit 240)) (nat_lit 240)

end CertificateChecks.KernelSpor.ON2

#kon_slices CertificateChecks.KernelSpor.ON2.negS 0 1023

#kon_join CertificateChecks.KernelSpor.ON2.negAll CertificateChecks.KernelSpor.ON2.negS 1023

end

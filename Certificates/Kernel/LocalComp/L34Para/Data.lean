module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Kernel.LocalComp.L34SChk
public import Certificates.Data.Kernel.L34DWord
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicCertInputs
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicCertInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

namespace CertificateChecks.KernelLC.L34Para

open CFSG.ComponentClassification.GrSLit.L34Facts

meta def tM : Array (Array Nat) := wordTabs wT₀

meta def bM : Array (Array Nat) := wordTabs wB₀

meta def p1M : Array (Array Nat) := wordTabs wP₁

meta def p2M : Array (Array Nat) := wordTabs wP₂

meta def yM : Array (Array Nat) := wordTabs wReps

meta def id42 : Array Nat := CFSG.PSL3Four.Native.idTab 42

end CertificateChecks.KernelLC.L34Para

public section

set_option maxRecDepth 400000

#kpenum CertificateChecks.KernelLC.L34PT 42 6 false CertificateChecks.KernelLC.L34Para.tM
  CertificateChecks.KernelLC.L34Para.tM CertificateChecks.KernelLC.L34Para.id42 64
#kpenum CertificateChecks.KernelLC.L34PB 42 6 false CertificateChecks.KernelLC.L34Para.bM
  CertificateChecks.KernelLC.L34Para.bM CertificateChecks.KernelLC.L34Para.id42 192
#kpenum CertificateChecks.KernelLC.L34P1 42 6 false CertificateChecks.KernelLC.L34Para.p1M
  CertificateChecks.KernelLC.L34Para.p1M CertificateChecks.KernelLC.L34Para.id42 960
#kpenum CertificateChecks.KernelLC.L34P2 42 6 false CertificateChecks.KernelLC.L34Para.p2M
  CertificateChecks.KernelLC.L34Para.p2M CertificateChecks.KernelLC.L34Para.id42 960
#kmisc_packarrs CertificateChecks.KernelLC.L34PR.Y CertificateChecks.KernelLC.L34Para.yM 6

#kc_repo #kc_ktree CertificateChecks.KernelLC.L34PC CL "Certificates/Kernel/LocalComp/L34Para/c.bin" 64 4 40320 13864195861916155012
#kc_repo #kc_natList CertificateChecks.KernelLC.L34PW WL "Certificates/Kernel/LocalComp/L34Para/w.txt" 3062 12989251615920313724

namespace CertificateChecks.KernelLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KLie.CT (fget)

@[expose] noncomputable def L34PR.YI (k : Nat) : Nat := pinvS 42 6 (mask 6) (L34PR.Y k)

@[expose] noncomputable def L34PC.C (i : Nat) : Nat :=
  fget (L34PC.CL (Nat.shiftRight i (nat_lit 5))) (Nat.land i (nat_lit 31)) (nat_lit 16)

@[expose] noncomputable def L34PW.A (k j : Nat) : Nat := nIf(Nat.blt j 3, L34PB.G j, L34PR.Y k)

end CertificateChecks.KernelLC

end

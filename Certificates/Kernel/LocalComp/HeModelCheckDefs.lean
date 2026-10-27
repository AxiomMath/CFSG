module

public import Certificates.Kernel.LocalComp.HeModelEnum
public import Certificates.Kernel.LocalComp.HeModelEnumP23
public import Certificates.Kernel.LocalComp.HeModelEnumC
public import Certificates.Kernel.LocalComp.HeModelData
public import Certificates.Kernel.LocalComp.HexaOrb
public import Certificates.Kernel.LocalComp.BindL
public import CFSG.Certificates.Kernel.HeModelKSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeModelCheck

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK CFSG.KC.HeModelK CFSG.KC.Enum CFSG.KS
open CFSG.KS.Prim CFSG.KS.Raw CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HeTri CertificateChecks.KernelLC
open CertificateChecks.KernelLC.BindL CertificateChecks.KernelLC.HeModel
open CertificateChecks.KernelLC.HexaOrb (PT0)

@[expose] noncomputable def PZ : Nat := packA 7 heZetaArr.toList

@[expose] noncomputable def PTC : Nat := packA 6 heTCArr.toList

@[expose] noncomputable def d64 : D64 :=
  ⟨HexaT.ng, HexaT.G, HexaT.N, HexaT.T, HexaM.N, HexaM.T, HexaC.ng, HexaC.G, HeMP12.N, HeMP12.T,
    HeMB0.ng, HeMB0.G, HeMB0.N, HeMB0.T, HeMF0.ng, HeMF0.G, HeMF0.N, HeMF0.T, HeMP23.ng,
    HeMP23.G, PT0, flagB0⟩

@[expose] noncomputable def d32 : D32 :=
  ⟨HeMC.N, HeMC.T, HeMC.ng, HeMC.G, PTC, HeMBC.ng, HeMBC.G, HeMBC.N, HeMBC.T, HeMP0.N, HeMP0.T,
    HeMP1.N, HeMP1.T, HeMP0.ng, HeMP0.G, HeMP1.ng, HeMP1.G, HeMU0.ng, HeMU0.G, HeMU0.N, HeMU0.T,
    HeMU1.ng, HeMU1.G, HeMU1.N, HeMU1.T, flagBC⟩

@[expose] noncomputable def hk : HK := ⟨d64, d32, HeMP23.N, PZ⟩

@[expose] noncomputable def oAt (i : Nat) : Bool := orbAt 7 d64.TT d64.NM d64.TM d64.t0 wOrb i

@[expose] noncomputable def UB : Nat → Bool :=
  ueAt 64 7 d64.NB d64.TB d64.NT d64.TT d64.NF d64.TF d64.FB

@[expose] noncomputable def UBC : Nat → Bool :=
  ueAt 32 6 d32.NBC d32.TBC d32.NU0 d32.TU0 d32.NU1 d32.TU1 d32.FBC

end CertificateChecks.KernelLC.HeModelCheck

end

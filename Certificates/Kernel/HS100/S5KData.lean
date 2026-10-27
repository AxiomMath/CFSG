module

public import Certificates.Kernel.HS100.S5OData
public import Certificates.Kernel.Misc.Perm.HS100.S0Data
public import Certificates.Data.Kernel.PGrp
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5CntData
meta import Certificates.Kernel.Sporadic.RawGen

namespace CertificateChecks.KernelHS100.S5KE

open CFSG.EvenSporadicStandard.HSStd

meta def gS : List (Array Nat) := s5SGens.toList

meta def kS : List Nat := CertificateChecks.KernelHS100.S5OE.keyOrder gS

end CertificateChecks.KernelHS100.S5KE

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelHS100.CS CertificateChecks.KernelHS100.S5KE.gS 100 7
#kss_natlist CertificateChecks.KernelHS100.CS.SKT CertificateChecks.KernelHS100.S5KE.kS

namespace CertificateChecks.KernelHS100.S5K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp
open CertificateChecks.KernelHS100

@[expose] noncomputable def CS.SK : List Nat := (List.range 1024).map CS.SKT

@[expose] noncomputable def F (k : Nat) : Nat := CertificateChecks.KernelMisc.HS100.S0.ZX.F k

@[expose] noncomputable def Z : Nat := F 4

@[expose] def ps : List Nat := [0, 1, 2, 3, 4]

@[expose] noncomputable def osOne (i : Nat) : Bool :=
  rngK (CS.T i) &&
    (Nat.beq (keyCK 100 7 ps Z (CS.T i)) (keyCK 100 7 ps (CS.T i) Z) || !inHS (CS.T i))

@[expose] noncomputable def out1 (i : Nat) : Bool :=
  Nat.beq (keyCK 100 7 ps (CS.T i) (CS.T i)) (keyK 100 7 ps (pidn 100 7)) && !inHS (CS.T i)

@[expose] noncomputable def outZ (i : Nat) : Bool :=
  Nat.beq (keyCK 100 7 ps (CS.T i) (CS.T i)) (keyK 100 7 ps Z) && !inHS (CS.T i)

end CertificateChecks.KernelHS100.S5K

end

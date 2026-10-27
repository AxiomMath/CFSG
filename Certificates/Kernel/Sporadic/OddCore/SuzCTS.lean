module

public import Certificates.Kernel.Sporadic.OddCore.SuzCT
public import Certificates.Kernel.SporSch.Ru.RowsGen

public section

namespace CertificateChecks.KernelSpor.SuzCT

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KC.Misc.HexAt

@[expose] noncomputable def kSl (s : Nat) : Bool :=
  penumSlK 42 6 (mask 6) (42 * 6) false K0E.G K0E.GI 22 K0E.cnt K0E.T K0E.PL K0E.POS K0E.SRT
    K0E.SRI (Nat.mul 448 s) 448

@[expose] noncomputable def dSl (s : Nat) : Bool :=
  penumSlK 42 6 (mask 6) (42 * 6) false DE.G DE.GI 5 DE.cnt DE.T DE.PL DE.POS DE.SRT DE.SRI
    (Nat.mul 2016 s) 2016

@[expose] noncomputable def oSl (l : Nat) : Bool :=
  penumSlK 42 6 (mask 6) (42 * 6) true OF.G OF.GI OF.k (OF.C l) (offF OF.T (OF.TO l))
    (offF OF.PL (OF.PLO l)) (offF OF.POS (OF.POSO l)) (offF OF.SRT (OF.SRTO l))
    (offF OF.SRI (OF.SRIO l)) 0 4032

@[expose] noncomputable def qSl : Bool :=
  penumSlK 54 6 (mask 6) (54 * 6) false QE.G QE.GI 6 QE.cnt QE.T QE.PL QE.POS QE.SRT QE.SRI 0 64

end CertificateChecks.KernelSpor.SuzCT

end

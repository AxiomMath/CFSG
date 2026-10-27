module

public import Certificates.Data.Kernel.SuzDc2.Defs
public import Certificates.Kernel.LocalComp.BlockGen
public import Certificates.Kernel.Sporadic.OddCore.SuzCert

public noncomputable section

namespace CFSG.KD.SuzDc2

open CFSG.KC.E64F

@[expose] def wh (p : Nat) : Bool := Nat.beq (L 5 p) (wordF L LT.hw p)

@[expose] def wx (p : Nat) : Bool := Nat.beq (L 8 p) (wordF L [6, 7] p)

@[expose] def wy (p : Nat) : Bool := Nat.beq (L 9 p) (wordF L [6, 7, 7] p)

@[expose] def winv (p : Nat) : Bool := Nat.beq (L 4 (L 3 p)) p

@[expose] def cb0 (p : Nat) : Bool :=
  Nat.beq (CFSG.KS.Row.rg 15 (CFSG.KS.mask 15) CertificateChecks.KernelSpor.SuzCertT.F 0 p) (L 6 p)

@[expose] def cb1 (p : Nat) : Bool :=
  Nat.beq (CFSG.KS.Row.rg 15 (CFSG.KS.mask 15) CertificateChecks.KernelSpor.SuzCertT.F 715 p)
    (L 7 p)

end CFSG.KD.SuzDc2

#lc_blocks CFSG.KD.SuzDc2.WHB CFSG.KD.SuzDc2.wh 22880 4576

#lc_blocks CFSG.KD.SuzDc2.WXB CFSG.KD.SuzDc2.wx 22880 11440

#lc_blocks CFSG.KD.SuzDc2.WYB CFSG.KD.SuzDc2.wy 22880 11440

#lc_blocks CFSG.KD.SuzDc2.WIB CFSG.KD.SuzDc2.winv 22880 22880

#lc_blocks CFSG.KD.SuzDc2.CB0 CFSG.KD.SuzDc2.cb0 22880 22880

#lc_blocks CFSG.KD.SuzDc2.CB1 CFSG.KD.SuzDc2.cb1 22880 22880

end

module

public import Certificates.Kernel.HN1408.TableIHV
public import Certificates.Kernel.HN1408.Words
public import Certificates.Data.Kernel.Spor.MulHQ
public import Certificates.Data.Kernel.Spor.PEnumR
public import Certificates.Data.Kernel.Spor.PEnumB
public import Certificates.Data.Kernel.HN1408Blk

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.Blk CFSG.KS.PEnumR
open CFSG.KS.PEnumB

@[expose] noncomputable def J1 (j : Nat) : Nat := TI1I j
@[expose] noncomputable def J3 (j : Nat) : Nat := TI3I j
@[expose] noncomputable def J4 (j : Nat) : Nat := TI4I j

@[expose] noncomputable def pe1 (s : Nat) : Bool :=
  slK TI1.cnt (penumPtR 1408 11 (mask 11) TI1.GI 7 TI1.cnt TI1.T TI1.PL TI1.POS TI1.SRT TI1.SRI)
    (Nat.mul 64 s) 64
@[expose] noncomputable def hv1 (s : Nat) : Bool :=
  slK TI1.cnt (hvF 1408 11 (mask 11) TI1.T TI1V) (Nat.mul 128 s) 128
@[expose] noncomputable def hs1 : Bool :=
  slK TI1.cnt (hsortVK TI1.cnt TI1V TI1.HS TI1.HSI) 0 256
@[expose] noncomputable def cl1 (s : Nat) : Bool :=
  slK (Nat.mul TI1.cnt 14) (findPtK TI1.cnt TI1.T (prodQK 1408 11 (mask 11) 14 TI1.T (bothK 7 TI1.GI J1))
    TI1Cl) (Nat.mul 448 s) 448

@[expose] noncomputable def pe3 (s : Nat) : Bool :=
  slK TI3.cnt (penumPtR 1408 11 (mask 11) TI3.GI 2 TI3.cnt TI3.T TI3.PL TI3.POS TI3.SRT TI3.SRI)
    (Nat.mul 240 s) 240
@[expose] noncomputable def hv3 (s : Nat) : Bool :=
  slK TI3.cnt (hvF 1408 11 (mask 11) TI3.T TI3V) (Nat.mul 240 s) 240
@[expose] noncomputable def hs3 : Bool :=
  slK TI3.cnt (hsortVK TI3.cnt TI3V TI3.HS TI3.HSI) 0 960
@[expose] noncomputable def cl3 (s : Nat) : Bool :=
  slK (Nat.mul TI3.cnt 4) (findPtK TI3.cnt TI3.T (prodQK 1408 11 (mask 11) 4 TI3.T (bothK 2 TI3.GI J3))
    TI3Cl) (Nat.mul 480 s) 480

@[expose] noncomputable def pe4 : Bool :=
  penumSlK 1408 11 (mask 11) (1408 * 11) true TI4.G TI4.GI 4 TI4.cnt TI4.T TI4.PL TI4.POS TI4.SRT
    TI4.SRI 0 TI4.cnt
@[expose] noncomputable def hs4 : Bool :=
  slK TI4.cnt (hsortPtK 1408 11 (mask 11) TI4.cnt TI4.T TI4.HS TI4.HSI) 0 TI4.cnt
@[expose] noncomputable def cl4 : Bool :=
  slK (Nat.mul TI4.cnt 8) (findPtK TI4.cnt TI4.T (prodQK 1408 11 (mask 11) 8 TI4.T (bothK 4 TI4.GI J4))
    TI4Cl) 0 (Nat.mul TI4.cnt 8)

@[expose] noncomputable def peL1 : Bool :=
  penumSlK 5 4 (mask 4) (5 * 4) true TL1.G TL1.GI 2 TL1.cnt TL1.T TL1.PL TL1.POS TL1.SRT TL1.SRI 0
    TL1.cnt
@[expose] noncomputable def hsL1 : Bool :=
  slK TL1.cnt (hsortPtK 5 4 (mask 4) TL1.cnt TL1.T TL1.HS TL1.HSI) 0 TL1.cnt
@[expose] noncomputable def clL1 : Bool :=
  slK (Nat.mul TL1.cnt 4) (findPtK TL1.cnt TL1.T (prodQK 5 4 (mask 4) 4 TL1.T (bothK 2 TL1.GI TL1J))
    TL1Cl) 0 (Nat.mul TL1.cnt 4)
@[expose] noncomputable def peL3 : Bool :=
  penumSlK 5 4 (mask 4) (5 * 4) true TL3.G TL3.GI 2 TL3.cnt TL3.T TL3.PL TL3.POS TL3.SRT TL3.SRI 0
    TL3.cnt
@[expose] noncomputable def hsL3 : Bool :=
  slK TL3.cnt (hsortPtK 5 4 (mask 4) TL3.cnt TL3.T TL3.HS TL3.HSI) 0 TL3.cnt
@[expose] noncomputable def clL3 : Bool :=
  slK (Nat.mul TL3.cnt 4) (findPtK TL3.cnt TL3.T (prodQK 5 4 (mask 4) 4 TL3.T (bothK 2 TL3.GI TL3J))
    TL3Cl) 0 (Nat.mul TL3.cnt 4)
@[expose] noncomputable def peL2 (s : Nat) : Bool :=
  penumSlK 8 4 (mask 4) (8 * 4) true TL2.G TL2.GI 2 TL2.cnt TL2.T TL2.PL TL2.POS TL2.SRT TL2.SRI
    (Nat.mul 2016 s) 2016
@[expose] noncomputable def hsL2 (s : Nat) : Bool :=
  slK TL2.cnt (hsortPtK 8 4 (mask 4) TL2.cnt TL2.T TL2.HS TL2.HSI) (Nat.mul 2016 s) 2016
@[expose] noncomputable def clL2 (s : Nat) : Bool :=
  slK (Nat.mul TL2.cnt 4) (findPtK TL2.cnt TL2.T (prodQK 8 4 (mask 4) 4 TL2.T (bothK 2 TL2.GI TL2J))
    TL2Cl) (Nat.mul 8064 s) 8064
@[expose] noncomputable def peLS (s : Nat) : Bool :=
  penumSlK 8 4 (mask 4) (8 * 4) true TLS.G TLS.GI 2 TLS.cnt TLS.T TLS.PL TLS.POS TLS.SRT TLS.SRI
    (Nat.mul 2016 s) 2016
@[expose] noncomputable def hsLS (s : Nat) : Bool :=
  slK TLS.cnt (hsortPtK 8 4 (mask 4) TLS.cnt TLS.T TLS.HS TLS.HSI) (Nat.mul 2016 s) 2016
@[expose] noncomputable def clLS (s : Nat) : Bool :=
  slK (Nat.mul TLS.cnt 4) (findPtK TLS.cnt TLS.T (prodQK 8 4 (mask 4) 4 TLS.T (bothK 2 TLS.GI TLSJ))
    TLSCl) (Nat.mul 8064 s) 8064

@[expose] noncomputable def inOrbS2 (x : Nat) : Bool := orbS2.any fun o => Nat.beq o x

@[expose] noncomputable def orbMapK (g : Nat) : Bool := orbS2.all fun o => inOrbS2 (pt g o)

end CFSG.KD.HN1408

end

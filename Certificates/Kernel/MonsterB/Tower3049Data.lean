module

public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public meta import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd

set_option maxRecDepth 400000

namespace CertificateChecks.Tower3049

open CFSG.Monster.B.Max2.Native

meta def nodeArr : Array (Array Nat) := nodeMats ()

meta def lvVecs (i : Nat) : Array Nat :=
  ((levelPoints (towerPointsAll ()) i).map (·.1)).toArray

meta def zeros : Array Nat := Array.replicate 2300 0

meta def lv0 : Array Nat := lvVecs 0
meta def lv1 : Array Nat := lvVecs 1
meta def lv2 : Array Nat := lvVecs 2
meta def lv3 : Array Nat := lvVecs 3
meta def lv4 : Array Nat := lvVecs 4
meta def lv5 : Array Nat := lvVecs 5

end CertificateChecks.Tower3049

#ks_chars Certificates.Tw3049D CFSG.Monster.B.Max2.Native.dagHex
#kmisc_hexflat Certificates.Tw3049D CFSG.Monster.B.Max2.Native.dagHex 4 2 16 5282
#ks_chars Certificates.Tw3049P CFSG.Monster.B.Max2.Native.pointsHex
#kmisc_hexflat Certificates.Tw3049P CFSG.Monster.B.Max2.Native.pointsHex 2 5 8 4802

#kmisc_packarrs Certificates.Tw3049T CertificateChecks.Tower3049.nodeArr 22

#kmisc_sortpair Certificates.Tw3049S0 CertificateChecks.Tower3049.zeros
  CertificateChecks.Tower3049.lv0 1 2300
#kmisc_sortpair Certificates.Tw3049S1 CertificateChecks.Tower3049.zeros
  CertificateChecks.Tower3049.lv1 1 1408
#kmisc_sortpair Certificates.Tw3049S2 CertificateChecks.Tower3049.zeros
  CertificateChecks.Tower3049.lv2 1 840
#kmisc_sortpair Certificates.Tw3049S3 CertificateChecks.Tower3049.zeros
  CertificateChecks.Tower3049.lv3 1 216
#kmisc_sortpair Certificates.Tw3049S4 CertificateChecks.Tower3049.zeros
  CertificateChecks.Tower3049.lv4 1 36
#kmisc_sortpair Certificates.Tw3049S5 CertificateChecks.Tower3049.zeros
  CertificateChecks.Tower3049.lv5 1 2

public section

namespace CertificateChecks.Tower3049

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def DA (j : Nat) : Nat := pg 16 (mask 16) (Certificates.Tw3049D.F j) 0

@[expose] noncomputable def DB (j : Nat) : Nat := pg 16 (mask 16) (Certificates.Tw3049D.F j) 1

@[expose] noncomputable def PB (k i : Nat) : Nat := pg 8 (mask 8) (Certificates.Tw3049P.F k) i

@[expose] noncomputable def V (k : Nat) : Nat := (PB k 0 * 256 + PB k 1) * 256 + PB k 2

@[expose] noncomputable def W (k : Nat) : Nat := PB k 3 * 256 + PB k 4

end CertificateChecks.Tower3049

end

module

public import Certificates.Kernel.Misc.Perm.LeftOrbCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYM12Data
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYM12Data
public import Std.Data.HashMap

public section

namespace CertificateChecks.KernelHSStd.M12Fy

open CFSG.EvenSporadicStandard.HSStd.FiveY CFSG.KS.RawGen

meta def ptsOf (gs : Array (Array Nat)) : Array (Array Nat) := (CFSG.KC.LeftOrbGen.search 12 6 gs).1

meta def clsOf (r : Array Nat) : Array (Array Nat) := (CFSG.KC.ConjOrbGen.search 12 6 m12Gens r).1

meta def posIn (L : Array (Array Nat)) : Std.HashMap (Array Nat) Nat := Id.run do
  let mut m : Std.HashMap (Array Nat) Nat := {}
  for i in [0:L.size] do
    m := m.insert L[i]! i
  return m

meta def chunks (k : Nat) (a : Array Nat) : Array (Array Nat) :=
  (Array.range ((a.size + k - 1) / k)).map fun j => a.extract (k * j) (k * j + k)

meta def coverW : Array (Array Nat) :=
  let maps := #[posIn (clsOf m12Inv0), posIn (clsOf m12Inv1)]
  let e := Array.range 12
  chunks 16 ((ptsOf m12Gens).map fun x =>
    if x != e && comp 12 x x == e then
      ((Array.range 2).findSome? fun o => (maps[o]!.get? x).map (o * 1024 + ·)).getD 0
    else 0)

meta def commW : Array (Array Nat) :=
  let cs := ptsOf m12CGens
  let dm := posIn (ptsOf m12DGens)
  cs.map fun a => #[pack 6 (cs.map fun b =>
    dm.getD (comp 12 (comp 12 a b) (comp 12 (inv 12 a) (inv 12 b))) 0)]

meta def dW : Array (Array Nat) :=
  let qm := posIn (clsOf m12Inv0)
  let e := Array.range 12
  (ptsOf m12DGens).map fun d =>
    #[if comp 12 d d == e then qm.getD (comp 12 m12Inv0 d) 0 else 0]

meta def cM : Array (Array Nat) :=
  let mm := posIn (ptsOf m12Gens)
  m12CGens.map fun g => #[mm.getD g 0]

end CertificateChecks.KernelHSStd.M12Fy

end

set_option maxRecDepth 400000

#left_orb CertificateChecks.KernelHSStd.M12Fy.M CFSG.EvenSporadicStandard.HSStd.FiveY.m12Gens 12 6
  CFSG.EvenSporadicStandard.HSStd.FiveY.m12Keys 1440
#left_orb CertificateChecks.KernelHSStd.M12Fy.C CFSG.EvenSporadicStandard.HSStd.FiveY.m12CGens 12 6
  CFSG.EvenSporadicStandard.HSStd.FiveY.m12Keys 240
#left_orb CertificateChecks.KernelHSStd.M12Fy.D CFSG.EvenSporadicStandard.HSStd.FiveY.m12DGens 12 6
  CFSG.EvenSporadicStandard.HSStd.FiveY.m12Keys 60
#conj_orb CertificateChecks.KernelHSStd.M12Fy.Q0 CFSG.EvenSporadicStandard.HSStd.FiveY.m12Gens 12 6
  CFSG.EvenSporadicStandard.HSStd.FiveY.m12Keys 396
  roots CFSG.EvenSporadicStandard.HSStd.FiveY.m12Inv0 gens 2
#conj_orb CertificateChecks.KernelHSStd.M12Fy.Q1 CFSG.EvenSporadicStandard.HSStd.FiveY.m12Gens 12 6
  CFSG.EvenSporadicStandard.HSStd.FiveY.m12Keys 495
  roots CFSG.EvenSporadicStandard.HSStd.FiveY.m12Inv1 gens 2

#kmisc_packarrs CertificateChecks.KernelHSStd.M12Fy.W CertificateChecks.KernelHSStd.M12Fy.coverW 11
#kmisc_packarrs CertificateChecks.KernelHSStd.M12Fy.CW CertificateChecks.KernelHSStd.M12Fy.commW 1440
#kmisc_packarrs CertificateChecks.KernelHSStd.M12Fy.DW CertificateChecks.KernelHSStd.M12Fy.dW 16
#kmisc_packarrs CertificateChecks.KernelHSStd.M12Fy.CM CertificateChecks.KernelHSStd.M12Fy.cM 32

module

public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.RowsWCmd
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.CFSGNative.He.Certificate
public meta import Certificates.Data.CFSGNative.He.Certificate

public section

set_option maxRecDepth 400000

#ks_chars CFSG.KD.HeOrb.SA CFSG.Sporadic.He.Native.seedA
#ks_chars CFSG.KD.HeOrb.SB CFSG.Sporadic.He.Native.seedB
#ks_chars CFSG.KD.HeOrb.RD CFSG.Sporadic.He.Native.rootDigits

namespace CFSG.KD.HeOrb

open CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native

meta def orbM : VOrbit := orbitData ()

meta def laneRow (v : Array Nat) : Nat :=
  ((List.range v.size).map fun j => v[j]! <<< (12 * j)).foldl (· ||| ·) 0

meta def trRows (M : Array (Array Nat)) : Array Nat :=
  (Array.range 50).map fun i => laneRow ((Array.range 50).map fun j => M[j]![i]!)

meta def ptM : Array Nat := orbM.keys.map laneRow
meta def alM : Array Nat := orbM.alpha.map (·.toNat)
meta def beM : Array Nat := orbM.beta.map (·.toNat)
meta def paM : Array Nat := orbM.par.map (·.toNat)
meta def laM : Array Nat := orbM.lab.map (·.toNat)

meta def soM : Array Nat := ((List.range 8330).toArray.qsort fun i j => ptM[i]! < ptM[j]!)

meta def taM : Array Nat := trRows (matA ())
meta def tbM : Array Nat := trRows (matB ())

end CFSG.KD.HeOrb

#krowsw CFSG.KD.HeOrb.PT 600 CFSG.KD.HeOrb.ptM
#krows CFSG.KD.HeOrb.AL CFSG.KD.HeOrb.alM
#krows CFSG.KD.HeOrb.BE CFSG.KD.HeOrb.beM
#krows CFSG.KD.HeOrb.PA CFSG.KD.HeOrb.paM
#krows CFSG.KD.HeOrb.LA CFSG.KD.HeOrb.laM
#krows CFSG.KD.HeOrb.SO CFSG.KD.HeOrb.soM
#krowsw CFSG.KD.HeOrb.TAR 600 CFSG.KD.HeOrb.taM
#krowsw CFSG.KD.HeOrb.TBR 600 CFSG.KD.HeOrb.tbM

namespace CFSG.KD.HeOrb

@[expose] noncomputable def TA : Nat :=
  Nat.lor (TAR (nat_lit 0)) (Nat.shiftLeft (TAR (nat_lit 1)) (nat_lit 19200))

@[expose] noncomputable def TB : Nat :=
  Nat.lor (TBR (nat_lit 0)) (Nat.shiftLeft (TBR (nat_lit 1)) (nat_lit 19200))

@[expose] def R : List Nat := [5, 6, 5, 0, 6, 4, 0, 2, 6, 5, 6, 2, 4, 1, 6, 4, 2, 6, 1, 0, 6, 0,
  6, 0, 5, 4, 4, 4, 4, 5, 5, 0, 6, 0, 3, 6, 6, 4, 0, 1, 5, 4, 5, 3, 4, 4, 4, 2, 2, 1]

end CFSG.KD.HeOrb

end

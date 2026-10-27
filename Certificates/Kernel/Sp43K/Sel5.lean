module

public import Certificates.Data.Kernel.Sp43KSyl
public import Certificates.Data.Sp43.Check
public import Certificates.Kernel.Sp43K.Data5
public import Certificates.Kernel.Sp43K.Data2
public import Certificates.Kernel.Sp43K.Data4
public import Certificates.Kernel.Sp43K.Sel

public section

namespace CFSG.KD.Sp43K

open CFSG.KC.Sp43K CFSG.Sp43.Native

@[expose] noncomputable def sylC (j : Nat) : Bool :=
  let k := if j == 0 then 0 else
    let r := dO.getD (162 * j - 1) (0, 0)
    keyT (gA 0) r.1 r.2
  dO.length == 1296 && sylGo (gA 0) ((dO.drop (162 * j)).take 162) k

@[expose] noncomputable def fixC : Bool :=
  ((List.range 81).filter fun v => vecC (toCT p0.1) v == v && vecC (toCT p0.2) v == v) ==
    [0, 3, negV 3]

@[expose] noncomputable def noEigC : Bool :=
  (List.range 40).all fun i =>
    let c := fldT nP i
    c == oneT || c == oneT <<< 16 || noEigOK (toCT c)

end CFSG.KD.Sp43K

end

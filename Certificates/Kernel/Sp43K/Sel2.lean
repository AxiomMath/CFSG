module

public import Certificates.Data.Kernel.Sp43KOrb
public import Certificates.Kernel.Sp43K.Sel
public import Certificates.Kernel.Sp43K.Data2

public section

namespace CFSG.KD.Sp43K

open CFSG.KC.Sp43K

@[expose] def nT : Nat := 6560

@[expose] noncomputable def g5C : Bool :=
  okT G5.1 && okT G5.2.1 && okT G5.2.2.1 && okT G5.2.2.2 &&
    mulT G5.1 G5.2.2.1 == oneT && mulT G5.2.1 G5.2.2.2 == oneT

@[expose] noncomputable def tC (j : Nat) : Bool :=
  let s := 656 * j
  tGo G5.1 G5.2.1 G5.2.2.1 G5.2.2.2 nT TP (min (s + 656) nT) ((TQ.drop s).take 656) s

@[expose] noncomputable def p0C : Bool :=
  lstK p0.1 p0.2 81 p0P p0D 0 81 p0R && p0T.length == 81 && inGo p0P nT TP p0T 0

@[expose] noncomputable def wdC : Bool :=
  wordT G5.1 G5.2.1 (wd.getD 0 []) == p0.1 && wordT G5.1 G5.2.1 (wd.getD 1 []) == p0.2 &&
    wordT G5.1 G5.2.1 (wd.getD 2 []) == gA 4 && wordT G5.1 G5.2.1 (wd.getD 3 []) == gB 4

@[expose] noncomputable def xP : Nat → Nat
  | 0 => x0P | 1 => x1P | 2 => x2P | 3 => x3P | 4 => x4P | _ => 0

@[expose] noncomputable def oD : Nat → Nat
  | 0 => o0D | 1 => o1D | 2 => o2D | 3 => o3D | 4 => o4D | _ => 0

@[expose] noncomputable def oR : Nat → List (Nat × Nat)
  | 0 => o0R | 1 => o1R | 2 => o2R | 3 => o3R | 4 => o4R | _ => []

@[expose] noncomputable def orbPart (i s : Nat) : Bool :=
  let n := ns.getD i ((0, 0), (0, 0))
  oGo n.1.1 n.1.2 n.2.1 n.2.2 (ords.getD i 0) (mP i) (nr.getD i 0) (xP i) nT TP (oD i)
    (min (s + 656) nT) (((oR i).drop s).take 656) s

@[expose] noncomputable def orbC (j : Nat) : Bool := orbPart (j / 10) (656 * (j % 10))

end CFSG.KD.Sp43K

end

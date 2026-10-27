module

public import Certificates.Data.Kernel.Sp43KList
public import Certificates.Kernel.Sp43K.Data

public section

namespace CFSG.KD.Sp43K

open CFSG.KC.Sp43K

@[expose] noncomputable def mP : Nat → Nat
  | 0 => m0P | 1 => m1P | 2 => m2P | 3 => m3P | 4 => m4P | _ => 0

@[expose] noncomputable def mD : Nat → Nat
  | 0 => m0D | 1 => m1D | 2 => m2D | 3 => m3D | 4 => m4D | _ => 0

@[expose] noncomputable def mR : Nat → List (Nat × Nat × Nat × Nat)
  | 0 => m0R | 1 => m1R | 2 => m2R | 3 => m3R | 4 => m4R | _ => []

@[expose] def ords : List Nat := [5, 120, 120, 720, 1920]

@[expose] noncomputable def gA (i : Nat) : Nat := (g.getD i (0, 0)).1

@[expose] noncomputable def gB (i : Nat) : Nat := (g.getD i (0, 0)).2

@[expose] def jobs : List (Nat × Nat) :=
  [(0, 0), (1, 0), (2, 0), (3, 0), (3, 128), (3, 256), (3, 384), (3, 512), (3, 640),
    (4, 0), (4, 128), (4, 256), (4, 384), (4, 512), (4, 640), (4, 768), (4, 896), (4, 1024),
    (4, 1152), (4, 1280), (4, 1408), (4, 1536), (4, 1664), (4, 1792)]

@[expose] noncomputable def memPart (i s : Nat) : Bool :=
  let n := ords.getD i 0
  lstK (gA i) (gB i) n (mP i) (mD i) s (min (s + 128) n) (((mR i).drop s).take 128)

@[expose] noncomputable def memC (j : Nat) : Bool :=
  let p := jobs.getD j (0, 0)
  memPart p.1 p.2

@[expose] def normK (n : (Nat × Nat) × (Nat × Nat)) (q : Nat × Nat × Nat × Nat) (P k a b : Nat) :
    Bool :=
  okT n.1.1 && okT n.1.2 && okT n.2.1 && okT n.2.2 &&
    mulT n.1.1 n.1.2 == oneT && mulT n.2.1 n.2.2 == oneT &&
    decide (q.1 < k) && fldT P q.1 == mulT (mulT n.1.1 a) n.1.2 &&
    decide (q.2.1 < k) && fldT P q.2.1 == mulT (mulT n.1.1 b) n.1.2 &&
    decide (q.2.2.1 < k) && fldT P q.2.2.1 == mulT (mulT n.2.1 a) n.2.2 &&
    decide (q.2.2.2 < k) && fldT P q.2.2.2 == mulT (mulT n.2.1 b) n.2.2

@[expose] noncomputable def normC (i : Nat) : Bool :=
  normK (ns.getD i ((0, 0), (0, 0))) (nq.getD i (0, 0, 0, 0)) (mP i) (ords.getD i 0) (gA i) (gB i)

end CFSG.KD.Sp43K

end

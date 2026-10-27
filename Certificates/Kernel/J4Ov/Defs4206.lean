module

public import Certificates.Kernel.J4Ov.Data4206
public import Certificates.Kernel.J4Q.MatData
public import Certificates.Kernel.J4Q.QTData
public import Certificates.Kernel.J4Q.MaskData
public import Certificates.Data.Kernel.J4Q.VOrb
public import Certificates.Data.Kernel.J4Q.Runs

public section

namespace CertificateChecks.KernelJ4Ov

open CFSG.KC.J4Q CFSG.KC.LQT.Syl CFSG.KD.J4Ov
open CFSG.KD.J4Q (c rm one A B L0 L1 L2 U0 mkKM_0 mkKM_1 mkKM_2 mkKM_3)

@[expose] noncomputable def chT (t : Nat) : List (List Nat) := F.getD t []

@[expose] noncomputable def ptsT (t : Nat) : List Nat := vptsK rm (RT.getD t 0) (chT t).flatten

@[expose] noncomputable def trTI (t i : Nat) : Bool :=
  vtChunkK rm R (ptsT t) ((chT t).getD i []) ((PP.getD t []).getD i 0) (1 + 1024 * i)

@[expose] noncomputable def tr4206 (g : Nat) : Bool := trTI (g / 8) (g % 8)

@[expose] noncomputable def tr4206B (g : Nat) : Bool := tr4206 (g + 224)

@[expose] noncomputable def pcT (t i : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [RT.getD t 0]
    (fun j _ => List.map (fun e => Nat.land e rm) ((chT t).getD j [])) i

@[expose] noncomputable def so4206 (g : Nat) : Bool :=
  eqLK (sortN (pcT (g / 9) (g % 9))) ((SC.getD (g / 9) []).getD (g % 9) [])

@[expose] noncomputable def runsK (lo n : Nat) : List (List Nat) :=
  List.flatten (List.map (fun t => SC.getD t []) (List.range' lo n))

@[expose] noncomputable def distK (lo n cap : Nat) : Bool :=
  andB (sincK (mergeRunsK (runsK lo n)) 0) (Nat.beq (runsK lo n).flatten.length cap)

@[expose] noncomputable def shape4206 : Bool :=
  andB (Nat.beq F.length 49) (andB (Nat.beq PP.length 49) (andB (Nat.beq SC.length 49)
  (andB (Nat.beq RT.length 49) (andB (Nat.beq W.length 49) (andB (Nat.beq LS.length 49)
  (allR 49 fun t => andB (Nat.ble (chT t).length 8)
    (andB (Nat.beq (PP.getD t []).length (chT t).length)
    (andB (Nat.beq (SC.getD t []).length (Nat.succ (chT t).length))
    (andB (Nat.beq (LS.getD t 0) (Bool.rec (motive := fun _ => Nat) 6 5 (Nat.blt t 28)))
      (allR (Nat.sub (chT t).length 1) fun i => Nat.beq ((chT t).getD i []).length 1024))))))))))

@[expose] noncomputable def letMs : List Nat := [mkKM_0, mkKM_1, mkKM_2, mulJ c rm mkKM_3 U0]

@[expose] noncomputable def lettersK : Bool :=
  andB (Nat.beq R.length 4) (allR 4 fun n => eqLK (R.getD n []) (rowsOfJ rm (getN one letMs n)))

@[expose] noncomputable def rootsK : Bool :=
  allR 49 fun t => Nat.beq (RT.getD t 0) (pathVK rm one [L0, L1, L2] (W.getD t [])
    (pathVK rm one [A, B] (KP.getD (Nat.sub (LS.getD t 0) 5) []) R0))

end CertificateChecks.KernelJ4Ov

end

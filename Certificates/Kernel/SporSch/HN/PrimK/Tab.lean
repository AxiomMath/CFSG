module

public import Certificates.Kernel.SporSch.HN.Prim2104Data
public import Certificates.Data.Kernel.SporSch.HNXSub
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_items_root CFSG.KD.HNXK.PRIMC
  "Certificates/Kernel/SporSch/HN/data/hnx_primc.bin" 272 7119952903687249692

public noncomputable section

namespace CFSG.KD.HNXK

open CFSG.KC.LL.HNX CFSG.KD.LgHNX CFSG.KD.HNPrim

@[expose] def imgOk (k : Nat) : Bool := imgRange TX UT CM3 M TR1 CFSG.KD.OrdHN.ONE 21 (47 * k) 47

@[expose] def orbOk (k : Nat) : Bool := orbRange UT REPS (47 * k) 47

@[expose] def eqOk (k : Nat) : Bool := eqRange TX UT (47 * k) 47

@[expose] def primLen (k : Nat) : Nat := nIf(Nat.blt k 7, 2256, 2021)

@[expose] def cntOk (k : Nat) : Bool := Nat.beq (cntSum UT (2256 * k) (primLen k)) (PRIMC k)

end CFSG.KD.HNXK

end

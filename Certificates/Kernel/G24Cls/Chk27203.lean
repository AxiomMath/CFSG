module

public import Certificates.Kernel.G24Cls.Text27203
public import Certificates.Kernel.G24Cls.Pack27203
public import Certificates.Kernel.G24Tri.Text27206
public import Certificates.Kernel.G24Tri.Pack27206
public import Certificates.Kernel.G24Tri.Chain27206
public import Certificates.Data.Kernel.G24Key
public import Certificates.Data.Kernel.DigitScan
public import Certificates.Data.Kernel.G24Tri
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CertificateChecks.KernelG24.Cls27203

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.G24Tri CFSG.KC.G24Key
  CFSG.KC.DigitScan CertificateChecks.KernelG24.Tri27206

@[expose] noncomputable def xyS (l : Nat) : Nat := LC.S (Nat.land l (nat_lit 1))

@[expose] noncomputable def xySI (l : Nat) : Nat := LC.SI (Nat.land l (nat_lit 1))

@[expose] noncomputable def gT (l : Nat) : Nat := RG (Nat.land l (nat_lit 7))

@[expose] noncomputable def keyLa (k : Nat) : Nat := keyK xyS xySI PLa GLa (nat_lit 24) (PK 6) k

@[expose] noncomputable def keyLb (k : Nat) : Nat :=
  keyK xyS xySI PLb GLb (nat_lit 19) (LC.S 0) k

@[expose] noncomputable def keyT (k : Nat) : Nat := tw (nat_lit 33) (nat_lit 8589934591) KY k

@[expose] noncomputable def fCls (i v : Nat) : Bool :=
  bIf(Nat.blt i (nat_lit 8192), true,
  bIf(Nat.blt i (nat_lit 19112), strictB (Nat.sub i (nat_lit 8192)) (fun t =>
      Nat.beq v (ap (RG (Nat.div t (nat_lit 1365))) (Nat.mod t (nat_lit 1365)))),
  bIf(Nat.blt i (nat_lit 23207), Nat.ble v (Nat.sub i (nat_lit 19112)),
  bIf(Nat.blt i (nat_lit 27302), Nat.blt v (nat_lit 8), true))))

@[expose] noncomputable def fLa (i v : Nat) : Bool :=
  bIf(Nat.blt i (nat_lit 1365), true,
  bIf(Nat.blt i (nat_lit 5459), strictB (Nat.sub i (nat_lit 1365)) (fun k =>
      bAnd(Nat.ble v k, Nat.beq v (t12 PLa k))),
  bIf(Nat.blt i (nat_lit 9553), strictB (Nat.sub i (nat_lit 5459)) (fun k =>
      bAnd(Nat.blt v (nat_lit 2), Nat.beq v (t12 GLa k))),
  true)))

theorem kTextC : scanK fCls (nat_lit 72575) CT.chars = true := by quickRfl
theorem kTextL : scanK fLa (nat_lit 19108) LT.chars = true := by quickRfl
theorem kRoot : rootK PLa (nat_lit 24) (nat_lit 4095) = true := by quickRfl
theorem kLa : sortedK keyLa OLa (nat_lit 4095) = true := by quickRfl
theorem kLb : sortedK keyLb OLb (nat_lit 4096) = true := by quickRfl
theorem kTree : treeK gT TP TG (nat_lit 8) keyT (nat_lit 4096) = true := by quickRfl
theorem kClos : closK gT (nat_lit 8) keyT CL (nat_lit 4096) = true := by quickRfl
theorem kInc : sortedK keyT OT (nat_lit 4096) = true := by quickRfl
theorem kRec : allN (nat_lit 4096) (fun k =>
    recK gT TP TG (nat_lit 8) keyT (LC.S 0) (LC.SI 1) (PK 6) (LC.S 0) k (REC k)) = true := by
  quickRfl
theorem kCan : (allN 8 (fun j => canonK 1365 11 (mask 11) (1365 * 11) (RG j)) &&
    allN 2 (fun i => canonK 1365 11 (mask 11) (1365 * 11) (C35 i))) = true := by quickRfl
theorem kInv : allN 8 (fun j => invEqK 1365 11 (mask 11) (1365 * 11) (RG j) (RGI j)) = true := by
  quickRfl
theorem kSift : (allN 8 (fun j =>
      siftK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) LC.LR LC.TRI LC.BP 3 0 (RG j)) &&
    allN 2 (fun i =>
      siftK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) LC.LR LC.TRI LC.BP 3 0 (C35 i)) &&
    siftK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) LC.LR LC.TRI LC.BP 3 0 (PK 6)) = true := by
  quickRfl
theorem kOrd : (ordAuxK (C35 0) 2 (C35 0) && ordAuxK (C35 1) 4 (C35 1) &&
    ordAuxK (PK 6) 1 (PK 6)) = true := by quickRfl
theorem kCent : (allN 8 (fun j => commB (RG j) (PK 6)) &&
    allN 2 (fun i => commB (C35 i) (PK 6))) = true := by quickRfl

end CertificateChecks.KernelG24.Cls27203

end

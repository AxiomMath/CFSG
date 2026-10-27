module

public import Certificates.Kernel.Sporadic.Fi22.HypCB
public meta import Certificates.Kernel.Sporadic.Fi22.HypCB
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Inputs
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22W

open CFSG.EvenSporadicStandard.HypOne.Fi22

meta def tabsM : Array (Array Nat) :=
  let u := CFSG.Monster.B.Fischer.fi22GraphOuterArr
  let z : Nat → Array Nat := fun k =>
    if k < 3 then (zT k).map (·.toNat) else CFSG.Sporadic.FischerOddCore.fi22ExtArr (21 + k)
  ((List.range 6).map fun k => Fi22CB.compA (z k) u).toArray ++
    ((List.range 3).map fun i => (lT (3 + i)).map (·.toNat)).toArray

end CertificateChecks.KernelSpor.Fi22W

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22WT CertificateChecks.KernelSpor.Fi22W.tabsM 12

namespace CertificateChecks.KernelSpor.Fi22W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.CommBase

@[expose] noncomputable def zOK (P T : Nat) : Bool :=
  bAnd(Fi22X.cn P,
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) P (Fi22X.inv P),
  bAnd(Fi22X.siftP P,
  Nat.beq (Fi22X.c (Fi22X.c P Fi22X.GO) T) (Fi22X.c T (Fi22X.c P Fi22X.GO)))))

@[expose] noncomputable def commP (L T : Nat) : Nat :=
  Fi22X.c (Fi22X.c (Fi22X.c L T) (Fi22X.inv L)) (Fi22X.inv T)

@[expose] noncomputable def invoOK (C : Nat) : Bool :=
  bAnd(notB (allN 3510 (fun x => Nat.beq (pg 12 (mask 12) C x) x)),
  Nat.beq (Fi22X.c C C) (pidn 3510 12))

@[expose] noncomputable def foursOK (L T : Nat) : Bool :=
  bAnd(Fi22X.cn L,
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) L (Fi22X.inv L),
  bAnd(permOK 3510 12 (mask 12) (3510 * 12) T (Fi22X.inv T),
  bAnd(Fi22X.siftP L, invoOK (commP L T)))))

theorem zAll : allN 6 (fun k => zOK (Fi22WT k) (Fi22ExtT.L (21 + k))) = true := by quickRfl

theorem foursAll : allN 3 (fun i => foursOK (Fi22WT (6 + i)) (Fi22ExtT.L (24 + i))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22W

end

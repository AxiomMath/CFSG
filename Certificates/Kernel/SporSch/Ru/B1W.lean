module

public import Certificates.Kernel.SporSch.Ru.B1E
public import Certificates.Kernel.SporSch.Ru.SChain4060
public import Certificates.Data.Kernel.SporSch.RuDist
meta import Certificates.Data.GMS78RuB1Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuB1K

open CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.RuB1 CFSG.Monster.B.Co2.Native

meta def wsM : Array (Array Nat) := (e8W.map fun q => q.2.1).toArray

meta def wsiM : Array (Array Nat) := (e8W.map fun q => q.2.2).toArray

end CertificateChecks.KernelSporSch.RuB1K

#kss_perms CertificateChecks.KernelSporSch.RuB1K.WS 12 CertificateChecks.KernelSporSch.RuB1K.wsM
#kss_perms CertificateChecks.KernelSporSch.RuB1K.WSI 12 CertificateChecks.KernelSporSch.RuB1K.wsiM

namespace CertificateChecks.KernelSporSch.RuB1K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.RuB1 CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def wok (i : Nat) : Bool :=
  bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) SG SGI 4 (dword e8ConjWords 0 i) (WS i),
    permOK 4060 12 (mask 12) (4060 * 12) (WS i) (WSI i))

theorem wsOK : allN 24 wok = true := by quickRfl

@[expose] noncomputable def bigP (k : Nat) : Nat :=
  nIf(Nat.blt k 7, EA k, XA (List.getD e8BigIdx (Nat.sub k 7) 0))

@[expose] noncomputable def invP (G : Nat) : Bool :=
  bAnd(Nat.beq (pcomp 4060 12 (mask 12) G G) (pidn 4060 12),
    bIf(Nat.beq G (pidn 4060 12), false, true))

@[expose] noncomputable def bigQ (G : Nat) : Bool :=
  bIf(allN 15 (fun k => bIf(Nat.beq G (bigP k), false, true)), false, true)

@[expose] noncomputable def wconj (i G : Nat) : Nat :=
  pcomp 4060 12 (mask 12) (pcomp 4060 12 (mask 12) (WS i) G) (WSI i)

@[expose] noncomputable def nConj (G : Nat) : Nat :=
  distNL ((List.range 24).map fun i => wconj i G)

@[expose] noncomputable def e8pK (G : Nat) : Bool :=
  bIf(invP G, bIf(bigQ G, true, Nat.ble 9 (nConj G)), true)

@[expose] noncomputable def e8row (a : Nat) : Bool :=
  row2K 4060 12 (mask 12) (4060 * 12) RuS4.LR RuS4.TR e8pK a

end CertificateChecks.KernelSporSch.RuB1K

end

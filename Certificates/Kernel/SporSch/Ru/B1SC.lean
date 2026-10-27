module

public import Certificates.Kernel.SporSch.Ru.B1X
public import Certificates.Data.GMS78RuB1SCCheck
meta import Certificates.Data.GMS78RuB1SCCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuB1K

open CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.RuB1 CFSG.Monster.B.Co2.Native

meta def slM : Array (Array Nat) := (scWords.map scL).toArray

meta def sliM : Array (Array Nat) := (scWords.map fun w => ruInv (scL w)).toArray

meta def seM : Array (Array Nat) := scEs.toArray.foldl (fun acc E => acc ++ E) #[]

end CertificateChecks.KernelSporSch.RuB1K

#kss_perms CertificateChecks.KernelSporSch.RuB1K.SL 12 CertificateChecks.KernelSporSch.RuB1K.slM
#kss_perms CertificateChecks.KernelSporSch.RuB1K.SLI 12 CertificateChecks.KernelSporSch.RuB1K.sliM
#kss_perms CertificateChecks.KernelSporSch.RuB1K.SE 12 CertificateChecks.KernelSporSch.RuB1K.seM

namespace CertificateChecks.KernelSporSch.RuB1K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.RuSchreier.RuB1 CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def g4 (j : Nat) : Nat := List.getD [C0, C1, Ns0, Ns1] j 0

@[expose] noncomputable def g4i (j : Nat) : Nat := List.getD [C0I, C1I, Ns0I, Ns1I] j 0

@[expose] noncomputable def slok (k : Nat) : Bool :=
  bAnd(wordEqK 4060 12 (mask 12) (pidn 4060 12) g4 g4i 4 (dword scWords 0 k) (SL k),
    permOK 4060 12 (mask 12) (4060 * 12) (SL k) (SLI k))

@[expose] noncomputable def seok (j : Nat) : Bool :=
  bAnd(Nat.beq (pc (pc (SL (Nat.div j 7)) (EA (Nat.mod j 7))) (SLI (Nat.div j 7))) (SE j),
    canonK 4060 12 (mask 12) (4060 * 12) (SE j))

@[expose] noncomputable def sesift (j : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight (SE j) (4060 * 12)) 0,
    siftK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) RuS4.LR RuS4.TRI RuS4.BP 2 0 (SE j))

@[expose] noncomputable def cm4 (G X : Nat) : Bool := Nat.beq (pc G X) (pc X G)

@[expose] noncomputable def scpK (G : Nat) : Bool :=
  bIf(Nat.beq (pc G G) (pidn 4060 12),
    bIf(allN 7 (fun j => cm4 G (EA j)), true,
      anyK 12 (fun k => allN 7 (fun i => cm4 G (SE (Nat.add (Nat.mul 7 k) i))))), true)

@[expose] noncomputable def scrow (a : Nat) : Bool :=
  row2K 4060 12 (mask 12) (4060 * 12) RuS4.LR RuS4.TR scpK a

end CertificateChecks.KernelSporSch.RuB1K

#kss_each CertificateChecks.KernelSporSch.RuB1K.SLC CertificateChecks.KernelSporSch.RuB1K.slok 12
#kss_each CertificateChecks.KernelSporSch.RuB1K.SEC CertificateChecks.KernelSporSch.RuB1K.seok 84
#kss_each CertificateChecks.KernelSporSch.RuB1K.SES CertificateChecks.KernelSporSch.RuB1K.sesift 84

end

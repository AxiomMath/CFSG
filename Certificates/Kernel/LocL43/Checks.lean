module

public import Certificates.Kernel.LocL43.Data
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocL43Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.GroupTheory.Perm.Basic
public import Std.Data.HashMap

public section

set_option maxRecDepth 400000

#kc_each CertificateChecks.KernelLocL43.l43Pt 0 8

#kc_each CertificateChecks.KernelLocL43.l43Fl 0 8

#kc_each CertificateChecks.KernelLocL43.l43Pr 0 40

namespace CertificateChecks.KernelLocL43

open CFSG.KD.LocLn CFSG.KC.Enum CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc

theorem kit4 : kitOK k4 = true := by quickRfl

theorem o8B : ((List.range 512).filter (fun i => Nat.beq (Nat.mod (F i) 2) 1) ==
    (List.range 160).map O8) = true := by
  quickRfl

theorem o2B : ((List.range 512).filter (fun i => Nat.beq (Nat.div (F i) 2) 1) ==
    (List.range 119).map O2) = true := by
  quickRfl

@[expose] noncomputable def repAt (i : Nat) (r : LocRep) : Bool :=
  bAnd(codeN k4 r.x (RX i), bAnd(codeN k4 r.t (RT i),
    strictB (pkL r.g₁.toList) fun G1 => strictB (pkL r.g₂.toList) fun G2 =>
    bAnd(codeN k4 r.g₁ G1, bAnd(codeN k4 r.g₂ G2,
      repN k4 (RX i) (RT i) G1 G2 r.wa r.wb r.ma r.mb r.j))))

@[expose] noncomputable def l43Rp (q : Nat) : Bool :=
  allBlk (Nat.mul 8 q) (fun i => strictB i fun i =>
    bIf(Nat.blt i 38, repAt i l43Data.reps[i]!, true)) 8

end CertificateChecks.KernelLocL43

#kc_each CertificateChecks.KernelLocL43.l43Rp 0 5

namespace CertificateChecks.KernelLocL43

open CFSG.KD.LocLn CFSG.KC.Enum CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc

theorem gensB : (Nat.beq l43Data.gens.size 4 && allBlk 0
    (fun k => bAnd(codeN k4 l43Data.gens[k]! (G k), validN k4 (G k))) 4) = true := by
  quickRfl

theorem repsSize : l43Data.reps.size = 38 := by decide +kernel

theorem fuelK : l43Data.fuel = 600 ∧ l43Data.k = 9 := by decide +kernel

theorem inF4B : (l43Data.reps.toList.all fun r => inF4 r.g₁ && inF4 r.g₂) = true := by
  decide +kernel

end CertificateChecks.KernelLocL43

end

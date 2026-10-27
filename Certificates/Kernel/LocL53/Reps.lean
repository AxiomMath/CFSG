module

public import Certificates.Kernel.LocL53.Data
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocL53Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.GroupTheory.Perm.Basic
public import Std.Data.HashMap

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLocL53

open CFSG.KD.LocLn CFSG.KC.Enum CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc

@[expose] noncomputable def repAt (i : Nat) (r : LocRep) : Bool :=
  bAnd(codeN k5 r.x (RX i), bAnd(codeN k5 r.t (RT i),
    strictB (pkL r.g₁.toList) fun G1 => strictB (pkL r.g₂.toList) fun G2 =>
    bAnd(codeN k5 r.g₁ G1, bAnd(codeN k5 r.g₂ G2,
      repN k5 (RX i) (RT i) G1 G2 r.wa r.wb r.ma r.mb r.j))))

@[expose] noncomputable def l53Rp (q : Nat) : Bool :=
  CFSG.KC.Enum.allBlk (Nat.mul 8 q) (fun i => CFSG.KC.Enum.strictB i fun i =>
    bIf(Nat.blt i 67, repAt i l53Data.reps[i]!, true)) 8

end CertificateChecks.KernelLocL53

#kc_each CertificateChecks.KernelLocL53.l53Rp 0 9

namespace CertificateChecks.KernelLocL53

open CFSG.KD.LocLn CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc

theorem gensB : (Nat.beq l53Data.gens.size 7 && CFSG.KC.Enum.allBlk 0
    (fun k => bAnd(codeN k5 l53Data.gens[k]! (G k), validN k5 (G k))) 7) = true := by
  quickRfl

theorem repsSize : l53Data.reps.size = 67 := by decide +kernel

theorem fuelK : l53Data.fuel = 1200 ∧ l53Data.k = 10 := by decide +kernel

end CertificateChecks.KernelLocL53

end

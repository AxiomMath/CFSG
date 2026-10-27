module

public import Certificates.Kernel.OmegaEight.SA3002K
public import Certificates.Data.Foote82OmegaEight
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEightMinus
open CFSG.CGT.Foote82.OmegaEight (eichRefl witTypes witWords)

@[expose] noncomputable def transCK (c : Nat) : Nat :=
  CFSG.KLie.CT.orN (nat_lit 136) fun i =>
    Nat.shiftLeft (nsMap NSM NIM (transK true c) i) (Nat.mul (nat_lit 8) i)

@[expose] noncomputable def transOK (c P : Nat) : Bool :=
  bAnd(cnM P, bAnd(allN 136 (fun i => Nat.blt (pg 8 (mask 8) P i) 136),
    allN 136 fun i => Nat.beq (at8 P i) (at8 NIM (transK true c (at8 NSM i)))))

@[expose] noncomputable def prodK (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) pidM (fun c _ ih => pcM (transCK c) ih) cs

@[expose] noncomputable def allLK (cs : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(f c, ih)) cs

@[expose] noncomputable def typeZ (g z : Nat) : Bool :=
  bAnd(cnM g, bAnd(pmM g, bAnd(cnM (pinvM g), bAnd(cnM z,
    bAnd(Nat.beq (ppwM z 12) pidM, bAnd(cnM (ppwM z 2), bAnd(cnM (ppwM z 3),
    bAnd(bIf(Nat.beq (ppwM z 2) pidM, false, true), bIf(Nat.beq (ppwM z 3) pidM, false, true)))))))))

@[expose] noncomputable def typeK (y g : Nat) : Bool := typeZ g (pcM y (cjM g y))

theorem ch919009q : allN 256 (fun c => CFSG.KLie.CT.anyN 136 fun j =>
    Nat.beq (q8K true (Nat.xor (at8 NSM j) c)) 1) = true := by quickRfl

theorem ch919009t : allN 136 (fun j => (fun c => (fun P => bAnd(transOK c P,
    siftK 136 8 (mask 8) (136 * 8) (pidn 136 8) AQM.LR AQM.TRI AQM.BP 8 0 P)) (transCK c))
    (at8 NSM j)) = true := by quickRfl

theorem ch919009e : bAnd(allN 10 (fun i => bAnd(allLK (eichRefl.getD i []) (fun c =>
    bAnd(Nat.blt c 256, bAnd(Nat.beq (q8K true c) 1, transOK c (transCK c)))),
    Nat.beq (AM.S i) (prodK (eichRefl.getD i [])))),
    bAnd(transOK 64 (transCK 64), Nat.beq (AM.S 10) (transCK 64))) = true := by quickRfl

theorem ch919009w : allN 4 (fun k => bAnd(lettersK 18 (witWords.getD k []),
    typeK (mainKM (witTypes.getD k 0)) (wOM (witWords.getD k [])))) = true := by quickRfl

theorem ch919009r : Nat.beq (mainKM 3) (transCK 64) = true := by quickRfl

end CertificateChecks.KernelO8

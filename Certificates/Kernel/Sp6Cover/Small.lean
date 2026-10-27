module

public import Certificates.Kernel.Sp6Cover.YChain
public import Certificates.Kernel.Sp6Cover.CChain
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.MulH
meta import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Kernel.Sp6Cover.Data
meta import Certificates.Data.PhilipHallSp6Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSp6Cover

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData

meta def cvM (wd : List Nat) : Array Nat :=
  wd.foldl (fun a l => CFSG.KS.RawGen.comp 240 a cA[l - 1]!) (Array.range 240)

meta def eM : Array (Array Nat) :=
  let ws := ew.toArray.map cvM
  let id := Array.range 240
  let pw := fun (x : Array Nat) (k : Nat) =>
    (List.replicate k x).foldl (fun a y => CFSG.KS.RawGen.comp 240 a y) id
  let pel := (List.range 9).toArray.map fun k =>
    CFSG.KS.RawGen.comp 240 (pw ws[0]! (k / 3)) (pw ws[1]! (k % 3))
  #[tA, iA, jA, gA[0]!, gA[1]!, gA[2]!, CFSG.KS.RawGen.inv 240 gA[0]!,
    CFSG.KS.RawGen.inv 240 gA[1]!, CFSG.KS.RawGen.inv 240 gA[2]!, ws[0]!, ws[1]!, ws[2]!,
    CFSG.KS.RawGen.inv 240 ws[2]!, ws[3]!] ++ ws.extract 4 13 ++ pel

end CertificateChecks.KernelSp6Cover

#kmisc_packarrs CertificateChecks.KernelSp6Cover.E CertificateChecks.KernelSp6Cover.eM 8

namespace CertificateChecks.KernelSp6Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 240 8 (mask 8) p q

@[expose] noncomputable def idP : Nat := pidn 240 8

@[expose] noncomputable def cnK (p : Nat) : Bool := canonK 240 8 (mask 8) (240 * 8) p

@[expose] noncomputable def commK (p q : Nat) : Bool := Nat.beq (pc p q) (pc q p)

@[expose] noncomputable def neK (p q : Nat) : Bool := bIf(Nat.beq p q, false, true)

@[expose] noncomputable def cL (l : Nat) : Nat := CC.S (Nat.sub l 1)

@[expose] noncomputable def pL (l : Nat) : Nat := nIf(Nat.beq l 1, E 9, E 10)

@[expose] noncomputable def rL (l : Nat) : Nat := nIf(Nat.beq l 1, E 1, E 2)

@[expose] def pWord (k : Nat) : List Nat := List.replicate (k / 3) 1 ++ List.replicate (k % 3) 2

@[expose] noncomputable def siftY (P : Nat) : Bool :=
  siftK 240 8 (mask 8) (240 * 8) (pidn 240 8) YC.LR YC.TRI YC.BP 4 0 P

@[expose] noncomputable def disjK (c cI : Nat) : Bool :=
  allN 8 fun a => strictB (pc (pc c (E (24 + a))) cI) fun x => allN 8 fun b => neK x (E (24 + b))

@[expose] noncomputable def goodK (Y : Nat → Nat) : Bool :=
  allN 9 fun k => bIf(bAnd(commK (E (23 + k)) (E 1), commK (E (23 + k)) (E 2)), true,
    bAnd(commK (Y k) (E 1), bAnd(commK (Y k) (E 2), bIf(commK (E (23 + k)) (Y k), false, true))))

theorem ebind : tA = unpack 240 8 (E 0) ∧ iA = unpack 240 8 (E 1) ∧ jA = unpack 240 8 (E 2) ∧
    gA.size = 3 ∧ ∀ k < 3, gA[k]! = unpack 240 8 (E (3 + k)) := by
  decide +kernel

theorem canon : bAnd(allN 32 (fun k => cnK (E k)), bAnd(cnK idP,
    bAnd(CFSG.KS.Prim.idK 240 8 (mask 8),
    bAnd(szOK 240 8, allN 3 (fun k => bAnd(cnK (CC.S k), bAnd(cnK (CC.SI k),
      bAnd(cnK (YC.S k), cnK (YC.SI k))))))))) = true := by
  quickRfl

theorem invs : bAnd(allN 3 (fun k => invEqK 240 8 (mask 8) (240 * 8) (E (3 + k)) (E (6 + k))),
    invEqK 240 8 (mask 8) (240 * 8) (E 11) (E 12)) = true := by
  quickRfl

theorem words : bAnd(allN 3 (fun k =>
      Nat.beq (E (9 + k)) (wfoldK 240 8 (mask 8) cL (ew.getD k []) idP)),
    bAnd(Nat.beq (E 13) (wfoldK 240 8 (mask 8) cL (ew.getD 3 []) idP),
    allN 9 (fun k => Nat.beq (E (14 + k)) (wfoldK 240 8 (mask 8) cL (ew.getD (4 + k) []) idP)))) =
    true := by
  quickRfl

theorem letters : (ew.all fun wd => wd.all fun l => decide (1 ≤ l ∧ l ≤ 3)) = true ∧
    ew.length = 13 := by
  decide +kernel

theorem pels : allN 9 (fun k => Nat.beq (E (23 + k)) (wfoldK 240 8 (mask 8) pL (pWord k) idP)) =
    true := by
  quickRfl

theorem sifts : bAnd(allN 6 (fun k => siftY (E k)), allN 3 (fun k => siftY (CC.S k))) = true := by
  quickRfl

theorem dRel : allN 3 (fun k =>
    Nat.beq (YC.SI k) (pc (E 0) (pc (pc (E (3 + k)) (E 0)) (E (6 + k))))) = true := by
  quickRfl

theorem rRel : bAnd(Nat.beq (pc (E 0) (E 0)) idP, bAnd(neK (E 0) idP,
    bAnd(Nat.beq (pc (E 1) (E 1)) (E 0), bAnd(Nat.beq (pc (E 2) (E 2)) (E 0),
    Nat.beq (pc (pc (E 2) (E 1)) (pc (E 0) (E 2))) (pc (E 0) (E 1)))))) = true := by
  quickRfl

theorem cCent : allN 3 (fun k => commK (CC.S k) (E 0)) = true := by quickRfl

theorem norm : allN 3 (fun k => bAnd(
    Nat.beq (pc (pc (CC.S k) (E 1)) (CC.SI k)) (wfoldK 240 8 (mask 8) rL (nw.getD (2 * k) []) idP),
    Nat.beq (pc (pc (CC.S k) (E 2)) (CC.SI k))
      (wfoldK 240 8 (mask 8) rL (nw.getD (2 * k + 1) []) idP))) = true := by
  quickRfl

theorem pRel : bAnd(Nat.beq (wfoldK 240 8 (mask 8) pL [1, 1, 1] idP) idP,
    bAnd(Nat.beq (wfoldK 240 8 (mask 8) pL [2, 2, 2] idP) idP, bAnd(commK (E 9) (E 10),
    allN 8 (fun k => neK (E (24 + k)) idP)))) = true := by
  quickRfl

theorem disj : disjK (E 11) (E 12) = true := by quickRfl

theorem good : goodK (fun k => E (14 + k)) = true := by quickRfl

theorem acts3 : bAnd(Nat.beq (pc (pc (E 13) (E 13)) (E 13)) idP,
    bIf(commK (E 13) (E 1), false, true)) = true := by
  quickRfl

end CertificateChecks.KernelSp6Cover

end

module

public import Certificates.Kernel.Sporadic.McLC.GenData
public import Certificates.Kernel.Sporadic.McLC.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC

@[expose] noncomputable def GT (j i : Nat) : Nat := GP (Nat.add (GO j) i)

@[expose] noncomputable def repD (j : Nat) : List Nat × List (List Nat) :=
  List.getD CFSG.ClassicalInvolution.McLData.repData j ([], [])

@[expose] noncomputable def gsOK (j : Nat) : Bool :=
  bAnd(Nat.beq (GL j) (Nat.succ (repD j).2.length),
  strictB (RP j) fun R => bAnd(strictB (GT j (nat_lit 0)) fun G =>
      allN (nat_lit 275) fun x => Nat.beq (pk G x) (pk R x),
    allN (repD j).2.length fun i => strictB (GT j (Nat.succ i)) fun G =>
      allN (nat_lit 275) fun x =>
        Nat.beq (pk G (List.foldr GK x (List.getD (repD j).2 i [])))
          (List.foldr GK (pk R x) (List.getD (repD j).2 i []))))

@[expose] noncomputable def vword (v : Nat) : List Nat :=
  List.map (fun i => VC (Nat.add (VS v) i)) (List.range (VN v))

@[expose] noncomputable def vOK (j : Nat) : Bool :=
  allN (nat_lit 2) fun e => strictB (Nat.add (Nat.mul (nat_lit 2) j) e) fun v =>
    bAnd(List.all (vword v) (fun i => Nat.blt i (GL j)),
      allN (nat_lit 275) fun x => Nat.beq (LJ (Nat.mul (nat_lit 2) e) x)
        (List.foldr (fun i y => pk (GT j i) y) x (vword v)))

theorem gsOK_ok : allN 21 gsOK = true := by quickRfl
theorem vOK_ok : allN 21 vOK = true := by quickRfl

end CertificateChecks.KernelSpor.McLC

end

module

public import Certificates.Kernel.Sporadic.ON2.Checks
public import Certificates.Kernel.Sporadic.ON2.MVData
public import Certificates.Data.Kernel.ON.BasisLit
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONF CFSG.Sporadic.ON.Native CFSG.Sporadic.ON.Kernel

@[expose] noncomputable def XL : List Nat := basisXPairs.map fun r => vmk r.1 r.2

@[expose] noncomputable def RbL : List Nat := (List.range 154).map fun t => key ONW.K (cq t)

@[expose] noncomputable def CO (c : Nat) : Nat := mv XL (key ONW.K c)

@[expose] noncomputable def fAF (j : Nat) : Bool := Nat.beq (mvF ONFA.T 39 (ONW.CA j)) (vmk (Nat.pow 2 j) 0)

@[expose] noncomputable def fBF (j : Nat) : Bool :=
  Nat.beq (mvF ONFB.T 39 (mvF ONFB.T 39 (mvF ONFB.T 39 (ONW.CB j)))) (vmk (Nat.pow 2 j) 0)

theorem matAF0 : allBlk (Nat.mul 14 0) fAF 14 = true := by quickRfl
theorem matAF1 : allBlk (Nat.mul 14 1) fAF 14 = true := by quickRfl
theorem matAF2 : allBlk (Nat.mul 14 2) fAF 14 = true := by quickRfl
theorem matAF3 : allBlk (Nat.mul 14 3) fAF 14 = true := by quickRfl
theorem matAF4 : allBlk (Nat.mul 14 4) fAF 14 = true := by quickRfl
theorem matAF5 : allBlk (Nat.mul 14 5) fAF 14 = true := by quickRfl
theorem matAF6 : allBlk (Nat.mul 14 6) fAF 14 = true := by quickRfl
theorem matAF7 : allBlk (Nat.mul 14 7) fAF 14 = true := by quickRfl
theorem matAF8 : allBlk (Nat.mul 14 8) fAF 14 = true := by quickRfl
theorem matAF9 : allBlk (Nat.mul 14 9) fAF 14 = true := by quickRfl
theorem matAF10 : allBlk (Nat.mul 14 10) fAF 14 = true := by quickRfl

theorem matBF0 : allBlk (Nat.mul 14 0) fBF 14 = true := by quickRfl
theorem matBF1 : allBlk (Nat.mul 14 1) fBF 14 = true := by quickRfl
theorem matBF2 : allBlk (Nat.mul 14 2) fBF 14 = true := by quickRfl
theorem matBF3 : allBlk (Nat.mul 14 3) fBF 14 = true := by quickRfl
theorem matBF4 : allBlk (Nat.mul 14 4) fBF 14 = true := by quickRfl
theorem matBF5 : allBlk (Nat.mul 14 5) fBF 14 = true := by quickRfl
theorem matBF6 : allBlk (Nat.mul 14 6) fBF 14 = true := by quickRfl
theorem matBF7 : allBlk (Nat.mul 14 7) fBF 14 = true := by quickRfl
theorem matBF8 : allBlk (Nat.mul 14 8) fBF 14 = true := by quickRfl
theorem matBF9 : allBlk (Nat.mul 14 9) fBF 14 = true := by quickRfl
theorem matBF10 : allBlk (Nat.mul 14 10) fBF 14 = true := by quickRfl

theorem allN_of_blk14 {f : Nat → Bool} (h : ∀ s < 11, allBlk (Nat.mul 14 s) f 14 = true) :
    allN 154 f = true :=
  CFSG.KS.PackFld.allN_of_forall fun j hj => by
    have h1 := allBlk_spec (h (j / 14) (by omega)) (j % 14) (Nat.mod_lt _ (by omega))
    have e : Nat.add (Nat.mul 14 (j / 14)) (j % 14) = j := Nat.div_add_mod j 14
    rwa [e] at h1

theorem matAF : allN 154 fAF = true := allN_of_blk14 fun s hs =>
  match s, hs with
  | 0, _ => matAF0 | 1, _ => matAF1 | 2, _ => matAF2 | 3, _ => matAF3 | 4, _ => matAF4
  | 5, _ => matAF5 | 6, _ => matAF6 | 7, _ => matAF7 | 8, _ => matAF8 | 9, _ => matAF9
  | 10, _ => matAF10 | _ + 11, h => absurd h (by omega)

theorem matBF : allN 154 fBF = true := allN_of_blk14 fun s hs =>
  match s, hs with
  | 0, _ => matBF0 | 1, _ => matBF1 | 2, _ => matBF2 | 3, _ => matBF3 | 4, _ => matBF4
  | 5, _ => matBF5 | 6, _ => matBF6 | 7, _ => matBF7 | 8, _ => matBF8 | 9, _ => matBF9
  | 10, _ => matBF10 | _ + 11, h => absurd h (by omega)

theorem matA : allN 154 (fun j => Nat.beq (mv ONW.LA (ONW.CA j)) (vmk (Nat.pow 2 j) 0)) = true := by
  have e := mvF_eq CertificateChecks.KernelSpor.ON.tabA CertificateChecks.KernelSpor.ON.lensA colsOKA
    flatWA CertificateChecks.KernelSpor.ON.lenA
  have h : (fun j => Nat.beq (mv ONW.LA (ONW.CA j)) (vmk (Nat.pow 2 j) 0)) = fAF := by
    funext j
    unfold fAF
    rw [e]
  rw [h]
  exact matAF

theorem matB : allN 154 (fun j => Nat.beq (mv ONW.LB (mv ONW.LB (mv ONW.LB (ONW.CB j))))
    (vmk (Nat.pow 2 j) 0)) = true := by
  have e := mvF_eq CertificateChecks.KernelSpor.ON.tabB CertificateChecks.KernelSpor.ON.lensB colsOKB
    flatWB CertificateChecks.KernelSpor.ON.lenB
  have h : (fun j => Nat.beq (mv ONW.LB (mv ONW.LB (mv ONW.LB (ONW.CB j)))) (vmk (Nat.pow 2 j) 0)) =
      fBF := by
    funext j
    unfold fBF
    rw [e, e, e]
  rw [h]
  exact matBF

@[expose] noncomputable def fBO (k : Nat) : Bool := bAnd(canon (List.getD XL k 0),
    bAnd(Nat.blt (List.getD basisXPairs k (0, 0)).1 (Nat.pow 2 154),
    bAnd(Nat.blt (List.getD basisXPairs k (0, 0)).2 (Nat.pow 2 154),
    Nat.beq (mv RbL (List.getD XL k 0)) (vmk (Nat.pow 2 k) 0))))

theorem basisOK0 : allBlk (Nat.mul 14 0) fBO 14 = true := by quickRfl
theorem basisOK1 : allBlk (Nat.mul 14 1) fBO 14 = true := by quickRfl
theorem basisOK2 : allBlk (Nat.mul 14 2) fBO 14 = true := by quickRfl
theorem basisOK3 : allBlk (Nat.mul 14 3) fBO 14 = true := by quickRfl
theorem basisOK4 : allBlk (Nat.mul 14 4) fBO 14 = true := by quickRfl
theorem basisOK5 : allBlk (Nat.mul 14 5) fBO 14 = true := by quickRfl
theorem basisOK6 : allBlk (Nat.mul 14 6) fBO 14 = true := by quickRfl
theorem basisOK7 : allBlk (Nat.mul 14 7) fBO 14 = true := by quickRfl
theorem basisOK8 : allBlk (Nat.mul 14 8) fBO 14 = true := by quickRfl
theorem basisOK9 : allBlk (Nat.mul 14 9) fBO 14 = true := by quickRfl
theorem basisOK10 : allBlk (Nat.mul 14 10) fBO 14 = true := by quickRfl

theorem basisOKF : allN 154 fBO = true := allN_of_blk14 fun s hs =>
  match s, hs with
  | 0, _ => basisOK0 | 1, _ => basisOK1 | 2, _ => basisOK2 | 3, _ => basisOK3 | 4, _ => basisOK4
  | 5, _ => basisOK5 | 6, _ => basisOK6 | 7, _ => basisOK7 | 8, _ => basisOK8 | 9, _ => basisOK9
  | 10, _ => basisOK10 | _ + 11, h => absurd h (by omega)

theorem basisOK : allN 154 (fun k => bAnd(canon (List.getD XL k 0),
    bAnd(Nat.blt (List.getD basisXPairs k (0, 0)).1 (Nat.pow 2 154),
    bAnd(Nat.blt (List.getD basisXPairs k (0, 0)).2 (Nat.pow 2 154),
    Nat.beq (mv RbL (List.getD XL k 0)) (vmk (Nat.pow 2 k) 0))))) = true :=
  basisOKF

theorem lensOK : bAnd(Nat.beq (List.length XL) 154, Nat.beq (List.length RbL) 154) = true := by quickRfl

theorem supOK : allN 7 (fun s => strictB (checkVecs[s]!) fun c => bAnd(Nat.blt c 245520,
    bAnd(canon (CO c), bAnd(Nat.beq (mv RbL (CO c)) (key ONW.K c),
    bIf(bit (vP (CO c)) 0, true, bit (vM (CO c)) 0))))) = true := by
  quickRfl

theorem supCover : allN 154 (fun t => Bool.not (allN 7 fun s =>
    Bool.not (bIf(bit (vP (CO (checkVecs[s]!))) t, true, bit (vM (CO (checkVecs[s]!))) t)))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.ON2

end

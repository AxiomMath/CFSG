module

public import Certificates.Kernel.U38R.Data
public import Certificates.Kernel.SchreierFam.C188001C1
public import Certificates.Kernel.U38.Data
public import Certificates.Data.Kernel.KeyIdx
public import Certificates.Data.Kernel.K426K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38R

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.K426K
  CFSG.KC.Misc.ArrEnum

@[expose] noncomputable def IX : Nat := IXL.headD 0

@[expose] noncomputable def ixBit (i : Nat) : Nat := pg 1 1 IX i

@[expose] noncomputable def siftXK (G : Nat) : Bool :=
  siftK 513 10 (mask 10) (Nat.mul 513 10) (pidn 513 10) KernelU38.UX.LR KernelU38.UX.TRI
    KernelU38.UX.BP 4 0 G

@[expose] noncomputable def mulK (i j : Nat) : Nat := mulIdx 513 10 [0, 1] KR (UR.T i) (UR.T j)

theorem kW : szOK 513 10 = true := by quickRfl

theorem permRH : allN 12 (fun j => permB 513 10 (RH.F j)) = true := by quickRfl

theorem nums : Nat.beq UR.N 729 = true ∧ Nat.beq UR.ng 3 = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem gensR : allN 3 (fun j => Nat.beq (UR.G j) (RH.F j)) = true := by quickRfl

theorem kIdx : allN 729 (fun m => Nat.beq (keyIdx 513 10 KR (CFSG.KC.BfsPin.keyK 513 10 [0, 1] (UR.T m))) m) =
    true := by
  quickRfl

theorem sift1R : allN 3 (fun j => siftOK 513 10 3 KernelSchreierFam.U38C1.LR
    KernelSchreierFam.U38C1.TRI KernelSchreierFam.U38C1.BP (RH.F j)) = true := by
  quickRfl

theorem siftHR : allN 9 (fun k => siftOK 513 10 4 KernelU38.UX.LR KernelU38.UX.TRI KernelU38.UX.BP
    (RH.F (Nat.add 3 k))) = true := by
  quickRfl

theorem flagsR : allN 729 (fun i =>
    cond (siftXK (UR.T i)) (Nat.beq (ixBit i) 1) (Nat.beq (ixBit i) 0)) = true := by
  quickRfl

theorem cntR : Nat.beq (CFSG.KLie.CT.sumN 729 (fun i =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq (ixBit i) 1))) 81 = true := by
  quickRfl

end CertificateChecks.KernelU38R

end

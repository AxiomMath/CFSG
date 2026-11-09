module

public import Certificates.Kernel.LyModel.Cp3Data
public import Certificates.Kernel.LyModel.Cp3Net
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CertificateChecks.KernelLyModel

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.LyBenes CFSG.KC.LyDce CFSG.KC.LyModel
  CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims CertificateChecks.KernelLyB
  CertificateChecks.KernelLyDce

theorem ly6110_cp3yC : yC = Ly0.wordY.map lcode := by decide +kernel

theorem ly6110_cp3gC : gC = Ly0.wordConj.map lcode := by decide +kernel

theorem ly6110_cp3uC : uC = Ly0.uWords.map fun w => w.map lcode := by decide +kernel

theorem ly6110_cp3orb : orbAll = true := by decide +kernel

theorem ly6110_cp3validY : netValid 17 NY0 = true := by decide +kernel

theorem cp3_recAnd {P : Nat → Bool} : ∀ n, (∀ b < n, P b = true) →
    Nat.rec (motive := fun _ => Bool) true (fun b ih => andB ih (P b)) n = true
  | 0, _ => rfl
  | n + 1, h => by
    show andB (Nat.rec (motive := fun _ => Bool) true (fun b ih => andB ih (P b)) n) (P n) = true
    rw [cp3_recAnd n (fun b hb => h b (by omega)), h n (by omega)]
    rfl

theorem cp3_planesEq_of {k N : Nat} {Ns : List Nat}
    (h : ∀ b < k, Nat.beq (netsApply k (Nat.shiftLeft 1 k) 1 Ns (idPlane (Nat.shiftLeft 1 k) b))
      (netApply k (Nat.shiftLeft 1 k) 1 N (idPlane (Nat.shiftLeft 1 k) b)) = true) :
    planesEq k Ns N = true := by
  unfold planesEq
  exact cp3_recAnd k h

@[expose] noncomputable def cp3Q (Ns : List Nat) (N b : Nat) : Bool :=
  Nat.beq (netsApply 17 (Nat.shiftLeft 1 17) 1 Ns (idPlane (Nat.shiftLeft 1 17) b))
    (netApply 17 (Nat.shiftLeft 1 17) 1 N (idPlane (Nat.shiftLeft 1 17) b))

theorem cp3_planesEq17 {Ns : List Nat} {N : Nat}
    (h0 : cp3Q Ns N 0 = true) (h1 : cp3Q Ns N 1 = true) (h2 : cp3Q Ns N 2 = true)
    (h3 : cp3Q Ns N 3 = true) (h4 : cp3Q Ns N 4 = true) (h5 : cp3Q Ns N 5 = true)
    (h6 : cp3Q Ns N 6 = true) (h7 : cp3Q Ns N 7 = true) (h8 : cp3Q Ns N 8 = true)
    (h9 : cp3Q Ns N 9 = true) (h10 : cp3Q Ns N 10 = true) (h11 : cp3Q Ns N 11 = true)
    (h12 : cp3Q Ns N 12 = true) (h13 : cp3Q Ns N 13 = true) (h14 : cp3Q Ns N 14 = true)
    (h15 : cp3Q Ns N 15 = true) (h16 : cp3Q Ns N 16 = true) :
    planesEq 17 Ns N = true :=
  cp3_planesEq_of fun b hb => by
    interval_cases b <;> assumption

theorem ly6110_cp3netY_p0 : cp3Q (genNets NS Ly0.wordY) NY0 0 = true := by quickRfl

theorem ly6110_cp3netY_p1 : cp3Q (genNets NS Ly0.wordY) NY0 1 = true := by quickRfl

theorem ly6110_cp3netY_p2 : cp3Q (genNets NS Ly0.wordY) NY0 2 = true := by quickRfl

theorem ly6110_cp3netY_p3 : cp3Q (genNets NS Ly0.wordY) NY0 3 = true := by quickRfl

theorem ly6110_cp3netY_p4 : cp3Q (genNets NS Ly0.wordY) NY0 4 = true := by quickRfl

theorem ly6110_cp3netY_p5 : cp3Q (genNets NS Ly0.wordY) NY0 5 = true := by quickRfl

theorem ly6110_cp3netY_p6 : cp3Q (genNets NS Ly0.wordY) NY0 6 = true := by quickRfl

theorem ly6110_cp3netY_p7 : cp3Q (genNets NS Ly0.wordY) NY0 7 = true := by quickRfl

theorem ly6110_cp3netY_p8 : cp3Q (genNets NS Ly0.wordY) NY0 8 = true := by quickRfl

theorem ly6110_cp3netY_p9 : cp3Q (genNets NS Ly0.wordY) NY0 9 = true := by quickRfl

theorem ly6110_cp3netY_p10 : cp3Q (genNets NS Ly0.wordY) NY0 10 = true := by quickRfl

theorem ly6110_cp3netY_p11 : cp3Q (genNets NS Ly0.wordY) NY0 11 = true := by quickRfl

theorem ly6110_cp3netY_p12 : cp3Q (genNets NS Ly0.wordY) NY0 12 = true := by quickRfl

theorem ly6110_cp3netY_p13 : cp3Q (genNets NS Ly0.wordY) NY0 13 = true := by quickRfl

theorem ly6110_cp3netY_p14 : cp3Q (genNets NS Ly0.wordY) NY0 14 = true := by quickRfl

theorem ly6110_cp3netY_p15 : cp3Q (genNets NS Ly0.wordY) NY0 15 = true := by quickRfl

theorem ly6110_cp3netY_p16 : cp3Q (genNets NS Ly0.wordY) NY0 16 = true := by quickRfl

theorem ly6110_cp3netY : planesEq 17 (genNets NS Ly0.wordY) NY0 = true :=
  cp3_planesEq17
    ly6110_cp3netY_p0 ly6110_cp3netY_p1 ly6110_cp3netY_p2 ly6110_cp3netY_p3 ly6110_cp3netY_p4
    ly6110_cp3netY_p5 ly6110_cp3netY_p6 ly6110_cp3netY_p7 ly6110_cp3netY_p8 ly6110_cp3netY_p9
    ly6110_cp3netY_p10 ly6110_cp3netY_p11 ly6110_cp3netY_p12 ly6110_cp3netY_p13
    ly6110_cp3netY_p14 ly6110_cp3netY_p15 ly6110_cp3netY_p16

theorem ly6110_cp3fix : fixM NY0 (maskOf o0) = true := by decide +kernel

end CertificateChecks.KernelLyModel

end

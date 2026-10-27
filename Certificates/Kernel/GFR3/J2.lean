module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3J2Inputs
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.GFR3K
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.GFR3.J2Chain
public meta import CFSG.HardMathSupport.Solomon.Coordinator.GFR3J2Inputs
public meta import Certificates.Kernel.B3S3.Gen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#kb3_enum CertificateChecks.KernelGFR3.J2.E
  CFSG.HardMathSupport.Solomon.Coordinator.j2ThreeGens
  CFSG.HardMathSupport.Solomon.Coordinator.j2ThreeBaseArr 315 9

public section

namespace CertificateChecks.KernelGFR3.J2

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K CFSG.KC.GFR3K

theorem szOK' : szOK 315 9 = true := by quickRfl

theorem pAB : permB 315 9 (JS.F 0) = true ∧ permB 315 9 (JS.F 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem sS : ∀ j < 7, Nat.beq (JH.F j) (C.S (j + 2)) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bG : ∀ j < 4, arrBind j2ThreeGens[j]! 315 9 (E.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem perm : allN 9 (fun j => permOK 315 9 (mask 9) (315 * 9) (C.S j) (C.SI j)) = true := by
  quickRfl

theorem head : Nat.beq (C.S 0) (JS.F 0) = true ∧ Nat.beq (C.S 1) (JS.F 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem bget : ∀ t < 7, j2ThreeBaseArr[t]! = pg 9 (mask 9) C.BP t := by decide +kernel

theorem siftG : ∀ k < 4, Nat.beq (Nat.shiftRight (E.G k) (315 * 9)) 0 = true ∧
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (E.G k) t) 315) = true ∧
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) C.LR C.TRI C.BP 7 0 (E.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem rels : relsK 315 9 3 C.BP (E.G 0) 7 j2ThreeRels = true := by quickRfl

theorem comm : commK 315 9 4 (E.G 0) E.G = true := by quickRfl

theorem x0 : permB 315 9 (E.G 0) = true ∧ Nat.beq (pw 315 9 (E.G 0) 3) (pidn 315 9) = true ∧
    (!Nat.beq (E.G 0) (pidn 315 9)) = true := ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem rc : Nat.beq (rcnt (C.LR 0)) 315 = true := by quickRfl

theorem orb : ((List.range 7).map fun i => rcnt (C.LR i)) = [315, 10, 16, 4, 3, 1, 1] := by
  decide +kernel

@[expose] noncomputable def clsBlock (b : Nat) : Bool :=
  allN 60 fun i => gfr3AtK 315 9 1080 E.T 1080 3 1 (Nat.add (Nat.mul 60 b) i)

theorem n0 : Nat.beq E.N 1080 = true ∧ Nat.beq E.ng 4 = true := ⟨by quickRfl, by quickRfl⟩

end CertificateChecks.KernelGFR3.J2

end

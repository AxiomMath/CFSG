module

public import Certificates.Kernel.Sporadic.SuzK.LaneDefs
public import Certificates.Kernel.Sporadic.SuzK.TreeK
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.F3R

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KC.Ord

set_option Elab.async false

theorem neg_edge : Bool.not (Nat.beq (MUL (x3 0) (kx 5)) (MUL (kx (Nat.succ (r32 AL 5))) (x3 0))) =
    true := by quickRfl

theorem neg_valid : Bool.not (VLD (Nat.lor (kx 7) (Nat.add 1 (Nat.shiftLeft 1 4096)))) = true := by
  quickRfl

theorem neg_sort : Bool.not (Nat.blt (kx (r32 SO 101)) (kx (r32 SO 100))) = true := by quickRfl

theorem neg_root : Bool.not (Nat.beq (kx 1) (x3 8)) = true := by quickRfl

theorem neg_rule : Bool.not (Nat.beq (symK 3 9)
    (Nat.succ (symK (List.getD RULES 0 0) (symK (List.getD RULES 1 0) 9)))) = true := by quickRfl

theorem neg_letter : Bool.not (allN 1000 fun x => Nat.beq (LJ 2 x) (LJ 4 x)) = true := by quickRfl

theorem neg_inv : Bool.not (allN 22880 fun x => Nat.beq (LJ 3 (LJ 4 x)) x) = true := by quickRfl

theorem neg_tree : Bool.not (tbfsSlK 22880 (TCNT 1) (lvK LJ BJ 28 1).length (fun l x => LJ l (Nat.succ x))
    (lvAt LJ BJ 28 1) (TPTS 1) (TPOS 1) (TPAR 1) (TLAB 1) (TTI 1) 0 1000) = true := by quickRfl

theorem neg_tr : Bool.not (bIf(Nat.beq (r32 LB 5) 1, Nat.beq (r32 BE (r32 PA 5)) 5,
    Nat.beq (r32 AL (r32 PA 5)) 5)) = true := by quickRfl

theorem neg_bfs : Bool.not (CFSG.KC.F3Bfs.bfsOrderOK (r32 BE) (r32 AL) (r32 PA) (r32 LB) 22880) =
    true := by quickRfl

end CertificateChecks.KernelSpor.SuzK

end

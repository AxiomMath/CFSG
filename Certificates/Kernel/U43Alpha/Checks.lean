module

public import Certificates.Data.Kernel.U43Alpha.Defs
public import Certificates.Kernel.U43Alpha.Data
public import Certificates.Kernel.U43Mod.OutChecks
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43P3Class
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 1

namespace CertificateChecks.KernelU43Alpha

open CFSG.KC.Enum CFSG.KC.U43Alpha CertificateChecks.KernelU43Out
open CFSG.RankThree.PartTwo.Sec6.Res611Res6.U43P

@[expose] noncomputable def KS (l : Nat) : Nat → Nat := fun j => G (Nat.add (Nat.mul (nat_lit 8) l) j)

@[expose] noncomputable def base3A (X w : Nat) : Bool :=
  bAnd(Nat.beq (pg (nat_lit 10) (nat_lit 1023) X (nat_lit 0)) (act w (nat_lit 0)),
  bAnd(Nat.beq (pg (nat_lit 10) (nat_lit 1023) X (nat_lit 1)) (act w (nat_lit 1)),
    Nat.beq (pg (nat_lit 10) (nat_lit 1023) X (nat_lit 9)) (act w (nat_lit 9))))

@[expose] noncomputable def commAt (X Y q : Nat) : Bool :=
  Nat.beq (pg (nat_lit 10) (nat_lit 1023) X (pg (nat_lit 10) (nat_lit 1023) Y q))
    (pg (nat_lit 10) (nat_lit 1023) Y (pg (nat_lit 10) (nat_lit 1023) X q))

theorem ch12650perm : allN 4 (fun l => allN 4 (fun j =>
    permOK 820 10 (CFSG.KS.mask 10) (820 * 10) (KS l j) (GI (Nat.add (Nat.mul 8 l) j)))) = true := by
  quickRfl

theorem ch12650inN : allN 4 (fun l => allN 4 (fun j => KernelU43Aut3962.inN (KS l j))) = true := by
  quickRfl

theorem ch12650rep : allN 4 (fun l => base3A (KS l 0) (repW (Nat.succ l))) = true := by
  quickRfl

theorem ch12650comm : allN 4 (fun l => allN 4 (fun j =>
    bAnd(commAt (KS l j) (KS l 0) 0, bAnd(commAt (KS l j) (KS l 0) 1, commAt (KS l j) (KS l 0) 9)))) =
    true := by
  quickRfl

theorem ch12650orb0 : orbPart 820 (KS 0) 4 (L 0) (W 0) (RO 0) (NB 0) (SZ 0) = true := by quickRfl

theorem ch12650orb1 : orbPart 820 (KS 1) 4 (L 1) (W 1) (RO 1) (NB 1) (SZ 1) = true := by quickRfl

theorem ch12650orb2 : orbPart 820 (KS 2) 4 (L 2) (W 2) (RO 2) (NB 2) (SZ 2) = true := by quickRfl

theorem ch12650orb3 : orbPart 820 (KS 3) 4 (L 3) (W 3) (RO 3) (NB 3) (SZ 3) = true := by quickRfl

theorem ch12650sum0 : noFixSum (SZ 0) (NB 0) = true := by quickRfl

theorem ch12650sum1 : noFixSum (SZ 1) (NB 1) = true := by quickRfl

theorem ch12650sum2 : noFixSum (SZ 2) (NB 2) = true := by quickRfl

theorem ch12650odd : bAnd(allN (NB 3) (fun i => Nat.beq (fld(SZ 3, Nat.mul 8 i, 255) % 2) 1),
    bAnd(Nat.beq (cntSz (SZ 3) (NB 3) 1 % 2) 1, bAnd(Nat.beq (cntSz (SZ 3) (NB 3) 3 % 2) 1,
    bAnd(Nat.beq (cntSz (SZ 3) (NB 3) 9 % 2) 1, Nat.beq (cntSz (SZ 3) (NB 3) 81 % 2) 1)))) = true := by
  quickRfl

theorem ch12650fix : allN 14 (repOK ET RP) = true := by quickRfl

theorem ch12650cj : allN 1024 (cjOK ET ETi FR RP CJ 14) = true := by quickRfl

end CertificateChecks.KernelU43Alpha

end

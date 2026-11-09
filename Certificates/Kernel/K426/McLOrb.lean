module

public import Certificates.Kernel.K426.McLChecks
public import Certificates.Data.Kernel.Misc.ChainTailOrb
public import Certificates.Kernel.SporSch.Th.GenV4
meta import Certificates.Data.K426McL
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval

namespace CertificateChecks.KernelK426.OB

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer

meta def orbL (S : Array (Array ℕ)) (base : Array ℕ) (x : Array ℕ) (rels : List (ℕ × ℕ × ℕ))
    (c : ArrCert) : List Nat × List Nat × List Nat := Id.run do
  let p := ((rawLevels 275 S base)[0]!).pts
  let c := c.pts
  let xs := powPA 3 275 x
  let mut idx := Array.replicate 275 0
  for k in [0:p.size] do
    idx := idx.set! (p[k]!) k
  let mut ri := Array.replicate p.size p.size
  let mut ek := Array.replicate p.size 0
  let mut reps : Array Nat := #[]
  for k in [0:p.size] do
    if ri[k]! == p.size && relOK base xs rels 0 (idA 275) p[k]! then
      let j := reps.size
      reps := reps.push k
      let q := p[k]!
      for e in [0:c.size] do
        let t := idx.getD ((c.getD e #[]).getD q 0) 0
        if ri[t]! == p.size then
          ri := ri.set! t j
          ek := ek.set! t e
  return (reps.toList, (ri.map fun i => if i == p.size then 0 else i).toList, ek.toList)

meta def orbA : List Nat × List Nat × List Nat :=
  orbL mcl3ChainAArrs mcl3ChainABaseArr mcl3Lines[0]! mcl3RelsA mcl3CACert
meta def orbB : List Nat × List Nat × List Nat :=
  orbL mcl3ChainBArrs mcl3ChainBBaseArr mcl3Lines[1]! mcl3RelsB mcl3CBCert

meta def repAL : List Nat := orbA.1
meta def riAL : List Nat := orbA.2.1
meta def ekAL : List Nat := orbA.2.2
meta def repBL : List Nat := orbB.1
meta def riBL : List Nat := orbB.2.1
meta def ekBL : List Nat := orbB.2.2

end CertificateChecks.KernelK426.OB

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelK426.RBA CertificateChecks.KernelK426.OB.repAL
#kss_natlist CertificateChecks.KernelK426.RIA CertificateChecks.KernelK426.OB.riAL
#kss_natlist CertificateChecks.KernelK426.EKA CertificateChecks.KernelK426.OB.ekAL
#kss_natlist CertificateChecks.KernelK426.RBB CertificateChecks.KernelK426.OB.repBL
#kss_natlist CertificateChecks.KernelK426.RIB CertificateChecks.KernelK426.OB.riBL
#kss_natlist CertificateChecks.KernelK426.EKB CertificateChecks.KernelK426.OB.ekBL

namespace CertificateChecks.KernelK426

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.KC.B3S3K CFSG.KC.K426K CFSG.RankThree.PartTwo.KFacts.K426

@[expose] noncomputable def repA (q : Nat) : Bool :=
  relOKK 9 (mask 9) MA.BP (pw 275 9 (F 4)) mcl3RelsA 0 (pidn 275 9) (rpt 9 (mask 9) (MA.LR 0) q) &&
    ptailBranchIdxK 275 9 MA.LR MA.TR MA.BP (F 4) (pw 275 9 (F 4)) mcl3RelsA EA.N EA.T EA.S 10 q

@[expose] noncomputable def repB (q : Nat) : Bool :=
  relOKK 9 (mask 9) MB.BP (pw 275 9 (F 5)) mcl3RelsB 0 (pidn 275 9) (rpt 9 (mask 9) (MB.LR 0) q) &&
    ptailBranchIdxK 275 9 MB.LR MB.TR MB.BP (F 5) (pw 275 9 (F 5)) mcl3RelsB EB.N EB.T EB.S 10 q

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem ptail_succ (n w : Nat) (LR TR : Nat → Nat) (BP X : Nat) (XP : Nat → Nat)
    (rels : List (Nat × Nat × Nat)) (NE : Nat) (EP ES : Nat → Nat) (m i acc : Nat) :
    ptailIdxK n w LR TR BP X XP rels NE EP ES (Nat.succ m) i acc =
      allN (rcnt (LR i)) (fun k => !(relOKK w (mask w) BP XP rels i acc (rpt w (mask w) (LR i) k)) ||
        ptailIdxK n w LR TR BP X XP rels NE EP ES m (Nat.succ i)
          (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) (LR i)) k)))) := by
  show strictB (LR i) (fun R => allN (rcnt R) fun k =>
    !(relOKK w (mask w) BP XP rels i acc (rpt w (mask w) R k)) ||
      ptailIdxK n w LR TR BP X XP rels NE EP ES m (Nat.succ i)
        (pcomp n w (mask w) acc (TR (Nat.add (roff n (Nat.mul n w) R) k)))) = _
  rw [strictB_eq']

theorem allN_guard_blocks {N : Nat} {f : Nat → Bool} (B K : Nat) (hN : Nat.ble N (B * K) = true)
    (h : ∀ s < K, allN B (fun j => !(Nat.blt (Nat.add (Nat.mul B s) j) N) ||
      f (Nat.add (Nat.mul B s) j)) = true) : allN N f = true := by
  rw [Orb.allN_iff]
  intro a ha
  have hle : N ≤ B * K := Nat.le_of_ble_eq_true hN
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · subst h0
      simp at hle
      omega
    · exact h0
  have haBK : a < B * K := Nat.lt_of_lt_of_le ha hle
  have hs : a / B < K := (Nat.div_lt_iff_lt_mul hB).2 (by rw [Nat.mul_comm]; exact haBK)
  have := Orb.allN_iff.1 (h (a / B) hs) (a % B) (Nat.mod_lt a hB)
  change (!(Nat.blt (Nat.add (Nat.mul B (a / B)) (a % B)) N) ||
    f (Nat.add (Nat.mul B (a / B)) (a % B))) = true at this
  rw [show Nat.add (Nat.mul B (a / B)) (a % B) = a from Nat.div_add_mod a B] at this
  have hlt : Nat.blt a N = true := Eq.mpr Nat.blt_eq ha
  rw [hlt] at this
  simpa using this

@[expose] noncomputable def gA (k : Nat) : Bool :=
  !(relOKK 9 (mask 9) MA.BP (pw 275 9 (F 4)) mcl3RelsA 1
      (MA.TR (Nat.add (roff 275 (Nat.mul 275 9) (MA.LR 0)) (RBA 0))) (rpt 9 (mask 9) (MA.LR 1) k)) ||
    ptailIdxK 275 9 MA.LR MA.TR MA.BP (F 4) (pw 275 9 (F 4)) mcl3RelsA EA.N EA.T EA.S 8 (Nat.succ 1)
      (pcomp 275 9 (mask 9) (MA.TR (Nat.add (roff 275 (Nat.mul 275 9) (MA.LR 0)) (RBA 0)))
        (MA.TR (Nat.add (roff 275 (Nat.mul 275 9) (MA.LR 1)) k)))

theorem pA_rel : relOKK 9 (mask 9) MA.BP (pw 275 9 (F 4)) mcl3RelsA 0 (pidn 275 9)
    (rpt 9 (mask 9) (MA.LR 0) (RBA 0)) = true := by quickRfl

theorem pA_N : Nat.ble (rcnt (MA.LR 1)) (22 * 8) = true := by quickRfl

theorem pA_b0 : allN 22 (fun j => !(Nat.blt (Nat.add (Nat.mul 22 0) j) (rcnt (MA.LR 1))) ||
    gA (Nat.add (Nat.mul 22 0) j)) = true := by quickRfl
theorem pA_b1 : allN 22 (fun j => !(Nat.blt (Nat.add (Nat.mul 22 1) j) (rcnt (MA.LR 1))) ||
    gA (Nat.add (Nat.mul 22 1) j)) = true := by quickRfl
theorem pA_b2 : allN 22 (fun j => !(Nat.blt (Nat.add (Nat.mul 22 2) j) (rcnt (MA.LR 1))) ||
    gA (Nat.add (Nat.mul 22 2) j)) = true := by quickRfl
theorem pA_b3 : allN 22 (fun j => !(Nat.blt (Nat.add (Nat.mul 22 3) j) (rcnt (MA.LR 1))) ||
    gA (Nat.add (Nat.mul 22 3) j)) = true := by quickRfl
theorem pA_b4 : allN 22 (fun j => !(Nat.blt (Nat.add (Nat.mul 22 4) j) (rcnt (MA.LR 1))) ||
    gA (Nat.add (Nat.mul 22 4) j)) = true := by quickRfl
theorem pA_b5 : allN 22 (fun j => !(Nat.blt (Nat.add (Nat.mul 22 5) j) (rcnt (MA.LR 1))) ||
    gA (Nat.add (Nat.mul 22 5) j)) = true := by quickRfl
theorem pA_b6 : allN 22 (fun j => !(Nat.blt (Nat.add (Nat.mul 22 6) j) (rcnt (MA.LR 1))) ||
    gA (Nat.add (Nat.mul 22 6) j)) = true := by quickRfl
theorem pA_b7 : allN 22 (fun j => !(Nat.blt (Nat.add (Nat.mul 22 7) j) (rcnt (MA.LR 1))) ||
    gA (Nat.add (Nat.mul 22 7) j)) = true := by quickRfl

theorem repA0 : repA (RBA 0) = true := by
  have h2 : ptailIdxK 275 9 MA.LR MA.TR MA.BP (F 4) (pw 275 9 (F 4)) mcl3RelsA EA.N EA.T EA.S
      (Nat.succ 8) 1 (MA.TR (Nat.add (roff 275 (Nat.mul 275 9) (MA.LR 0)) (RBA 0))) = true := by
    rw [ptail_succ]
    exact allN_guard_blocks (f := gA) 22 8 pA_N fun s hs => match s, hs with
      | 0, _ => pA_b0 | 1, _ => pA_b1 | 2, _ => pA_b2 | 3, _ => pA_b3
      | 4, _ => pA_b4 | 5, _ => pA_b5 | 6, _ => pA_b6 | 7, _ => pA_b7 | _ + 8, h => absurd h (by omega)
  unfold repA ptailBranchIdxK
  rw [pA_rel]
  simp only [Bool.true_and, Bool.not_true, Bool.false_or]
  exact h2

theorem repB0 : repB (RBB 0) = true := by quickRfl

theorem repB1 : repB (RBB 1) = true := by quickRfl

theorem repB2 : repB (RBB 2) = true := by quickRfl

theorem kOrbA : allN 275 (orbRelK 275 9 MA.LR MA.BP (pw 275 9 (F 4)) mcl3RelsA EA.N EA.T 1 RBA
    RIA EKA) = true := by quickRfl

theorem kOrbB : allN 275 (orbRelK 275 9 MB.LR MB.BP (pw 275 9 (F 5)) mcl3RelsB EB.N EB.T 3 RBB
    RIB EKB) = true := by quickRfl

end CertificateChecks.KernelK426

end

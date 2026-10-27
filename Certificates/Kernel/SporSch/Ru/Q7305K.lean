
module

public import Certificates.Kernel.SporSch.Ru.Q7307K
public import CFSG.Quasithin.Recognition.RuRank3J55DataInputs
meta import CFSG.Quasithin.Recognition.RuRank3J55DataInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.Q7305E CFSG.Quasithin.RuRank3.ruEGText
#kmisc_hexflat CertificateChecks.KernelSporSch.Q7305E CFSG.Quasithin.RuRank3.ruEGText 3 4060 12 2
#ks_chars CertificateChecks.KernelSporSch.Q7305F CFSG.Quasithin.RuRank3.ruFrobText
#kmisc_hexflat CertificateChecks.KernelSporSch.Q7305F CFSG.Quasithin.RuRank3.ruFrobText 3 4060 12 2

namespace CertificateChecks.KernelSporSch.Q7305

meta def labM : Array Nat := CFSG.Quasithin.RuRank3.ruELab

meta def rootsM : Array Nat :=
  (CFSG.Quasithin.RuRank3.orbLabels 4060 CFSG.Quasithin.RuRank3.ruEGArrs).2

meta def mM : Array Nat := #[rootsM.size]

meta def forestM : Array Nat × Array Nat × Array Nat := Id.run do
  let gens := CFSG.Quasithin.RuRank3.ruEGArrs
  let n := 4060
  let mut par : Array Nat := Array.replicate n 0
  let mut kk : Array Nat := Array.replicate n 0
  let mut dep : Array Nat := Array.replicate n 0
  let mut seen : Array Bool := Array.replicate n false
  for r in rootsM do
    seen := seen.set! r true
    let mut queue : Array Nat := #[r]
    let mut head := 0
    for _ in [0:n] do
      if head < queue.size then
        let x := queue[head]!
        head := head + 1
        for k in [0:gens.size] do
          let y := (gens[k]!)[x]!
          if y < n && !seen[y]! then
            seen := seen.set! y true
            par := par.set! y x
            kk := kk.set! y k
            dep := dep.set! y (dep[x]! + 1)
            queue := queue.push y
  return (par, kk, dep)

meta def parM : Array Nat := forestM.1
meta def kM : Array Nat := forestM.2.1
meta def depM : Array Nat := forestM.2.2

end CertificateChecks.KernelSporSch.Q7305

#ks_perm CertificateChecks.KernelSporSch.Q7305.EL 12 CertificateChecks.KernelSporSch.Q7305.labM
#ks_perm CertificateChecks.KernelSporSch.Q7305.ER 12 CertificateChecks.KernelSporSch.Q7305.rootsM
#ks_perm CertificateChecks.KernelSporSch.Q7305.EM 12 CertificateChecks.KernelSporSch.Q7305.mM
#ks_perm CertificateChecks.KernelSporSch.Q7305.EP 12 CertificateChecks.KernelSporSch.Q7305.parM
#ks_perm CertificateChecks.KernelSporSch.Q7305.EK 12 CertificateChecks.KernelSporSch.Q7305.kM
#ks_perm CertificateChecks.KernelSporSch.Q7305.ED 12 CertificateChecks.KernelSporSch.Q7305.depM

namespace CertificateChecks.KernelSporSch.Q7305

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.OrbLab
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.G2Ru7164
  CertificateChecks.KernelSporSch.Q7307

@[expose] noncomputable def gE (k x : Nat) : Nat := fl (Q7305E.F k) x

@[expose] noncomputable def ELf (x : Nat) : Nat := fl EL x
@[expose] noncomputable def ERf (c : Nat) : Nat := fl ER c
@[expose] noncomputable def EPf (x : Nat) : Nat := fl EP x
@[expose] noncomputable def EKf (x : Nat) : Nat := fl EK x
@[expose] noncomputable def EDf (x : Nat) : Nat := fl ED x
@[expose] noncomputable def EMv : Nat := fl EM 0

theorem kOrbE : orbRecK 4060 EMv 2 gE ELf ERf EPf EKf EDf = true := by quickRfl

@[expose] noncomputable def TG : Nat := pinv (wK Af (Iso7047.twK 32 2808))

theorem kWordG : ((Iso7047.twK 32 2808).all fun l => l != 0 && decide (l.natAbs ≤ 2)) = true := by
  quickRfl

@[expose] noncomputable def eOK (T x : Nat) : Bool :=
  bAnd(Nat.blt (fl T x) 4060,
    (Nat.beq (Lf x) (Lf 1) && Nat.beq (Lf (fl T x)) (Lf 1)) == Nat.beq (ELf x) 2 &&
    (Nat.beq (Lf x) (Lf 1) && !Nat.beq (Lf (fl T x)) (Lf 1)) == Nat.beq (ELf x) 1 &&
    (Nat.beq (Lf x) (Lf 2808) && Nat.beq (Lf (fl T x)) (Lf 1)) == Nat.beq (ELf x) 3)

theorem kE : strictB TG (fun T => allN 4060 (eOK T)) = true := by quickRfl

@[expose] noncomputable def cnt (l : Nat) : Nat := (List.range 4060).countP fun x => Nat.beq (ELf x) l

theorem kCnt : cnt 0 = 1 ∧ cnt 1 = 975 ∧ cnt 2 = 780 ∧ cnt 3 = 975 ∧ cnt 4 = 300 ∧ cnt 5 = 650 ∧
    cnt 6 = 300 ∧ cnt 7 = 78 ∧ cnt 8 = 1 := by
  decide +kernel

theorem kLt : allN 4060 (fun x => Nat.blt (ELf x) 9) = true := by quickRfl

theorem kWit : bAnd(Nat.beq (ELf 0) 0, bAnd(Nat.beq (ELf 1) 1, bAnd(Nat.beq (ELf 2) 2,
    bAnd(bIf(Nat.beq (Lf 0) (Lf 2808), false, true), bAnd(bIf(Nat.beq (Lf 1) (Lf 2808), false, true),
      bIf(Nat.beq (Lf 2) (Lf 2808), false, true)))))) = true := by
  quickRfl

@[expose] noncomputable def FR (i : Nat) : Nat := Q7305F.F i

@[expose] noncomputable def fOK (i : Nat) : Bool :=
  bAnd(permOK 4060 12 (mask 12) (4060 * 12) (FR i) (pinvS 4060 12 (mask 12) (FR i)),
  bAnd(Nat.beq (Nat.shiftRight (FR i) (4060 * 12)) 0,
  bAnd(allN 4060 (fun x => Nat.blt (pg 12 (mask 12) (FR i) x) 4060),
  bAnd(siftK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) RuJS.LR RuJS.TRI RuJS.BP 4 0 (FR i),
  bAnd(Nat.beq (pg 12 (mask 12) (FR i) 0) 0,
  bAnd(Nat.beq (pg 12 (mask 12) (FR i) 2808) 2808, Nat.beq (pg 12 (mask 12) (FR i) 2) 2))))))

theorem kF0 : fOK 0 = true := by quickRfl
theorem kF1 : fOK 1 = true := by quickRfl

theorem kPow : bAnd(Nat.beq (powK (FR 0) 5) pid, bAnd(bIf(Nat.beq (FR 0) pid, false, true),
    bAnd(Nat.beq (powK (FR 1) 4) pid, bAnd(bIf(Nat.beq (powK (FR 1) 2) pid, false, true),
      Nat.beq (conjK (FR 1) (FR 0)) (powK (FR 0) 2))))) = true := by
  quickRfl

theorem neg : bAnd(bIf(Nat.beq (powK (FR 0) 4) pid, false, true),
    bAnd(bIf(Nat.beq (conjK (FR 1) (FR 0)) (FR 0), false, true),
    bAnd(bIf(Nat.beq (ELf 2) 3, false, true),
      bIf(allN 4060 (fun x => (Nat.beq (Lf x) (Lf 1) && Nat.beq (Lf (fl TG x)) (Lf 1)) ==
        Nat.beq (ELf x) 3), false, true)))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Q7305

end

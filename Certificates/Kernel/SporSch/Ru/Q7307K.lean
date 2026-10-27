
module

public import Certificates.Kernel.SporSch.Ru.Iso7047K
public import Certificates.Kernel.SporSch.Ru.G2Ru7164K
public import Certificates.Kernel.SporSch.Tits.Graph2265K
public import Certificates.Data.Kernel.SporSch.OrbRec
public import CFSG.Quasithin.Recognition.RuRank3RuGraphDataInputs
meta import CFSG.Quasithin.Recognition.RuRank3RuGraphDataInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Q7307

meta def labM : Array Nat := CFSG.Quasithin.RuRank3.ruQLab

meta def rootsM : Array Nat := (CFSG.Quasithin.RuRank3.orbLabels 4060 CFSG.Quasithin.RuRank3.ruR0Arrs).2

meta def mM : Array Nat := #[rootsM.size]

meta def forestM : Array Nat × Array Nat × Array Nat := Id.run do
  let gens := CFSG.Quasithin.RuRank3.ruR0Arrs
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

end CertificateChecks.KernelSporSch.Q7307

#ks_perm CertificateChecks.KernelSporSch.Q7307.QL 12 CertificateChecks.KernelSporSch.Q7307.labM
#ks_perm CertificateChecks.KernelSporSch.Q7307.QR 12 CertificateChecks.KernelSporSch.Q7307.rootsM
#ks_perm CertificateChecks.KernelSporSch.Q7307.QM 12 CertificateChecks.KernelSporSch.Q7307.mM
#ks_perm CertificateChecks.KernelSporSch.Q7307.QP 12 CertificateChecks.KernelSporSch.Q7307.parM
#ks_perm CertificateChecks.KernelSporSch.Q7307.QK 12 CertificateChecks.KernelSporSch.Q7307.kM
#ks_perm CertificateChecks.KernelSporSch.Q7307.QD 12 CertificateChecks.KernelSporSch.Q7307.depM

namespace CertificateChecks.KernelSporSch.Q7307

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.OrbLab
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.G2Ru7164

@[expose] noncomputable def fl (T x : Nat) : Nat := pg 12 (mask 12) T x

@[expose] noncomputable def gR (k x : Nat) : Nat := fl (Iso7047.R k) x

@[expose] noncomputable def Lf (x : Nat) : Nat := fl QL x
@[expose] noncomputable def Rf (c : Nat) : Nat := fl QR c
@[expose] noncomputable def Pf (x : Nat) : Nat := fl QP x
@[expose] noncomputable def Kf (x : Nat) : Nat := fl QK x
@[expose] noncomputable def Df (x : Nat) : Nat := fl QD x
@[expose] noncomputable def Mv : Nat := fl QM 0

theorem kOrb : orbRecK 4060 Mv 4 gR Lf Rf Pf Kf Df = true := by quickRfl

@[expose] noncomputable def stepK (L : List Nat) : List Nat :=
  L ++ L.flatMap fun x => (List.range 10).map fun i => pgW 11 TitsGN.NB (10 * x + i)

@[expose] noncomputable def ballK : List Nat := stepK (stepK (stepK [0]))

@[expose] noncomputable def maskL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ acc => Nat.lor (Nat.shiftLeft 1 x) acc) l

@[expose] noncomputable def Af (j : Nat) : Nat := Bool.rec (motive := fun _ => Nat) A1 A0 (Nat.beq j 0)

@[expose] noncomputable def TI : Nat := pinv (wK Af (Iso7047.twK 32 1))

theorem kNbr : allN 1755 (fun u => allN 10 (fun i => Nat.blt (pgW 11 TitsGN.NB (10 * u + i)) 1755)) =
    true := by
  quickRfl

theorem kWord : ((Iso7047.twK 32 1).all fun l => l != 0 && decide (l.natAbs ≤ 2)) = true := by
  quickRfl

theorem kPerm0 : permOK 4060 12 (mask 12) (4060 * 12) A0 (pinv A0) = true := by quickRfl

theorem kPerm1 : permOK 4060 12 (mask 12) (4060 * 12) A1 (pinv A1) = true := by quickRfl

@[expose] noncomputable def ptOK (B T j : Nat) : Bool :=
  bAnd(Nat.blt (fl T (fl Iso7047.D j)) 4060,
    (Nat.testBit B j == (Nat.beq j 0 || Nat.beq (Lf (fl T (fl Iso7047.D j))) (Lf 1))))

theorem kMain : strictB (maskL ballK) (fun B => strictB TI (fun T => allN 1755 (ptOK B T))) = true := by
  quickRfl

theorem neg : bAnd(bIf(allN 1755 (fun j => Nat.testBit (maskL ballK) j), false, true),
    bAnd(bIf(Nat.beq (Lf 1) (Lf 0), false, true),
      bIf(strictB TI (fun T => allN 1755 (fun j => (Nat.testBit (maskL ballK) j ==
        (Nat.beq j 0 || Nat.beq (Lf (fl T (fl Iso7047.D j))) (Lf 0))))), false, true))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.Q7307

end

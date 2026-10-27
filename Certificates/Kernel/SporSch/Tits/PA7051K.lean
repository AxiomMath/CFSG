module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Tits.Text
public import Certificates.Data.Kernel.SporSch.OrbRec
public import Certificates.Data.Kernel.SporSch.RuOrbKG
public meta import CFSG.Quasithin.Recognition.RuRank3TitsSylInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Assembly.LowTwoRankDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PA7051

open CFSG.Sporadic.RuSchreier

meta def gensM : Array (Array Nat) := CFSG.Quasithin.RuRank3.titsPAGens

meta def labM : Array Nat := CFSG.Quasithin.RuRank3.titsPALab

meta def rootsM : Array Nat := (CFSG.Quasithin.RuRank3.orbLabels 1755 gensM).2

meta def mM : Array Nat := #[rootsM.size]

meta def forestM : Array Nat × Array Nat × Array Nat := orbitForest 1755 gensM rootsM

meta def queueM : Array Nat := Id.run do
  let n := 1755
  let mut seen : Array Bool := Array.replicate n false
  let mut queue : Array Nat := #[]
  for r in rootsM do
    if r < n && !seen[r]! then
      seen := seen.set! r true
      queue := queue.push r
  let mut head := 0
  for _ in [0:n] do
    if head < queue.size then
      let x := queue[head]!
      head := head + 1
      for k in [0:gensM.size] do
        let y := (gensM[k]!)[x]!
        if y < n && !seen[y]! then
          seen := seen.set! y true
          queue := queue.push y
  return queue

meta def ordM : Array Nat := Id.run do
  let mut r := Array.replicate 1755 0
  for t in [0:queueM.size] do
    r := r.set! queueM[t]! t
  return r

meta def foM : Array Nat :=
  (Array.range queueM.size).map fun t =>
    if t < rootsM.size then 0 else 4 * ordM[forestM.2.1[queueM[t]!]!]! + forestM.2.2[queueM[t]!]!

meta def depM : Array Nat := forestM.1
meta def parM : Array Nat := forestM.2.1
meta def glM : Array Nat := forestM.2.2

end CertificateChecks.KernelSporSch.PA7051

#ks_perm CertificateChecks.KernelSporSch.PA7051.EL 11 CertificateChecks.KernelSporSch.PA7051.labM
#ks_perm CertificateChecks.KernelSporSch.PA7051.ER 11 CertificateChecks.KernelSporSch.PA7051.rootsM
#ks_perm CertificateChecks.KernelSporSch.PA7051.EM 11 CertificateChecks.KernelSporSch.PA7051.mM
#ks_perm CertificateChecks.KernelSporSch.PA7051.QK 11 CertificateChecks.KernelSporSch.PA7051.queueM
#ks_perm CertificateChecks.KernelSporSch.PA7051.ORK 11 CertificateChecks.KernelSporSch.PA7051.ordM
#ks_perm CertificateChecks.KernelSporSch.PA7051.FOK 13 CertificateChecks.KernelSporSch.PA7051.foM
#ks_perm CertificateChecks.KernelSporSch.PA7051.DPK 11 CertificateChecks.KernelSporSch.PA7051.depM
#ks_perm CertificateChecks.KernelSporSch.PA7051.PAK 11 CertificateChecks.KernelSporSch.PA7051.parM
#ks_perm CertificateChecks.KernelSporSch.PA7051.GLK 11 CertificateChecks.KernelSporSch.PA7051.glM

namespace CertificateChecks.KernelSporSch.PA7051

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.OrbLab CertificateChecks.KernelMisc

@[expose] noncomputable def fl (T x : Nat) : Nat := pg 11 (mask 11) T x

@[expose] noncomputable def GP (k : Nat) : Nat :=
  nIf(Nat.beq k 3, TitsText.F 1, TitsText.F (Nat.add 52 k))

@[expose] noncomputable def gP (k x : Nat) : Nat := fl (GP k) x

@[expose] noncomputable def Lf (x : Nat) : Nat := fl EL x
@[expose] noncomputable def Rf (c : Nat) : Nat := fl ER c
@[expose] noncomputable def Mv : Nat := fl EM 0
@[expose] noncomputable def Qf (t : Nat) : Nat := fl QK t
@[expose] noncomputable def ORf (x : Nat) : Nat := fl ORK x
@[expose] noncomputable def FOf (t : Nat) : Nat := pg 13 (mask 13) FOK t
@[expose] noncomputable def DPf (x : Nat) : Nat := fl DPK x
@[expose] noncomputable def PAf (x : Nat) : Nat := fl PAK x
@[expose] noncomputable def GLf (x : Nat) : Nat := fl GLK x

@[expose] noncomputable def cntL (n c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (Nat.beq (Lf x) c)) n

theorem kOrb : orbRecK 1755 Mv 4 gP Lf Rf PAf GLf DPf = true := by quickRfl

theorem kF : allN 1755 (forestAtG 1755 4 Mv gP Qf ORf FOf DPf PAf GLf) = true := by quickRfl

theorem kE : allN 7020 (eventAtG 1755 4 Mv gP Qf ORf FOf) = true := by quickRfl

theorem kP : allN 1755 (partAtG 1755 4 Mv gP Lf Qf DPf PAf GLf) = true := by quickRfl

theorem kRt : allN Mv (rootAtG 1755 Lf Qf) = true := by quickRfl

theorem kQR : bAnd(Nat.ble Mv 1755, allN Mv (fun t => Nat.beq (Qf t) (Rf t))) = true := by
  quickRfl

theorem kCnt : bAnd(Nat.beq (cntL 1755 (Lf 0)) 1, bAnd(Nat.beq (Lf 1) (Lf 2),
    Nat.beq (cntL 1755 (Lf 1)) 2)) = true := by
  quickRfl

theorem kLt : allN 1755 (fun x => Nat.blt (Lf x) Mv) = true := by quickRfl

theorem kBig : allN Mv (fun c => bIf(Nat.beq c (Lf 0), true,
    bIf(Nat.beq c (Lf 1), true, Nat.ble 8 (cntL 1755 c)))) = true := by
  quickRfl

theorem kOut : allN 1755 (fun x => bIf(Nat.blt x 3, true,
    bAnd(bIf(Nat.beq (Lf x) (Lf 0), false, true), bIf(Nat.beq (Lf x) (Lf 1), false, true)))) =
    true := by
  quickRfl

theorem kFix : Nat.beq (gP 3 0) 0 = true := by quickRfl

theorem negPA : bAnd(bIf(allN 1755 (forestAtG 1755 4 Mv gP (fun t => Qf (Nat.succ t)) ORf FOf DPf
      PAf GLf), false, true),
    bAnd(bIf(orbRecK 1755 Mv 4 gP (fun x => Lf (Nat.succ x)) Rf PAf GLf DPf, false, true),
    bAnd(bIf(Nat.beq (cntL 1755 (Lf 0)) 2, false, true),
    bAnd(bIf(allN Mv (fun c => bIf(Nat.beq c (Lf 0), true,
      bIf(Nat.beq c (Lf 1), true, Nat.ble 9 (cntL 1755 c)))), false, true),
    bIf(allN 4 (fun k => Nat.beq (gP k 1) 1), false, true))))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.PA7051

end

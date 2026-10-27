
module

public import Certificates.Kernel.SporSch.Ru.Rows7045K
public import Certificates.Kernel.Misc.Tits.E07043K
public import Certificates.Data.Kernel.SporSch.RuOrbKG
public meta import CFSG.Quasithin.Recognition.RuRank3RuAutDataInputs
public meta import CFSG.Quasithin.Recognition.RuRank3TitsSylInputs
import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.K07045

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

meta def gensM : Array (Array Nat) := CFSG.Quasithin.RuRank3.titsK0Gens

meta def rootsM : Array Nat := (CFSG.Quasithin.RuRank3.orbLabels 1755 gensM).2

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
    if t < rootsM.size then 0 else 3 * ordM[forestM.2.1[queueM[t]!]!]! + forestM.2.2[queueM[t]!]!

meta def depM : Array Nat := forestM.1
meta def parM : Array Nat := forestM.2.1
meta def glM : Array Nat := forestM.2.2

end CertificateChecks.KernelSporSch.K07045

#ks_perm CertificateChecks.KernelSporSch.K07045.QK 11 CertificateChecks.KernelSporSch.K07045.queueM
#ks_perm CertificateChecks.KernelSporSch.K07045.ORK 11 CertificateChecks.KernelSporSch.K07045.ordM
#ks_perm CertificateChecks.KernelSporSch.K07045.FOK 13 CertificateChecks.KernelSporSch.K07045.foM
#ks_perm CertificateChecks.KernelSporSch.K07045.DPK 11 CertificateChecks.KernelSporSch.K07045.depM
#ks_perm CertificateChecks.KernelSporSch.K07045.PAK 11 CertificateChecks.KernelSporSch.K07045.parM
#ks_perm CertificateChecks.KernelSporSch.K07045.GLK 11 CertificateChecks.KernelSporSch.K07045.glM

namespace CertificateChecks.KernelSporSch.K07045

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.RowTree CFSG.KS.RuTree CFSG.KLC.Fi22
  CertificateChecks.KernelSporSch CertificateChecks.KernelMisc

@[expose] noncomputable def fl (T x : Nat) : Nat := pg 11 (mask 11) T x

@[expose] noncomputable def Qf (t : Nat) : Nat := fl QK t
@[expose] noncomputable def ORf (x : Nat) : Nat := fl ORK x
@[expose] noncomputable def FOf (t : Nat) : Nat := pg 13 (mask 13) FOK t
@[expose] noncomputable def DPf (x : Nat) : Nat := fl DPK x
@[expose] noncomputable def PAf (x : Nat) : Nat := fl PAK x
@[expose] noncomputable def GLf (x : Nat) : Nat := fl GLK x

theorem kF : allN 1755 (forestAtG 1755 3 E7043.Mv E7043.gK Qf ORf FOf DPf PAf GLf) = true := by
  quickRfl

theorem kE : allN 5265 (eventAtG 1755 3 E7043.Mv E7043.gK Qf ORf FOf) = true := by quickRfl

theorem kP : allN 1755 (partAtG 1755 3 E7043.Mv E7043.gK E7043.Lf Qf DPf PAf GLf) = true := by
  quickRfl

theorem kRt : allN E7043.Mv (rootAtG 1755 E7043.Lf Qf) = true := by quickRfl

theorem kQR : andB (Nat.ble E7043.Mv 1755) (allN E7043.Mv (fun t => Nat.beq (Qf t) (E7043.Rf t))) =
    true := by
  quickRfl

@[expose] noncomputable def cntL (n c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (Nat.beq (E7043.Lf x) c)) n

theorem kLt : allN 1755 (fun x => Nat.blt (E7043.Lf x) E7043.Mv) = true := by quickRfl

theorem kC0 :Nat.beq (cntL 1755 (E7043.Lf 0)) 975 = true := by quickRfl

theorem kSmall : allN E7043.Mv (fun c => orB (Nat.beq c (E7043.Lf 0)) (Nat.blt (cntL 1755 c) 975)) =
    true := by
  quickRfl

@[expose] noncomputable def eqB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

theorem kG0 : allN 1755 (fun j => eqB (notB (Nat.beq (E7043.Lf j) (E7043.Lf 0)))
    (bt (Ru7045.Row 2808) (pg 12 (mask 12) Iso7047.D j))) = true := by
  quickRfl

theorem negK0 : andB (notB (allN 1755 (forestAtG 1755 3 E7043.Mv E7043.gK (fun t => Qf (Nat.succ t))
      ORf FOf DPf PAf GLf)))
    (andB (notB (Nat.beq (cntL 1755 (E7043.Lf 0)) 974))
      (notB (allN 1755 (fun j => eqB (notB (Nat.beq (E7043.Lf j) (E7043.Lf 0)))
        (bt (Ru7045.Row 1) (pg 12 (mask 12) Iso7047.D j)))))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.K07045

end

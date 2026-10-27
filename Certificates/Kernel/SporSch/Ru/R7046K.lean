
module

public import Certificates.Kernel.SporSch.Ru.Q7307K
public import Certificates.Data.Kernel.SporSch.RuOrbKG
public import CFSG.Certificates.Kernel.LieCocycle.Fi22.Core
public meta import CFSG.Quasithin.Recognition.RuRank3RuGraphDataInputs
public meta import Certificates.Kernel.SporSch.Ru.QueueGen
import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.QueueGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.R7046

open CFSG.Sporadic.RuSchreier

meta def gensM : Array (Array Nat) := CFSG.Quasithin.RuRank3.ruR0Arrs
meta def rootsM : Array Nat := (CFSG.Quasithin.RuRank3.orbLabels 4060 gensM).2
meta def forestM : Array Nat × Array Nat × Array Nat := orbitForest 4060 gensM rootsM
meta def queueM : Array Nat := QueueGen.queue 4060 gensM rootsM
meta def ordM : Array Nat := QueueGen.ord 4060 queueM
meta def foM : Array Nat := QueueGen.events 4 rootsM.size queueM ordM forestM.2.1 forestM.2.2
meta def depM : Array Nat := forestM.1
meta def parM : Array Nat := forestM.2.1
meta def glM : Array Nat := forestM.2.2

end CertificateChecks.KernelSporSch.R7046

#ks_perm CertificateChecks.KernelSporSch.R7046.RQ 12 CertificateChecks.KernelSporSch.R7046.queueM
#ks_perm CertificateChecks.KernelSporSch.R7046.RO 12 CertificateChecks.KernelSporSch.R7046.ordM
#ks_perm CertificateChecks.KernelSporSch.R7046.RFO 14 CertificateChecks.KernelSporSch.R7046.foM
#ks_perm CertificateChecks.KernelSporSch.R7046.RDP 12 CertificateChecks.KernelSporSch.R7046.depM
#ks_perm CertificateChecks.KernelSporSch.R7046.RPA 12 CertificateChecks.KernelSporSch.R7046.parM
#ks_perm CertificateChecks.KernelSporSch.R7046.RGL 12 CertificateChecks.KernelSporSch.R7046.glM

namespace CertificateChecks.KernelSporSch.R7046

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KLC.Fi22
  CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def fl (T x : Nat) : Nat := pg 12 (mask 12) T x

@[expose] noncomputable def Qf (t : Nat) : Nat := fl RQ t
@[expose] noncomputable def ORf (x : Nat) : Nat := fl RO x
@[expose] noncomputable def FOf (t : Nat) : Nat := pg 14 (mask 14) RFO t
@[expose] noncomputable def DPf (x : Nat) : Nat := fl RDP x
@[expose] noncomputable def PAf (x : Nat) : Nat := fl RPA x
@[expose] noncomputable def GLf (x : Nat) : Nat := fl RGL x

theorem kF : allN 4060 (forestAtG 4060 4 Q7307.Mv Q7307.gR Qf ORf FOf DPf PAf GLf) = true := by
  quickRfl

theorem kE : allN 16240 (eventAtG 4060 4 Q7307.Mv Q7307.gR Qf ORf FOf) = true := by quickRfl

theorem kP : allN 4060 (partAtG 4060 4 Q7307.Mv Q7307.gR Q7307.Lf Qf DPf PAf GLf) = true := by
  quickRfl

theorem kRt : allN Q7307.Mv (rootAtG 4060 Q7307.Lf Qf) = true := by quickRfl

theorem kQR : andB (Nat.ble Q7307.Mv 4060)
    (allN Q7307.Mv (fun t => Nat.beq (Qf t) (Q7307.Rf t))) = true := by
  quickRfl

@[expose] noncomputable def cntL (n c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (Nat.beq (Q7307.Lf x) c)) n

theorem kQ0 : allN 4060 (fun x => orB (Nat.beq x 0) (notB (Nat.beq (Q7307.Lf x) (Q7307.Lf 0)))) =
    true := by
  quickRfl

theorem kQD : allN 1755 (fun j => Nat.beq (Q7307.Lf (fl Iso7047.D j)) (Q7307.Lf 1)) = true := by
  quickRfl

theorem kQC : andB (Nat.beq (cntL 4060 (Q7307.Lf 1)) 1755)
    (Nat.beq (cntL 4060 (Q7307.Lf 2808)) 2304) = true := by
  quickRfl

theorem kQ3 : allN 4060 (fun x => orB (Nat.beq (Q7307.Lf x) (Q7307.Lf 0))
    (orB (Nat.beq (Q7307.Lf x) (Q7307.Lf 1)) (Nat.beq (Q7307.Lf x) (Q7307.Lf 2808)))) = true := by
  quickRfl

theorem kQne : andB (notB (Nat.beq (Q7307.Lf 1) (Q7307.Lf 2808)))
    (notB (Nat.beq (Q7307.Lf 0) (Q7307.Lf 2808))) = true := by
  quickRfl

theorem kA0 : andB (Nat.beq (fl A0 0) 1) (Nat.beq (fl A0 1) 0) = true := by quickRfl

theorem negR : andB (notB (allN 4060 (forestAtG 4060 4 Q7307.Mv Q7307.gR (fun t => Qf (Nat.succ t))
      ORf FOf DPf PAf GLf)))
    (andB (notB (Nat.beq (cntL 4060 (Q7307.Lf 1)) 1754))
      (andB (notB (allN 4060 (fun x => orB (Nat.beq x 1)
          (notB (Nat.beq (Q7307.Lf x) (Q7307.Lf 0))))))
        (notB (Nat.beq (fl A0 0) 0)))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.R7046

end

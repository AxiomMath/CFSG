
module

public import Certificates.Kernel.SporSch.Ru.S7046
public import Certificates.Data.Kernel.SporSch.RuOrbKG
public meta import CFSG.Quasithin.Recognition.RuRank3RuGraphDataInputs
public meta import Certificates.Kernel.SporSch.Ru.QueueGen
import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.QueueGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.E7046

open CFSG.Sporadic.RuSchreier

meta def gensM : Array (Array Nat) := CFSG.Quasithin.RuRank3.ruEGArrs
meta def rootsM : Array Nat := (CFSG.Quasithin.RuRank3.orbLabels 4060 gensM).2
meta def forestM : Array Nat × Array Nat × Array Nat := orbitForest 4060 gensM rootsM
meta def queueM : Array Nat := QueueGen.queue 4060 gensM rootsM
meta def ordM : Array Nat := QueueGen.ord 4060 queueM
meta def foM : Array Nat := QueueGen.events 2 rootsM.size queueM ordM forestM.2.1 forestM.2.2
meta def depM : Array Nat := forestM.1
meta def parM : Array Nat := forestM.2.1
meta def glM : Array Nat := forestM.2.2

end CertificateChecks.KernelSporSch.E7046

#ks_perm CertificateChecks.KernelSporSch.E7046.EQ 12 CertificateChecks.KernelSporSch.E7046.queueM
#ks_perm CertificateChecks.KernelSporSch.E7046.EO 12 CertificateChecks.KernelSporSch.E7046.ordM
#ks_perm CertificateChecks.KernelSporSch.E7046.EFO 13 CertificateChecks.KernelSporSch.E7046.foM
#ks_perm CertificateChecks.KernelSporSch.E7046.EDP 12 CertificateChecks.KernelSporSch.E7046.depM
#ks_perm CertificateChecks.KernelSporSch.E7046.EPA 12 CertificateChecks.KernelSporSch.E7046.parM
#ks_perm CertificateChecks.KernelSporSch.E7046.EGL 12 CertificateChecks.KernelSporSch.E7046.glM

namespace CertificateChecks.KernelSporSch.E7046

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KLC.Fi22
  CertificateChecks.KernelSporSch.S7046

@[expose] noncomputable def fl (T x : Nat) : Nat := pg 12 (mask 12) T x

@[expose] noncomputable def Qf (t : Nat) : Nat := fl EQ t
@[expose] noncomputable def ORf (x : Nat) : Nat := fl EO x
@[expose] noncomputable def FOf (t : Nat) : Nat := pg 13 (mask 13) EFO t
@[expose] noncomputable def DPf (x : Nat) : Nat := fl EDP x
@[expose] noncomputable def PAf (x : Nat) : Nat := fl EPA x
@[expose] noncomputable def GLf (x : Nat) : Nat := fl EGL x

theorem kF : allN 4060 (forestAtG 4060 2 Q7305.EMv Q7305.gE Qf ORf FOf DPf PAf GLf) = true := by
  quickRfl

theorem kE : allN 8120 (eventAtG 4060 2 Q7305.EMv Q7305.gE Qf ORf FOf) = true := by quickRfl

theorem kP : allN 4060 (partAtG 4060 2 Q7305.EMv Q7305.gE Q7305.ELf Qf DPf PAf GLf) = true := by
  quickRfl

theorem kRt : allN Q7305.EMv (rootAtG 4060 Q7305.ELf Qf) = true := by quickRfl

theorem kQR : andB (Nat.ble Q7305.EMv 4060)
    (allN Q7305.EMv (fun t => Nat.beq (Qf t) (Q7305.ERf t))) = true := by
  quickRfl

theorem kS0 : sOK (Q7305E.F 0) 2808 = true := by quickRfl
theorem kS1 : sOK (Q7305E.F 1) 2808 = true := by quickRfl

theorem kW : Nat.beq (Q7305.ELf 2808) 8 = true := by quickRfl

theorem kD : allN 4060 (fun x => eqB (bt 6 (Q7305.ELf x)) (Nat.beq (Q7307.Lf x) (Q7307.Lf 1))) =
    true := by
  quickRfl

theorem kN : strictB Q7305.TG (fun T => allN 4060 (fun x => bAnd(Nat.blt (fl T x) 4060,
    eqB (bt 12 (Q7305.ELf x)) (Nat.beq (Q7307.Lf (fl T x)) (Q7307.Lf 1))))) = true := by
  quickRfl

theorem negE : andB (notB (allN 4060 (forestAtG 4060 2 Q7305.EMv Q7305.gE (fun t => Qf (Nat.succ t))
      ORf FOf DPf PAf GLf)))
    (andB (notB (sOK (Q7305E.F 0) 1))
      (notB (strictB Q7305.TG (fun T => allN 4060 (fun x => bAnd(Nat.blt (fl T x) 4060,
        eqB (bt 10 (Q7305.ELf x)) (Nat.beq (Q7307.Lf (fl T x)) (Q7307.Lf 1)))))))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.E7046

end

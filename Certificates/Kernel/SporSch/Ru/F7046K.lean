
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

namespace CertificateChecks.KernelSporSch.F7046

open CFSG.Sporadic.RuSchreier

meta def gensM : Array (Array Nat) := CFSG.Quasithin.RuRank3.ruFGArrs
meta def labM : Array Nat := CFSG.Quasithin.RuRank3.ruFLab
meta def rootsM : Array Nat := (CFSG.Quasithin.RuRank3.orbLabels 4060 gensM).2
meta def mM : Array Nat := #[rootsM.size]
meta def forestM : Array Nat × Array Nat × Array Nat := orbitForest 4060 gensM rootsM
meta def queueM : Array Nat := QueueGen.queue 4060 gensM rootsM
meta def ordM : Array Nat := QueueGen.ord 4060 queueM
meta def foM : Array Nat := QueueGen.events 2 rootsM.size queueM ordM forestM.2.1 forestM.2.2
meta def depM : Array Nat := forestM.1
meta def parM : Array Nat := forestM.2.1
meta def glM : Array Nat := forestM.2.2

end CertificateChecks.KernelSporSch.F7046

#ks_perm CertificateChecks.KernelSporSch.F7046.FL 12 CertificateChecks.KernelSporSch.F7046.labM
#ks_perm CertificateChecks.KernelSporSch.F7046.FR 12 CertificateChecks.KernelSporSch.F7046.rootsM
#ks_perm CertificateChecks.KernelSporSch.F7046.FM 12 CertificateChecks.KernelSporSch.F7046.mM
#ks_perm CertificateChecks.KernelSporSch.F7046.FQ 12 CertificateChecks.KernelSporSch.F7046.queueM
#ks_perm CertificateChecks.KernelSporSch.F7046.FO 12 CertificateChecks.KernelSporSch.F7046.ordM
#ks_perm CertificateChecks.KernelSporSch.F7046.FFO 13 CertificateChecks.KernelSporSch.F7046.foM
#ks_perm CertificateChecks.KernelSporSch.F7046.FDP 12 CertificateChecks.KernelSporSch.F7046.depM
#ks_perm CertificateChecks.KernelSporSch.F7046.FPA 12 CertificateChecks.KernelSporSch.F7046.parM
#ks_perm CertificateChecks.KernelSporSch.F7046.FGL 12 CertificateChecks.KernelSporSch.F7046.glM

namespace CertificateChecks.KernelSporSch.F7046

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.OrbLab CFSG.KLC.Fi22
  CertificateChecks.KernelSporSch.S7046

@[expose] noncomputable def fl (T x : Nat) : Nat := pg 12 (mask 12) T x

@[expose] noncomputable def gF (k x : Nat) : Nat := fl (Q7046F.F k) x

@[expose] noncomputable def Lf (x : Nat) : Nat := fl FL x
@[expose] noncomputable def Rf (c : Nat) : Nat := fl FR c
@[expose] noncomputable def Mv : Nat := fl FM 0
@[expose] noncomputable def Qf (t : Nat) : Nat := fl FQ t
@[expose] noncomputable def ORf (x : Nat) : Nat := fl FO x
@[expose] noncomputable def FOf (t : Nat) : Nat := pg 13 (mask 13) FFO t
@[expose] noncomputable def DPf (x : Nat) : Nat := fl FDP x
@[expose] noncomputable def PAf (x : Nat) : Nat := fl FPA x
@[expose] noncomputable def GLf (x : Nat) : Nat := fl FGL x

theorem kOrb : orbRecK 4060 Mv 2 gF Lf Rf PAf GLf DPf = true := by quickRfl

theorem kF : allN 4060 (forestAtG 4060 2 Mv gF Qf ORf FOf DPf PAf GLf) = true := by quickRfl

theorem kE : allN 8120 (eventAtG 4060 2 Mv gF Qf ORf FOf) = true := by quickRfl

theorem kP : allN 4060 (partAtG 4060 2 Mv gF Lf Qf DPf PAf GLf) = true := by quickRfl

theorem kRt : allN Mv (rootAtG 4060 Lf Qf) = true := by quickRfl

theorem kQR : andB (Nat.ble Mv 4060) (allN Mv (fun t => Nat.beq (Qf t) (Rf t))) = true := by
  quickRfl

theorem kS0 : sOK (Q7046F.F 0) 1 = true := by quickRfl
theorem kS1 : sOK (Q7046F.F 1) 1 = true := by quickRfl

theorem kLt : allN 4060 (fun x => Nat.blt (Lf x) 8) = true := by quickRfl

theorem kW : andB (Nat.beq (Lf 0) 0) (Nat.beq (Lf 1) 1) = true := by quickRfl

@[expose] noncomputable def cnt (l : Nat) : Nat := (List.range 4060).countP fun x => Nat.beq (Lf x) l

theorem kCnt : cnt 0 = 1 ∧ cnt 1 = 1 ∧ cnt 2 = 640 ∧ cnt 3 = 1024 ∧ cnt 4 = 1024 ∧ cnt 5 = 1280 ∧
    cnt 6 = 80 ∧ cnt 7 = 10 := by
  decide +kernel

theorem kMiss : allN 4060 (fun x => orB (notB (bt 205 (Lf x)))
    (notB (Nat.beq (Q7307.Lf x) (Q7307.Lf 2808)))) = true := by
  quickRfl

theorem kRow : strictB Q7307.TI (fun T => allN 4060 (fun x => bAnd(Nat.blt (fl T x) 4060,
    eqB (bt 213 (Lf x)) (Nat.beq (Q7307.Lf (fl T x)) (Q7307.Lf 1))))) = true := by
  quickRfl

theorem negF : andB (notB (allN 4060 (forestAtG 4060 2 Mv gF (fun t => Qf (Nat.succ t))
      ORf FOf DPf PAf GLf)))
    (andB (notB (sOK (Q7046F.F 0) 2808))
      (andB (notB (allN 4060 (fun x => orB (notB (bt 213 (Lf x)))
          (notB (Nat.beq (Q7307.Lf x) (Q7307.Lf 2808))))))
        (notB (strictB Q7307.TI (fun T => allN 4060 (fun x => bAnd(Nat.blt (fl T x) 4060,
          eqB (bt 205 (Lf x)) (Nat.beq (Q7307.Lf (fl T x)) (Q7307.Lf 1))))))))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.F7046

end

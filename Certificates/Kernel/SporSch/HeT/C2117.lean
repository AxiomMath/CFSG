module

public import Certificates.Kernel.SporSch.HeT.Q2117
public meta import CFSG.Sporadic.HeldB.OuterCentCheckInputs
meta import Certificates.Kernel.SporSch.HeT.Q2117K
meta import Certificates.Kernel.SporSch.Mathieu.GenChainCls
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeQ17

open CFSG.KS.SporSch.ChainClsG

meta def QYLsrc : Array Nat × Array Nat × Array Nat × Array Nat × Array Nat := chainCls 35 SQY baseQY 3

meta def QYLlb : Array (Array Nat) := chainLabs QYLsrc.1 512

meta def QYLcj : Array (Array Nat) := singles QYLsrc.2.1

meta def QYLrp : Array (Array Nat) := singles QYLsrc.2.2.1

meta def QYLsz : Array (Array Nat) := singles QYLsrc.2.2.2.1

meta def QYLzc : Array (Array Nat) := singles QYLsrc.2.2.2.2

end CertificateChecks.KernelSporSch.HeQ17

#kmisc_packarrs CertificateChecks.KernelSporSch.HeQ17.QYL.LB CertificateChecks.KernelSporSch.HeQ17.QYLlb 64

#kmisc_packarrs CertificateChecks.KernelSporSch.HeQ17.QYL.CJ CertificateChecks.KernelSporSch.HeQ17.QYLcj 64

#kmisc_packarrs CertificateChecks.KernelSporSch.HeQ17.QYL.RP CertificateChecks.KernelSporSch.HeQ17.QYLrp 64

#kmisc_packarrs CertificateChecks.KernelSporSch.HeQ17.QYL.SZ CertificateChecks.KernelSporSch.HeQ17.QYLsz 64

#kmisc_packarrs CertificateChecks.KernelSporSch.HeQ17.QYL.ZC CertificateChecks.KernelSporSch.HeQ17.QYLzc 64

namespace CertificateChecks.KernelSporSch.HeQ17

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CFSG.KS.SporSch.ChainCls

@[expose] noncomputable def QYL.invB (s : Nat) : Bool :=
  allBlk (s * 512) (fun j => bIf(Nat.blt j (ordK QY.LR 4),
    clsInvK 35 6 (mask 6) (35 * 6) (pidn 35 6) QY.LR QY.TR 4 QY.S QY.SI 3 QYL.LB QYL.CJ QYL.RP 9
      (ordK QY.LR 4) j, true)) 512

@[expose] noncomputable def QYL.repB (l : Nat) : Bool :=
  clsRepK 35 6 (mask 6) (35 * 6) (pidn 35 6) QY.LR QY.TR 4 QYL.LB QYL.RP QYL.SZ QYL.ZC
    (ordK QY.LR 4) l

end CertificateChecks.KernelSporSch.HeQ17

#kss_each CertificateChecks.KernelSporSch.HeQ17.QYL.I CertificateChecks.KernelSporSch.HeQ17.QYL.invB 5

#kss_each CertificateChecks.KernelSporSch.HeQ17.QYL.R CertificateChecks.KernelSporSch.HeQ17.QYL.repB 9

namespace CertificateChecks.KernelSporSch.HeQ17

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CFSG.KS.SporSch.ChainCls
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.HeldB

theorem kQYL : bAnd(Nat.ble (ordK QY.LR 4) (Nat.mul 5 512),
    allN 9 (fun l => Nat.ble (QYL.SZ l) 3000)) = true := by quickRfl

theorem szs : (List.range 9).map QYL.SZ = [630, 210, 360, 360, 504, 105, 70, 280, 1] := by
  decide +kernel

theorem zcs : (List.range 9).map QYL.ZC = [4, 12, 7, 7, 5, 24, 36, 9, 2520] := by
  decide +kernel

theorem classes_ok : classOK 35 heYGens heYGensInv (allTables heQY) 3000 = true ∧
    (classes 35 heYGens heYGensInv (allTables heQY) 3000).map (fun c => c.2.1.size) =
      [630, 210, 360, 360, 504, 105, 70, 280, 1] ∧
    (classes 35 heYGens heYGensInv (allTables heQY) 3000).map
      (fun c => (allTables heQY).countP (commT 35 c.1)) = [4, 12, 7, 7, 5, 24, 36, 9, 2520] := by
  have hk : Nat.ble (ordK QY.LR 4) (Nat.mul 5 512) = true ∧
      allN 9 (fun l => Nat.ble (QYL.SZ l) 3000) = true := by
    simpa only [bAnd_iff] using kQYL
  obtain ⟨h1, h2, h3⟩ := chainK_classes (by decide) (by decide) chainQY (c := 9) (cap := 3000)
    (Nat.le_of_ble_eq_true hk.1) QYL.I.all QYL.R.all
    (fun l hl => Nat.le_of_ble_eq_true (allN_spec hk.2 l hl))
  exact ⟨h1, h2.trans szs, h3.trans zcs⟩

end CertificateChecks.KernelSporSch.HeQ17

end

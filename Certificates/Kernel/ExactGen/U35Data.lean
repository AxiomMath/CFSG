module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.IntWordsCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.ExactGen.Parse
public import Certificates.Data.ExactGen.U35Text
public meta import CFSG.LocalAnalysis.ComponentClassification.ExactGenU35Inputs
public meta import Mathlib

namespace CertificateChecks.KernelEG.U35

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

public meta def fcM : FCCert := u35FC ()

public meta def toksM : Array (List Int) := #[(fcTokens ExactGenData.u35Text).toList]

public meta def dOf (cd : ChainData) : Array (List Int) := cd.W.extract cd.k cd.W.size

public meta def btOf (j : Nat) : Array (Array Nat) :=
  let r := fcM.reps[j]!
  bfsAux 50 fcM.ctx.chP.S (CFSG.Certificates.Native.rawInvs 50 fcM.ctx.chP.S) r.par
    #[r.nuA 50 fcM.ctx]

public meta def bt0 : Array (Array Nat) := btOf 0
public meta def bt1 : Array (Array Nat) := btOf 1

public meta def dP : Array (List Int) := dOf fcM.ctx.chP
public meta def dN : Array (List Int) := dOf fcM.ctx.chN
public meta def dTN : Array (List Int) := dOf fcM.chTN
public meta def dC0 : Array (List Int) := dOf fcM.reps[0]!.chC
public meta def dX0 : Array (List Int) := dOf fcM.reps[0]!.chX
public meta def dT0 : Array (List Int) := dOf fcM.reps[0]!.chT
public meta def dC1 : Array (List Int) := dOf fcM.reps[1]!.chC
public meta def dX1 : Array (List Int) := dOf fcM.reps[1]!.chX
public meta def dT1 : Array (List Int) := dOf fcM.reps[1]!.chT

public meta def sP : Array (Array Nat) := fcM.ctx.chP.S
public meta def sN : Array (Array Nat) := fcM.ctx.chN.S
public meta def sTN : Array (Array Nat) := fcM.chTN.S
public meta def sC0 : Array (Array Nat) := fcM.reps[0]!.chC.S
public meta def sX0 : Array (Array Nat) := fcM.reps[0]!.chX.S
public meta def sT0 : Array (Array Nat) := fcM.reps[0]!.chT.S
public meta def sC1 : Array (Array Nat) := fcM.reps[1]!.chC.S
public meta def sX1 : Array (Array Nat) := fcM.reps[1]!.chX.S
public meta def sT1 : Array (Array Nat) := fcM.reps[1]!.chT.S

public meta def bP : Array Nat := fcM.ctx.chP.base.toArray
public meta def bN : Array Nat := fcM.ctx.chN.base.toArray
public meta def bTN : Array Nat := fcM.chTN.base.toArray
public meta def bC0 : Array Nat := fcM.reps[0]!.chC.base.toArray
public meta def bX0 : Array Nat := fcM.reps[0]!.chX.base.toArray
public meta def bT0 : Array Nat := fcM.reps[0]!.chT.base.toArray
public meta def bC1 : Array Nat := fcM.reps[1]!.chC.base.toArray
public meta def bX1 : Array Nat := fcM.reps[1]!.chX.base.toArray
public meta def bT1 : Array Nat := fcM.reps[1]!.chT.base.toArray

end CertificateChecks.KernelEG.U35

public section

set_option maxRecDepth 1000000

#ks_chars CertificateChecks.KernelEG.U35.PT ExactGenData.u35Text

#kc_intwords CertificateChecks.KernelEG.U35.PTok CertificateChecks.KernelEG.U35.toksM

#kmisc_packarrs CertificateChecks.KernelEG.U35.BT0 CertificateChecks.KernelEG.U35.bt0 6
#kmisc_packarrs CertificateChecks.KernelEG.U35.BT1 CertificateChecks.KernelEG.U35.bt1 6

#kc_intwords CertificateChecks.KernelEG.U35.DP CertificateChecks.KernelEG.U35.dP
#kc_intwords CertificateChecks.KernelEG.U35.DN CertificateChecks.KernelEG.U35.dN
#kc_intwords CertificateChecks.KernelEG.U35.DTN CertificateChecks.KernelEG.U35.dTN
#kc_intwords CertificateChecks.KernelEG.U35.DC0 CertificateChecks.KernelEG.U35.dC0
#kc_intwords CertificateChecks.KernelEG.U35.DX0 CertificateChecks.KernelEG.U35.dX0
#kc_intwords CertificateChecks.KernelEG.U35.DT0 CertificateChecks.KernelEG.U35.dT0
#kc_intwords CertificateChecks.KernelEG.U35.DC1 CertificateChecks.KernelEG.U35.dC1
#kc_intwords CertificateChecks.KernelEG.U35.DX1 CertificateChecks.KernelEG.U35.dX1
#kc_intwords CertificateChecks.KernelEG.U35.DT1 CertificateChecks.KernelEG.U35.dT1

namespace CertificateChecks.KernelEG.U35

@[expose] noncomputable def C : CFSG.ComponentClassification.SolMax.SwapP2.ExactFin.FCCert :=
  CFSG.KC.ExactGen.parseFCL 50 PTok.head!

@[expose] noncomputable def BT (j : Nat) : Nat → Nat :=
  if j = 0 then BT0 else BT1

end CertificateChecks.KernelEG.U35

end

module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.IntWordsCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.ExactGen.Parse
public import Certificates.Data.ExactGen.J2Text
public meta import CFSG.LocalAnalysis.ComponentClassification.ExactGenJ2Inputs
public meta import Mathlib

namespace CertificateChecks.KernelEG.J2

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

public meta def fcM : FCCert := j2FC ()

public meta def toksM : Array (List Int) := #[(fcTokens ExactGenData.j2Text).toList]

public meta def dOf (cd : ChainData) : Array (List Int) := cd.W.extract cd.k cd.W.size

public meta def btOf (j : Nat) : Array (Array Nat) :=
  let r := fcM.reps[j]!
  bfsAux 315 fcM.ctx.chP.S (CFSG.Certificates.Native.rawInvs 315 fcM.ctx.chP.S) r.par
    #[r.nuA 315 fcM.ctx]

public meta def bt0 : Array (Array Nat) := btOf 0
public meta def bt1 : Array (Array Nat) := btOf 1
public meta def bt2 : Array (Array Nat) := btOf 2

public meta def dP : Array (List Int) := dOf fcM.ctx.chP
public meta def dN : Array (List Int) := dOf fcM.ctx.chN
public meta def dTN : Array (List Int) := dOf fcM.chTN
public meta def dC0 : Array (List Int) := dOf fcM.reps[0]!.chC
public meta def dX0 : Array (List Int) := dOf fcM.reps[0]!.chX
public meta def dT0 : Array (List Int) := dOf fcM.reps[0]!.chT
public meta def dC1 : Array (List Int) := dOf fcM.reps[1]!.chC
public meta def dX1 : Array (List Int) := dOf fcM.reps[1]!.chX
public meta def dT1 : Array (List Int) := dOf fcM.reps[1]!.chT
public meta def dC2 : Array (List Int) := dOf fcM.reps[2]!.chC
public meta def dX2 : Array (List Int) := dOf fcM.reps[2]!.chX
public meta def dT2 : Array (List Int) := dOf fcM.reps[2]!.chT

public meta def sP : Array (Array Nat) := fcM.ctx.chP.S
public meta def sN : Array (Array Nat) := fcM.ctx.chN.S
public meta def sTN : Array (Array Nat) := fcM.chTN.S
public meta def sC0 : Array (Array Nat) := fcM.reps[0]!.chC.S
public meta def sX0 : Array (Array Nat) := fcM.reps[0]!.chX.S
public meta def sT0 : Array (Array Nat) := fcM.reps[0]!.chT.S
public meta def sC1 : Array (Array Nat) := fcM.reps[1]!.chC.S
public meta def sX1 : Array (Array Nat) := fcM.reps[1]!.chX.S
public meta def sT1 : Array (Array Nat) := fcM.reps[1]!.chT.S
public meta def sC2 : Array (Array Nat) := fcM.reps[2]!.chC.S
public meta def sX2 : Array (Array Nat) := fcM.reps[2]!.chX.S
public meta def sT2 : Array (Array Nat) := fcM.reps[2]!.chT.S

public meta def bP : Array Nat := fcM.ctx.chP.base.toArray
public meta def bN : Array Nat := fcM.ctx.chN.base.toArray
public meta def bTN : Array Nat := fcM.chTN.base.toArray
public meta def bC0 : Array Nat := fcM.reps[0]!.chC.base.toArray
public meta def bX0 : Array Nat := fcM.reps[0]!.chX.base.toArray
public meta def bT0 : Array Nat := fcM.reps[0]!.chT.base.toArray
public meta def bC1 : Array Nat := fcM.reps[1]!.chC.base.toArray
public meta def bX1 : Array Nat := fcM.reps[1]!.chX.base.toArray
public meta def bT1 : Array Nat := fcM.reps[1]!.chT.base.toArray
public meta def bC2 : Array Nat := fcM.reps[2]!.chC.base.toArray
public meta def bX2 : Array Nat := fcM.reps[2]!.chX.base.toArray
public meta def bT2 : Array Nat := fcM.reps[2]!.chT.base.toArray

end CertificateChecks.KernelEG.J2

public section

set_option maxRecDepth 1000000

#ks_chars CertificateChecks.KernelEG.J2.J2T ExactGenData.j2Text

#kc_intwords CertificateChecks.KernelEG.J2.J2Tok CertificateChecks.KernelEG.J2.toksM

#kmisc_packarrs CertificateChecks.KernelEG.J2.BT0 CertificateChecks.KernelEG.J2.bt0 9
#kmisc_packarrs CertificateChecks.KernelEG.J2.BT1 CertificateChecks.KernelEG.J2.bt1 9
#kmisc_packarrs CertificateChecks.KernelEG.J2.BT2 CertificateChecks.KernelEG.J2.bt2 9

#kc_intwords CertificateChecks.KernelEG.J2.DP CertificateChecks.KernelEG.J2.dP
#kc_intwords CertificateChecks.KernelEG.J2.DN CertificateChecks.KernelEG.J2.dN
#kc_intwords CertificateChecks.KernelEG.J2.DTN CertificateChecks.KernelEG.J2.dTN
#kc_intwords CertificateChecks.KernelEG.J2.DC0 CertificateChecks.KernelEG.J2.dC0
#kc_intwords CertificateChecks.KernelEG.J2.DX0 CertificateChecks.KernelEG.J2.dX0
#kc_intwords CertificateChecks.KernelEG.J2.DT0 CertificateChecks.KernelEG.J2.dT0
#kc_intwords CertificateChecks.KernelEG.J2.DC1 CertificateChecks.KernelEG.J2.dC1
#kc_intwords CertificateChecks.KernelEG.J2.DX1 CertificateChecks.KernelEG.J2.dX1
#kc_intwords CertificateChecks.KernelEG.J2.DT1 CertificateChecks.KernelEG.J2.dT1
#kc_intwords CertificateChecks.KernelEG.J2.DC2 CertificateChecks.KernelEG.J2.dC2
#kc_intwords CertificateChecks.KernelEG.J2.DX2 CertificateChecks.KernelEG.J2.dX2
#kc_intwords CertificateChecks.KernelEG.J2.DT2 CertificateChecks.KernelEG.J2.dT2

namespace CertificateChecks.KernelEG.J2

@[expose] noncomputable def C : CFSG.ComponentClassification.SolMax.SwapP2.ExactFin.FCCert := CFSG.KC.ExactGen.parseFCL 315 J2Tok.head!

@[expose] noncomputable def BT (j : Nat) : Nat → Nat :=
  if j = 0 then BT0 else if j = 1 then BT1 else BT2

end CertificateChecks.KernelEG.J2

end

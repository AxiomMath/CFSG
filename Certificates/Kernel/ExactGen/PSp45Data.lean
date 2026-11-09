module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.IntWordsCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.ExactGen.Parse
public import Certificates.Data.ExactGen.PSp45Text
public import Certificates.Data.ExactGen.PSp45Rel
public meta import CFSG.LocalAnalysis.ComponentClassification.ExactGenPSp45Inputs
public meta import Mathlib

namespace CertificateChecks.KernelEG.PSp45

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin

public meta def fcM : FCCert := psp45FC ()

public meta def toksM : Array (List Int) := #[(fcTokens ExactGenData.psp45Text).toList]

public meta def dOf (cd : ChainData) : Array (List Int) := cd.W.extract cd.k cd.W.size

public meta def btOf (j : Nat) : Array (Array Nat) :=
  let r := fcM.reps[j]!
  bfsAux 156 fcM.ctx.chP.S (CFSG.Certificates.Native.rawInvs 156 fcM.ctx.chP.S) r.par
    #[r.nuA 156 fcM.ctx]

public meta def ftOf (j : Nat) : Array (Array Nat) :=
  let r := fcM.reps[j]!
  let S := fcM.ctx.chP.S
  let Si := CFSG.Certificates.Native.rawInvs 156 S
  let nu := r.nuA 156 fcM.ctx
  let f0 := ((List.range 156).filter fun i => nu[i]! == i).toArray
  r.par.foldl (fun L e => L.push (L[e.1]!.map fun x => (CFSG.Monster.B.Co2.Native.letterA S Si e.2)[x]!)) #[f0]

public meta def relRowsOf (j : Nat) : Array (Array Nat) :=
  let r := fcM.reps[j]!
  let S := fcM.ctx.chP.S
  let Si := CFSG.Certificates.Native.rawInvs 156 S
  let nu := r.nuA 156 fcM.ctx
  let f0 := ((List.range 156).filter fun i => (fcM.ctx.rel[i]!).testBit nu[i]!).toArray
  r.par.foldl (fun L e =>
    L.push (L[e.1]!.map fun x => (CFSG.Monster.B.Co2.Native.letterA S Si e.2)[x]!)) #[f0]

public meta def bt0 : Array (Array Nat) := btOf 0
public meta def bt1 : Array (Array Nat) := ftOf 1
public meta def bt2 : Array (Array Nat) := btOf 2
public meta def bt3 : Array (Array Nat) := relRowsOf 3

public meta def relPRows : Array (Array Nat) :=
  (fcM.ctx.relP.map fun q => ((List.range 30).map fun j => (q >>> (8 * j)) % 256).toArray).toArray

public meta def parRows (r c : Nat) : List (List (Nat × Int)) :=
  (List.range c).map fun j => (fcM.reps[r]!.par.drop (j * 1400)).take 1400

public meta def p1P : Array (List Int) := ((parRows 1 7).map (·.map fun e => (e.1 : Int))).toArray
public meta def p1L : Array (List Int) := ((parRows 1 7).map (·.map (·.2))).toArray
public meta def p3P : Array (List Int) := ((parRows 3 5).map (·.map fun e => (e.1 : Int))).toArray
public meta def p3L : Array (List Int) := ((parRows 3 5).map (·.map (·.2))).toArray

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
public meta def dC3 : Array (List Int) := dOf fcM.reps[3]!.chC
public meta def dX3 : Array (List Int) := dOf fcM.reps[3]!.chX
public meta def dT3 : Array (List Int) := dOf fcM.reps[3]!.chT

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
public meta def sC3 : Array (Array Nat) := fcM.reps[3]!.chC.S
public meta def sX3 : Array (Array Nat) := fcM.reps[3]!.chX.S
public meta def sT3 : Array (Array Nat) := fcM.reps[3]!.chT.S

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
public meta def bC3 : Array Nat := fcM.reps[3]!.chC.base.toArray
public meta def bX3 : Array Nat := fcM.reps[3]!.chX.base.toArray
public meta def bT3 : Array Nat := fcM.reps[3]!.chT.base.toArray

end CertificateChecks.KernelEG.PSp45

public section

set_option maxRecDepth 1000000

#ks_chars CertificateChecks.KernelEG.PSp45.PT ExactGenData.psp45Text

#kc_intwords CertificateChecks.KernelEG.PSp45.PTok CertificateChecks.KernelEG.PSp45.toksM

#kmisc_packarrs CertificateChecks.KernelEG.PSp45.BT0 CertificateChecks.KernelEG.PSp45.bt0 8
#kmisc_packarrs CertificateChecks.KernelEG.PSp45.BT1 CertificateChecks.KernelEG.PSp45.bt1 8
#kmisc_packarrs CertificateChecks.KernelEG.PSp45.BT2 CertificateChecks.KernelEG.PSp45.bt2 8
#kmisc_packarrs CertificateChecks.KernelEG.PSp45.BT3 CertificateChecks.KernelEG.PSp45.bt3 8
#kmisc_packarrs CertificateChecks.KernelEG.PSp45.RelRP CertificateChecks.KernelEG.PSp45.relPRows 8

#kc_intwords CertificateChecks.KernelEG.PSp45.Par1P CertificateChecks.KernelEG.PSp45.p1P
#kc_intwords CertificateChecks.KernelEG.PSp45.Par1L CertificateChecks.KernelEG.PSp45.p1L
#kc_intwords CertificateChecks.KernelEG.PSp45.Par3P CertificateChecks.KernelEG.PSp45.p3P
#kc_intwords CertificateChecks.KernelEG.PSp45.Par3L CertificateChecks.KernelEG.PSp45.p3L

#kc_intwords CertificateChecks.KernelEG.PSp45.DP CertificateChecks.KernelEG.PSp45.dP
#kc_intwords CertificateChecks.KernelEG.PSp45.DN CertificateChecks.KernelEG.PSp45.dN
#kc_intwords CertificateChecks.KernelEG.PSp45.DTN CertificateChecks.KernelEG.PSp45.dTN
#kc_intwords CertificateChecks.KernelEG.PSp45.DC0 CertificateChecks.KernelEG.PSp45.dC0
#kc_intwords CertificateChecks.KernelEG.PSp45.DX0 CertificateChecks.KernelEG.PSp45.dX0
#kc_intwords CertificateChecks.KernelEG.PSp45.DT0 CertificateChecks.KernelEG.PSp45.dT0
#kc_intwords CertificateChecks.KernelEG.PSp45.DC1 CertificateChecks.KernelEG.PSp45.dC1
#kc_intwords CertificateChecks.KernelEG.PSp45.DX1 CertificateChecks.KernelEG.PSp45.dX1
#kc_intwords CertificateChecks.KernelEG.PSp45.DT1 CertificateChecks.KernelEG.PSp45.dT1
#kc_intwords CertificateChecks.KernelEG.PSp45.DC2 CertificateChecks.KernelEG.PSp45.dC2
#kc_intwords CertificateChecks.KernelEG.PSp45.DX2 CertificateChecks.KernelEG.PSp45.dX2
#kc_intwords CertificateChecks.KernelEG.PSp45.DT2 CertificateChecks.KernelEG.PSp45.dT2
#kc_intwords CertificateChecks.KernelEG.PSp45.DC3 CertificateChecks.KernelEG.PSp45.dC3
#kc_intwords CertificateChecks.KernelEG.PSp45.DX3 CertificateChecks.KernelEG.PSp45.dX3
#kc_intwords CertificateChecks.KernelEG.PSp45.DT3 CertificateChecks.KernelEG.PSp45.dT3

namespace CertificateChecks.KernelEG.PSp45

@[expose] noncomputable def C : CFSG.ComponentClassification.SolMax.SwapP2.ExactFin.FCCert :=
  let c := CFSG.KC.ExactGen.parseFCL 156 PTok.head!
  { c with
    ctx := { c.ctx with rel := ExactGenData.psp45Rel, relP := ExactGenData.psp45RelP, relK := 30 } }

@[expose] noncomputable def BT (j : Nat) : Nat → Nat :=
  if j = 0 then BT0 else if j = 1 then BT1 else if j = 2 then BT2 else BT3

@[expose] noncomputable def RelRG (a : Nat) : Nat := bif Nat.blt a 156 then RelRP a else 0

end CertificateChecks.KernelEG.PSp45

end

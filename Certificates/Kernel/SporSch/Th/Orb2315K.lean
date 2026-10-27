
module

public import Certificates.Kernel.SporSch.Th.GenOrb
public import Certificates.Kernel.SporSch.Th.Plane2320K
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Co1B.GenTri2045
public import CFSG.Sporadic.ThSchreier.OrbitCheck819Inputs
meta import CFSG.Sporadic.ThSchreier.OrbitCheck819Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelSporSch.ThO.M CFSG.KS.SporSchGen.matsL
#kss_natlist CertificateChecks.KernelSporSch.ThO.S CFSG.KS.SporSchGen.sortedL
#kss_natlist CertificateChecks.KernelSporSch.ThO.SG CFSG.KS.SporSchGen.sgL
#kss_natlist CertificateChecks.KernelSporSch.ThO.TU CFSG.KS.SporSchGen.soL
#kss_natlist CertificateChecks.KernelSporSch.ThO.PAR CFSG.Sporadic.ThSchreier.centOrbitPar
#kss_natlist CertificateChecks.KernelSporSch.ThO.LAB CFSG.Sporadic.ThSchreier.centOrbitLab
#kss_natlist CertificateChecks.KernelSporSch.ThO.EDG CFSG.Sporadic.ThSchreier.centOrbitEdges

namespace CertificateChecks.KernelSporSch.ThO

open CFSG.KC.Enum CFSG.KS.SporSch

@[expose] noncomputable def A : Nat := M 0
@[expose] noncomputable def B : Nat := M 1
@[expose] noncomputable def BB : Nat := M 2
@[expose] noncomputable def X : Nat := M 3
@[expose] noncomputable def Y : Nat := M 4
@[expose] noncomputable def YY : Nat := M 5
@[expose] noncomputable def V : Nat := M 6
@[expose] noncomputable def VI : Nat := M 7
@[expose] noncomputable def T : Nat := M 8

@[expose] noncomputable def eB (q : Nat) : Bool :=
  allBlk (Nat.mul q 7) (entK S SG TU PAR LAB EDG T X Y YY) 7

@[expose] noncomputable def sB (q : Nat) : Bool := allBlk (Nat.mul q 7) (srtK S) 7

end CertificateChecks.KernelSporSch.ThO

#kc_slices CertificateChecks.KernelSporSch.ThO.E CertificateChecks.KernelSporSch.ThO.eB 117
#kc_slices CertificateChecks.KernelSporSch.ThO.R CertificateChecks.KernelSporSch.ThO.sB 117

namespace CertificateChecks.KernelSporSch.ThO

open CFSG.KC.Enum CFSG.KS.SporSch

theorem hE : ∀ q < 117, allBlk (Nat.mul q 7) (entK S SG TU PAR LAB EDG T X Y YY) 7 = true := E.all

theorem hS : ∀ q < 117, allBlk (Nat.mul q 7) (srtK S) 7 = true := R.all

end CertificateChecks.KernelSporSch.ThO

namespace CertificateChecks.KernelSporSch.ThOrbK

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.ThSchreier
open CertificateChecks.KernelSporSch

theorem bA : allN 248 (fun i => Nat.beq (unpk ThO.A i) (ThA i)) = true := by quickRfl
theorem bB : allN 248 (fun i => Nat.beq (unpk ThO.B i) (ThB i)) = true := by quickRfl
theorem bBB : Nat.beq (mulPk ThO.B ThO.B) ThO.BB = true := by quickRfl
theorem bYY : Nat.beq (mulPk ThO.Y ThO.Y) ThO.YY = true := by quickRfl
theorem bT : Nat.beq (mulPk (mulPk ThO.VI ThO.A) ThO.V) ThO.T = true := by quickRfl

theorem wX : Nat.beq (wordR ThO.A ThO.B ThO.BB (CFSG.Sporadic.Th.Native.xWord ())) ThO.X = true := by
  quickRfl
theorem wY : Nat.beq (wordR ThO.A ThO.B ThO.BB (CFSG.Sporadic.Th.Native.yWord ())) ThO.Y = true := by
  quickRfl
theorem wV : Nat.beq (wordR ThO.A ThO.B ThO.BB transporterWord) ThO.V = true := by quickRfl
theorem wVI : Nat.beq (wordR ThO.A ThO.B ThO.BB (invWord transporterWord)) ThO.VI = true := by
  quickRfl

theorem bPar : Nat.beq (thBindK false ThO.PAR ThPar.chars) (2 * 819) = true := by quickRfl
theorem bLab : Nat.beq (thBindK false ThO.LAB ThLab.chars) (2 * 819) = true := by quickRfl
theorem bEdg : Nat.beq (thBindK false ThO.EDG ThEdg.chars) (2 * 1638) = true := by quickRfl

end CertificateChecks.KernelSporSch.ThOrbK

end

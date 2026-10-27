module

public import Certificates.Kernel.SporSch.Tits.Stab2270K
public import Certificates.Kernel.SporSch.Tits.GenPrim
public import CFSG.Certificates.Kernel.SporSch.TitsPrimSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLatticeCheckInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsOverInputs
meta import CFSG.Sporadic.Schreier.TitsData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeInvariantMerge
public import CFSG.Sporadic.Schreier.TitsLocal
public import CFSG.Sporadic.Schreier.TitsStabCheck

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLocalQT.Tits4139

meta def repsS : List Nat := [0, 1, 2, 4, 6, 9, 13, 19, 26, 38, 51, 72, 99, 141, 194, 281, 315, 464]

end CertificateChecks.KernelLocalQT.Tits4139

#kst_words CertificateChecks.KernelLocalQT.TitsSW 8775 14 CertificateChecks.KernelSporSch.TitsSF.T 13
  CFSG.Sporadic.Schreier.Tits.titsSWords
#kst_forest CertificateChecks.KernelLocalQT.TitsFS 8775 14 CertificateChecks.KernelLocalQT.TitsSW.W 0 3
  CertificateChecks.KernelLocalQT.Tits4139.repsS

namespace CertificateChecks.KernelLocalQT.Tits4139

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.QuasithinUnique.Setup.X6.TitsLat
open CertificateChecks.KernelSporSch CertificateChecks.KernelLocalQT

theorem sW0 : wordW 8775 14 TitsSF.T TitsSF.TI 13 titsSWords[0]! (TitsSW.W 0) = true := by quickRfl
theorem sW1 : wordW 8775 14 TitsSF.T TitsSF.TI 13 titsSWords[1]! (TitsSW.W 1) = true := by quickRfl
theorem sW2 : wordW 8775 14 TitsSF.T TitsSF.TI 13 titsSWords[2]! (TitsSW.W 2) = true := by quickRfl
theorem sCan : allN 3 (fun i => canonK 8775 14 (mask 14) (8775 * 14) (TitsSW.W i)) = true := by
  quickRfl

theorem fS : bfsTK 8775 14 TitsSW.W 3 18 TitsFS.REP TitsFS.N TitsFS.Q TitsFS.POS TitsFS.C TitsFS.LAB
    TitsFS.DEP TitsFS.PAR TitsFS.GL = true := by quickRfl
theorem lS : labOKK 8775 14 TitsSW.W 3 18 TitsFS.LAB TitsFS.REP TitsFS.DEP TitsFS.PAR TitsFS.GL =
    true := by quickRfl
theorem cS : (List.range 18).map (cntK 8775 14 TitsFS.LAB) =
    [1, 2, 4, 8, 8, 16, 32, 64, 64, 128, 256, 512, 512, 1024, 1024, 2048, 1024, 2048] := by decide
theorem rSe : titsSFlagReps = unpack 18 14 TitsFS.REP := by decide

theorem s0 : allN 8775 (fun x => beqB (Nat.beq (pgW 14 TitsFS.LAB x) 0) (memN x [0])) = true := by
  quickRfl
theorem s1 : allN 8775 (fun x => beqB (Nat.beq (pgW 14 TitsFS.LAB x) 1) (memN x [1, 3])) = true := by
  quickRfl
theorem s2 : allN 8775 (fun x => beqB (Nat.beq (pgW 14 TitsFS.LAB x) 2) (memN x [2, 5, 10, 20])) =
    true := by quickRfl

theorem pts : allN 15 (fun l => bAnd(lettersK 13 (titsFlagRepWord l),
    bAnd(lettersK 13 (titsFlagZWord l),
    bAnd(Nat.beq (wPtG 14 TitsSF.T TitsSF.TI (titsFlagRepWord l) 0) (titsFlagMergeReps.getD l 0),
    memN (wPtG 14 TitsSF.T TitsSF.TI (titsFlagZWord l) 0) [2, 5, 10, 20])))) = true := by quickRfl

end CertificateChecks.KernelLocalQT.Tits4139

end

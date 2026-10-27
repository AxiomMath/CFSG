
module

public import Certificates.Kernel.Sporadic.OddCore.Suz2304
public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import CFSG.Sporadic.SuzOddCore.CertChainCheckInputs
meta import CFSG.Sporadic.SuzOddCore.CertChainCheckInputs
import CFSG.Sporadic.SuzOddCore.Arrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Perm.Native

meta def certLettersM : Array CFSG.Sporadic.Th.Native.Table := certLetters

meta def lv0M : Array Nat := certLevelLetters 0
meta def lv1M : Array Nat := certLevelLetters 1
meta def lv2M : Array Nat := certLevelLetters 2
meta def lv3M : Array Nat := certLevelLetters 3
meta def lv4M : Array Nat := certLevelLetters 4
meta def lv5M : Array Nat := certLevelLetters 5

meta def fixBitsM : List Nat :=
  (List.range 60).map fun b => if (certArr (b / 6 + 2))[b % 6]! == b % 6 then 1 else 0

meta def lvL0 : List Nat := lv0M.toList
meta def lvL1 : List Nat := lv1M.toList
meta def lvL2 : List Nat := lv2M.toList
meta def lvL3 : List Nat := lv3M.toList

end CertificateChecks.KernelSpor.OddCore

#ktbfs CertificateChecks.KernelSpor.CT0 22880 0 CertificateChecks.KernelSpor.OddCore.certLettersM
  CertificateChecks.KernelSpor.OddCore.lv0M
#ktbfs CertificateChecks.KernelSpor.CT1 22880 1 CertificateChecks.KernelSpor.OddCore.certLettersM
  CertificateChecks.KernelSpor.OddCore.lv1M
#ktbfs CertificateChecks.KernelSpor.CT2 22880 2 CertificateChecks.KernelSpor.OddCore.certLettersM
  CertificateChecks.KernelSpor.OddCore.lv2M
#ktbfs CertificateChecks.KernelSpor.CT3 22880 3 CertificateChecks.KernelSpor.OddCore.certLettersM
  CertificateChecks.KernelSpor.OddCore.lv3M
#ktbfs CertificateChecks.KernelSpor.CT4 22880 4 CertificateChecks.KernelSpor.OddCore.certLettersM
  CertificateChecks.KernelSpor.OddCore.lv4M
#ktbfs CertificateChecks.KernelSpor.CT5 22880 5 CertificateChecks.KernelSpor.OddCore.certLettersM
  CertificateChecks.KernelSpor.OddCore.lv5M

#knatlist CertificateChecks.KernelSpor.OddCore.lvK0 CertificateChecks.KernelSpor.OddCore.lvL0
#knatlist CertificateChecks.KernelSpor.OddCore.lvK1 CertificateChecks.KernelSpor.OddCore.lvL1
#knatlist CertificateChecks.KernelSpor.OddCore.lvK2 CertificateChecks.KernelSpor.OddCore.lvL2
#knatlist CertificateChecks.KernelSpor.OddCore.lvK3 CertificateChecks.KernelSpor.OddCore.lvL3
#knatlist CertificateChecks.KernelSpor.OddCore.fixBits CertificateChecks.KernelSpor.OddCore.fixBitsM

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Row CFSG.KS.TBfs
open CFSG.KS.Mathieu

@[expose] noncomputable def certLt (l x : Nat) : Nat :=
  nIf(Nat.beq (Nat.land l 1) 0,
    rg 15 (mask 15) SuzCertT.F (ocs (Nat.shiftRight l 1)) x,
    rg 15 (mask 15) SuzCertI (ocs (Nat.shiftRight l 1)) x)

theorem gens_rows : bAnd(allN 715 (fun j => Nat.beq (SuzCertT.F (Nat.add 1430 j)) (SuzCertT.F j)),
    allN 715 (fun j => Nat.beq (SuzCertT.F (Nat.add 2145 j)) (SuzCertT.F (Nat.add 715 j)))) =
    true := by
  quickRfl

theorem fix_ok : allN 60 (fun b => Nat.beq
    (nIf(Nat.beq (cg (Nat.add (Nat.div b 6) 2) (Nat.mod b 6)) (Nat.mod b 6), 1, 0))
    (nget fixBits b)) = true := by
  quickRfl

theorem d2 : allN 22880 (fun x => Nat.beq (cg 4 x) (wpt (certDerivs[2]!) x)) = true := by quickRfl
theorem d3 : allN 22880 (fun x => Nat.beq (cg 5 x) (wpt (certDerivs[3]!) x)) = true := by quickRfl
theorem d4 : allN 22880 (fun x => Nat.beq (cg 6 x) (wpt (certDerivs[4]!) x)) = true := by quickRfl
theorem d5 : allN 22880 (fun x => Nat.beq (cg 7 x) (wpt (certDerivs[5]!) x)) = true := by quickRfl
theorem d6 : allN 22880 (fun x => Nat.beq (cg 8 x) (wpt (certDerivs[6]!) x)) = true := by quickRfl
theorem d7 : allN 22880 (fun x => Nat.beq (cg 9 x) (wpt (certDerivs[7]!) x)) = true := by quickRfl
theorem d8 : allN 22880 (fun x => Nat.beq (cg 10 x) (wpt (certDerivs[8]!) x)) = true := by quickRfl
theorem d9 : allN 22880 (fun x => Nat.beq (cg 11 x) (wpt (certDerivs[9]!) x)) = true := by quickRfl

theorem t0_hd : tbfsHdK 22880 0 CT0.cnt CT0.PTS CT0.POS CT0.PAR CT0.LAB = true := by quickRfl
theorem t1_hd : tbfsHdK 22880 1 CT1.cnt CT1.PTS CT1.POS CT1.PAR CT1.LAB = true := by quickRfl
theorem t2_hd : tbfsHdK 22880 2 CT2.cnt CT2.PTS CT2.POS CT2.PAR CT2.LAB = true := by quickRfl
theorem t3_hd : tbfsHdK 22880 3 CT3.cnt CT3.PTS CT3.POS CT3.PAR CT3.LAB = true := by quickRfl
theorem t4_hd : tbfsHdK 22880 4 CT4.cnt CT4.PTS CT4.POS CT4.PAR CT4.LAB = true := by quickRfl
theorem t5_hd : tbfsHdK 22880 5 CT5.cnt CT5.PTS CT5.POS CT5.PAR CT5.LAB = true := by quickRfl

theorem t0_s0 : tbfsSlK 22880 CT0.cnt 20 certLt (nget lvK0) CT0.PTS CT0.POS CT0.PAR CT0.LAB CT0.TI
    0 2860 = true := by quickRfl
theorem t0_s1 : tbfsSlK 22880 CT0.cnt 20 certLt (nget lvK0) CT0.PTS CT0.POS CT0.PAR CT0.LAB CT0.TI
    2860 2860 = true := by quickRfl
theorem t0_s2 : tbfsSlK 22880 CT0.cnt 20 certLt (nget lvK0) CT0.PTS CT0.POS CT0.PAR CT0.LAB CT0.TI
    5720 2860 = true := by quickRfl
theorem t0_s3 : tbfsSlK 22880 CT0.cnt 20 certLt (nget lvK0) CT0.PTS CT0.POS CT0.PAR CT0.LAB CT0.TI
    8580 2860 = true := by quickRfl
theorem t0_s4 : tbfsSlK 22880 CT0.cnt 20 certLt (nget lvK0) CT0.PTS CT0.POS CT0.PAR CT0.LAB CT0.TI
    11440 2860 = true := by quickRfl
theorem t0_s5 : tbfsSlK 22880 CT0.cnt 20 certLt (nget lvK0) CT0.PTS CT0.POS CT0.PAR CT0.LAB CT0.TI
    14300 2860 = true := by quickRfl
theorem t0_s6 : tbfsSlK 22880 CT0.cnt 20 certLt (nget lvK0) CT0.PTS CT0.POS CT0.PAR CT0.LAB CT0.TI
    17160 2860 = true := by quickRfl
theorem t0_s7 : tbfsSlK 22880 CT0.cnt 20 certLt (nget lvK0) CT0.PTS CT0.POS CT0.PAR CT0.LAB CT0.TI
    20020 2860 = true := by quickRfl

theorem t1_s0 : tbfsSlK 22880 CT1.cnt 16 certLt (nget lvK1) CT1.PTS CT1.POS CT1.PAR CT1.LAB CT1.TI
    0 2127 = true := by quickRfl
theorem t1_s1 : tbfsSlK 22880 CT1.cnt 16 certLt (nget lvK1) CT1.PTS CT1.POS CT1.PAR CT1.LAB CT1.TI
    2127 2127 = true := by quickRfl
theorem t1_s2 : tbfsSlK 22880 CT1.cnt 16 certLt (nget lvK1) CT1.PTS CT1.POS CT1.PAR CT1.LAB CT1.TI
    4254 2127 = true := by quickRfl
theorem t1_s3 : tbfsSlK 22880 CT1.cnt 16 certLt (nget lvK1) CT1.PTS CT1.POS CT1.PAR CT1.LAB CT1.TI
    6381 2127 = true := by quickRfl

theorem t2_s : tbfsSlK 22880 CT2.cnt 12 certLt (nget lvK2) CT2.PTS CT2.POS CT2.PAR CT2.LAB CT2.TI
    0 1152 = true := by quickRfl
theorem t3_s : tbfsSlK 22880 CT3.cnt 2 certLt (nget lvK3) CT3.PTS CT3.POS CT3.PAR CT3.LAB CT3.TI
    0 2 = true := by quickRfl
theorem t4_s : tbfsSlK 22880 CT4.cnt 0 certLt (fun _ => 0) CT4.PTS CT4.POS CT4.PAR CT4.LAB CT4.TI
    0 1 = true := by quickRfl
theorem t5_s : tbfsSlK 22880 CT5.cnt 0 certLt (fun _ => 0) CT5.PTS CT5.POS CT5.PAR CT5.LAB CT5.TI
    0 1 = true := by quickRfl

end CertificateChecks.KernelSpor.OddCore

end

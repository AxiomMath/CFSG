module

public import Certificates.Kernel.Sporadic.OddCore.McLL
public import Certificates.Kernel.Sporadic.OddCore.PEnumFamCmd
meta import CFSG.Sporadic.SmallOddCore.McLLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McL2287

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore

meta def repsM : Array (Array Nat) :=
  (List.range 14).toArray.map fun l => wordTabS 35 mclXGens (mclXWords.getD l [])

end CertificateChecks.KernelSpor.McL2287

#kpenumfam CertificateChecks.KernelSpor.MOF 35 6 true CertificateChecks.KernelSpor.McL2287.xgM
  CertificateChecks.KernelSpor.McL2287.xiM CertificateChecks.KernelSpor.McL2287.repsM 5000

namespace CertificateChecks.KernelSpor.McL2287

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Mathieu CFSG.KC.Misc.HexAt

theorem fam_g : allN 2 (fun k => bAnd(Nat.beq (MOF.G k) (MXE.G k), Nat.beq (MOF.GI k) (MXI k))) =
    true := by
  quickRfl

@[expose] noncomputable def orbK (l : Nat) : Bool :=
  bAnd(penumHdK (MOF.R l) (MOF.C l) 5000 (offF MOF.T (MOF.TO l)) (offF MOF.PL (MOF.PLO l)),
    penumSlK 35 6 (mask 6) (35 * 6) true MOF.G MOF.GI MOF.k (MOF.C l) (offF MOF.T (MOF.TO l))
      (offF MOF.PL (MOF.PLO l)) (offF MOF.POS (MOF.POSO l)) (offF MOF.SRT (MOF.SRTO l))
      (offF MOF.SRI (MOF.SRIO l)) 0 (MOF.C l))

theorem o0 : orbK 0 = true := by quickRfl
theorem o1 : orbK 1 = true := by quickRfl
theorem o2 : orbK 2 = true := by quickRfl
theorem o3 : orbK 3 = true := by quickRfl
theorem o4 : orbK 4 = true := by quickRfl
theorem o5 : orbK 5 = true := by quickRfl
theorem o6 : orbK 6 = true := by quickRfl
theorem o7 : orbK 7 = true := by quickRfl
theorem o8 : orbK 8 = true := by quickRfl
theorem o9 : orbK 9 = true := by quickRfl
theorem o10 : orbK 10 = true := by quickRfl
theorem o11 : orbK 11 = true := by quickRfl
theorem o12 : orbK 12 = true := by quickRfl
theorem o13 : orbK 13 = true := by quickRfl

theorem reps_ok : allN 14 (fun l => bAnd(Nat.beq (MOF.R l)
    (wordTabK 35 6 (mask 6) (pidn 35 6) MXE.G (lget2 mclXWords l)),
    Nat.beq (MOF.C l) (nget mclXSizes l))) = true := by
  quickRfl

theorem notin : allN 14 (fun l => allN 14 (fun l' => bIf(Nat.beq l l', true,
    allN (MOF.C l) (fun q => bIf(Nat.beq (offF MOF.T (MOF.TO l) q) (MOF.R l'), false, true))))) =
    true := by
  quickRfl

end CertificateChecks.KernelSpor.McL2287

end

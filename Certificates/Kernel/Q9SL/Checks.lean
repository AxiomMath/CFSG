module

public import Certificates.Data.Kernel.Q9SL.Enc
public import Certificates.Kernel.Q9SL.Data
import all CFSG.GH74.GLS.Stage4.Q9.ModelBaseInputs
import all CFSG.GH74.GLS.Stage4.Q9.ModelBase
import all CFSG.GH74.GLS.Stage4.Q9.TablesInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelQ9SL

open CFSG.KC.Q9SL CFSG.GH74.GLS.Stage4.Q9

theorem ch5102enc : (allSL2.map enc == CFSG.KD.Q9SL.L) = true := by decide +kernel

theorem ch5102sort : ckSort CFSG.KD.Q9SL.L = true := by quickRfl

theorem ch5102lp : ckLP CFSG.KD.Q9SL.L CFSG.KD.Q9SL.LP = true := by quickRfl

theorem ch5102rep : ckRep CFSG.KD.Q9SL.R CFSG.KD.Q9SL.RP = true := by quickRfl

theorem ch5102wit : ckWit CFSG.KD.Q9SL.L CFSG.KD.Q9SL.LP CFSG.KD.Q9SL.RP CFSG.KD.Q9SL.W = true := by
  quickRfl

theorem ch5102conj : ckConj CFSG.KD.Q9SL.L CFSG.KD.Q9SL.RP = true := by quickRfl

theorem ch5102neg : ckNeg CFSG.KD.Q9SL.L = true := by quickRfl

theorem ch5102sig : ckSig CFSG.KD.Q9SL.L = true := by quickRfl

theorem ch5102inv : ckInv CFSG.KD.Q9SL.L = true := by quickRfl

theorem ch5102cnt : ckCnt CFSG.KD.Q9SL.L = true := by quickRfl

theorem ch5102zero : ckZero CFSG.KD.Q9SL.L = true := by quickRfl

theorem ch5102ord : ckOrd CFSG.KD.Q9SL.L = true := by quickRfl

end CertificateChecks.KernelQ9SL

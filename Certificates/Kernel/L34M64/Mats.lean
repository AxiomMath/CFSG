module

public import Certificates.Data.Kernel.L34M64.Twin
public import Certificates.Kernel.L34M64.Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelL34M64

open CFSG.KC.L34M64 CFSG.KD.L34M64 CFSG.Quasithin.H13.Ch9.L34M CFSG.Quasithin.H13.Ch9.Herm9

theorem ch7241x12_0 :
    matChk (adM (um (f4c 0) 0 0) (um (f4c 0) 0 0)) (PX12.getD 0 0) (X12.getD 0 []) = true := by
  quickRfl

theorem ch7241x12_1 :
    matChk (adM (um (f4c 1) 0 0) (um (f4c 1) 0 0)) (PX12.getD 1 0) (X12.getD 1 []) = true := by
  quickRfl

theorem ch7241x12_2 :
    matChk (adM (um (f4c 2) 0 0) (um (f4c 2) 0 0)) (PX12.getD 2 0) (X12.getD 2 []) = true := by
  quickRfl

theorem ch7241x12_3 :
    matChk (adM (um (f4c 3) 0 0) (um (f4c 3) 0 0)) (PX12.getD 3 0) (X12.getD 3 []) = true := by
  quickRfl

theorem ch7241x13_0 :
    matChk (adM (um 0 (f4c 0) 0) (um 0 (f4c 0) 0)) (PX13.getD 0 0) (X13.getD 0 []) = true := by
  quickRfl

theorem ch7241x13_1 :
    matChk (adM (um 0 (f4c 1) 0) (um 0 (f4c 1) 0)) (PX13.getD 1 0) (X13.getD 1 []) = true := by
  quickRfl

theorem ch7241x13_2 :
    matChk (adM (um 0 (f4c 2) 0) (um 0 (f4c 2) 0)) (PX13.getD 2 0) (X13.getD 2 []) = true := by
  quickRfl

theorem ch7241x13_3 :
    matChk (adM (um 0 (f4c 3) 0) (um 0 (f4c 3) 0)) (PX13.getD 3 0) (X13.getD 3 []) = true := by
  quickRfl

theorem ch7241x23_0 :
    matChk (adM (um 0 0 (f4c 0)) (um 0 0 (f4c 0))) (PX23.getD 0 0) (X23.getD 0 []) = true := by
  quickRfl

theorem ch7241x23_1 :
    matChk (adM (um 0 0 (f4c 1)) (um 0 0 (f4c 1))) (PX23.getD 1 0) (X23.getD 1 []) = true := by
  quickRfl

theorem ch7241x23_2 :
    matChk (adM (um 0 0 (f4c 2)) (um 0 0 (f4c 2))) (PX23.getD 2 0) (X23.getD 2 []) = true := by
  quickRfl

theorem ch7241x23_3 :
    matChk (adM (um 0 0 (f4c 3)) (um 0 0 (f4c 3))) (PX23.getD 3 0) (X23.getD 3 []) = true := by
  quickRfl

theorem ch7241gm : matChk gM PGM GR = true := by
  quickRfl

theorem ch7241fld : colsChk fldP FLD 0 = true := by
  quickRfl

theorem ch7241len :
    (X12.length == 4 && X13.length == 4 && X23.length == 4 &&
      CFSG.KD.L34M64.U.length == 64) = true := by
  quickRfl

end CertificateChecks.KernelL34M64

module

public import Certificates.Kernel.PlusFrame.Data
public import Certificates.Kernel.PlusQuandle.Data
public import Certificates.Data.Kernel.PlusFrameK

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelPlusFr

open CFSG.KC.PlusFrameK CertificateChecks.KernelPlusQ

theorem ch1383004_ds : dsOK DS = true := by decide +kernel
theorem ch1383004_da : daOK DA = true := by decide +kernel

theorem ch1383004a_0 : autOK R DS DA 0 5 = true := by decide +kernel
theorem ch1383004a_1 : autOK R DS DA 5 10 = true := by decide +kernel
theorem ch1383004a_2 : autOK R DS DA 10 15 = true := by decide +kernel
theorem ch1383004a_3 : autOK R DS DA 15 20 = true := by decide +kernel
theorem ch1383004a_4 : autOK R DS DA 20 25 = true := by decide +kernel
theorem ch1383004a_5 : autOK R DS DA 25 30 = true := by decide +kernel
theorem ch1383004a_6 : autOK R DS DA 30 35 = true := by decide +kernel
theorem ch1383004a_7 : autOK R DS DA 35 40 = true := by decide +kernel
theorem ch1383004a_8 : autOK R DS DA 40 45 = true := by decide +kernel
theorem ch1383004a_9 : autOK R DS DA 45 50 = true := by decide +kernel
theorem ch1383004a_10 : autOK R DS DA 50 55 = true := by decide +kernel
theorem ch1383004a_11 : autOK R DS DA 55 60 = true := by decide +kernel

end CertificateChecks.KernelPlusFr

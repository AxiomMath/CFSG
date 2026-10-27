module

public import Certificates.Kernel.MinusAut.Data
public import Certificates.Kernel.MinusQuandle.Data
public import Certificates.Data.Kernel.MinusAut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelMinusAut

open CFSG.KD.MinusAut CertificateChecks.KernelMinusQ

set_option profiler true

theorem ord_ok : ordOK R PP XX YY QQ = true := by decide +kernel

theorem homs_ok : homsOK R PP XX YY homs = true := by decide +kernel

theorem trans_ok : transOK R trans = true := by decide +kernel

theorem ch1383011m_0 : mainOK R PP XX YY QQ (kmask homs) 0 9 = true := by decide +kernel
theorem ch1383011m_1 : mainOK R PP XX YY QQ (kmask homs) 9 8 = true := by decide +kernel
theorem ch1383011m_2 : mainOK R PP XX YY QQ (kmask homs) 17 8 = true := by decide +kernel
theorem ch1383011m_3 : mainOK R PP XX YY QQ (kmask homs) 25 8 = true := by decide +kernel
theorem ch1383011m_4 : mainOK R PP XX YY QQ (kmask homs) 33 8 = true := by decide +kernel
theorem ch1383011m_5 : mainOK R PP XX YY QQ (kmask homs) 41 8 = true := by decide +kernel
theorem ch1383011m_6 : mainOK R PP XX YY QQ (kmask homs) 49 8 = true := by decide +kernel
theorem ch1383011m_7 : mainOK R PP XX YY QQ (kmask homs) 57 8 = true := by decide +kernel

end CertificateChecks.KernelMinusAut

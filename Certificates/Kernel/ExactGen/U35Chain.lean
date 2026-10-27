module

public import Certificates.Kernel.ExactGen.U35Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#ks_rawchain CertificateChecks.KernelEG.U35.CP 50 6 16 CertificateChecks.KernelEG.U35.sP
  CertificateChecks.KernelEG.U35.bP 6 CertificateChecks.KernelEG.U35.DP
#ks_rawchain CertificateChecks.KernelEG.U35.CN 50 6 16 CertificateChecks.KernelEG.U35.sN
  CertificateChecks.KernelEG.U35.bN 7 CertificateChecks.KernelEG.U35.DN
#ks_rawchain CertificateChecks.KernelEG.U35.CTN 50 6 16 CertificateChecks.KernelEG.U35.sTN
  CertificateChecks.KernelEG.U35.bTN 5 CertificateChecks.KernelEG.U35.DTN
#ks_rawchain CertificateChecks.KernelEG.U35.CC0 50 6 16 CertificateChecks.KernelEG.U35.sC0
  CertificateChecks.KernelEG.U35.bC0 2 CertificateChecks.KernelEG.U35.DC0
#ks_rawchain CertificateChecks.KernelEG.U35.CX0 50 6 16 CertificateChecks.KernelEG.U35.sX0
  CertificateChecks.KernelEG.U35.bX0 2 CertificateChecks.KernelEG.U35.DX0
#ks_rawchain CertificateChecks.KernelEG.U35.CT0 50 6 16 CertificateChecks.KernelEG.U35.sT0
  CertificateChecks.KernelEG.U35.bT0 2 CertificateChecks.KernelEG.U35.DT0
#ks_rawchain CertificateChecks.KernelEG.U35.CC1 50 6 16 CertificateChecks.KernelEG.U35.sC1
  CertificateChecks.KernelEG.U35.bC1 3 CertificateChecks.KernelEG.U35.DC1
#ks_rawchain CertificateChecks.KernelEG.U35.CX1 50 6 16 CertificateChecks.KernelEG.U35.sX1
  CertificateChecks.KernelEG.U35.bX1 2 CertificateChecks.KernelEG.U35.DX1
#ks_rawchain CertificateChecks.KernelEG.U35.CT1 50 6 16 CertificateChecks.KernelEG.U35.sT1
  CertificateChecks.KernelEG.U35.bT1 2 CertificateChecks.KernelEG.U35.DT1

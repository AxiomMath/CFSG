module

public import Certificates.Kernel.Misc.Perm.C2Data
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.RankThree.Native.Co2FiveMats
public import CFSG.RankThree.Native.Co2FiveData
public import CFSG.Sporadic.Co2Cert.Data
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.Misc.Perm.C2Data
meta import CFSG.RankThree.Native.Co2FiveMats
meta import CFSG.RankThree.Native.Co2FiveData
meta import CFSG.Sporadic.Co2Cert.Data
public import Certificates.Data.Kernel.Misc.HexFlat
public import Mathlib.GroupTheory.Schreier
meta import Mathlib.GroupTheory.Schreier

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.Co2K.HV CFSG.RankThree.Native.co2FiveVHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HV CFSG.RankThree.Native.co2FiveVHex 6 2300 22 1
#ks_chars CertificateChecks.KernelMisc.Co2K.HA CFSG.RankThree.Native.co2FiveHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HA CFSG.RankThree.Native.co2FiveHex 3 2300 12 38
#ks_chars CertificateChecks.KernelMisc.Co2K.HQP CFSG.RankThree.Native.co2FiveQMHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HQP CFSG.RankThree.Native.co2FiveQMHex 121 1 484 125
#ks_chars CertificateChecks.KernelMisc.Co2K.HQE CFSG.RankThree.Native.co2FiveQEHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HQE CFSG.RankThree.Native.co2FiveQEHex 3 2 12 125
#ks_chars CertificateChecks.KernelMisc.Co2K.HQR CFSG.RankThree.Native.co2FiveQRHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HQR CFSG.RankThree.Native.co2FiveQRHex 3 125 12 1
#ks_chars CertificateChecks.KernelMisc.Co2K.HQL CFSG.RankThree.Native.co2FiveQLHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HQL CFSG.RankThree.Native.co2FiveQLHex 3 125 12 1
#ks_chars CertificateChecks.KernelMisc.Co2K.HC0P CFSG.RankThree.Native.co2FiveC0MHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HC0P CFSG.RankThree.Native.co2FiveC0MHex 121 1 484 3000
#ks_chars CertificateChecks.KernelMisc.Co2K.HC0E CFSG.RankThree.Native.co2FiveC0EHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HC0E CFSG.RankThree.Native.co2FiveC0EHex 3 2 12 3000
#ks_chars CertificateChecks.KernelMisc.Co2K.HC0R CFSG.RankThree.Native.co2FiveC0RHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HC0R CFSG.RankThree.Native.co2FiveC0RHex 3 3000 12 1
#ks_chars CertificateChecks.KernelMisc.Co2K.HC0L CFSG.RankThree.Native.co2FiveC0LHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HC0L CFSG.RankThree.Native.co2FiveC0LHex 3 3000 12 1
#ks_chars CertificateChecks.KernelMisc.Co2K.HC1P CFSG.RankThree.Native.co2FiveC1MHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HC1P CFSG.RankThree.Native.co2FiveC1MHex 121 1 484 600
#ks_chars CertificateChecks.KernelMisc.Co2K.HC1E CFSG.RankThree.Native.co2FiveC1EHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HC1E CFSG.RankThree.Native.co2FiveC1EHex 3 3 12 600
#ks_chars CertificateChecks.KernelMisc.Co2K.HC1R CFSG.RankThree.Native.co2FiveC1RHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HC1R CFSG.RankThree.Native.co2FiveC1RHex 3 600 12 1
#ks_chars CertificateChecks.KernelMisc.Co2K.HC1L CFSG.RankThree.Native.co2FiveC1LHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HC1L CFSG.RankThree.Native.co2FiveC1LHex 3 600 12 1
#ks_chars CertificateChecks.KernelMisc.Co2K.HDP CFSG.RankThree.Native.co2FiveDMHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HDP CFSG.RankThree.Native.co2FiveDMHex 121 1 484 60
#ks_chars CertificateChecks.KernelMisc.Co2K.HDE CFSG.RankThree.Native.co2FiveDEHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HDE CFSG.RankThree.Native.co2FiveDEHex 3 2 12 60
#ks_chars CertificateChecks.KernelMisc.Co2K.HDR CFSG.RankThree.Native.co2FiveDRHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HDR CFSG.RankThree.Native.co2FiveDRHex 3 60 12 1
#ks_chars CertificateChecks.KernelMisc.Co2K.HDL CFSG.RankThree.Native.co2FiveDLHex
#kmisc_hexflat CertificateChecks.KernelMisc.Co2K.HDL CFSG.RankThree.Native.co2FiveDLHex 3 60 12 1
#kmisc_packarrs CertificateChecks.KernelMisc.Co2K.SS CFSG.Sporadic.Co2Cert.co2StrongArrs 12
#kmisc_packarrs CertificateChecks.KernelMisc.Co2K.MSt CertificateChecks.KernelMisc.Co2K.MStArr 484
#kmisc_packarrs CertificateChecks.KernelMisc.Co2K.AMt CertificateChecks.KernelMisc.Co2K.AMtArr 484
#kmisc_packarrs CertificateChecks.KernelMisc.Co2K.TMt CertificateChecks.KernelMisc.Co2K.TMtArr 484
#kmisc_packarrs CertificateChecks.KernelMisc.Co2K.LVt CertificateChecks.KernelMisc.Co2K.LVtArr 12
#kmisc_packarrs CertificateChecks.KernelMisc.Co2K.SVt CertificateChecks.KernelMisc.Co2K.SVtArr 22
#kmisc_packarrs CertificateChecks.KernelMisc.Co2K.SPt CertificateChecks.KernelMisc.Co2K.SPtArr 12
#kmisc_packarrs CertificateChecks.KernelMisc.Co2K.CSt CertificateChecks.KernelMisc.Co2K.CStArr 12
#kmisc_packarrs CertificateChecks.KernelMisc.Co2K.DIt CertificateChecks.KernelMisc.Co2K.DItArr 484
#kmisc_packarrs CertificateChecks.KernelMisc.Co2K.SEt CertificateChecks.KernelMisc.Co2K.SEtArr 484
#kmisc_packarrs CertificateChecks.KernelMisc.Co2K.SEPt CertificateChecks.KernelMisc.Co2K.SEPtArr 12
#kmisc_packarrs CertificateChecks.KernelMisc.Co2K.WTt CertificateChecks.KernelMisc.Co2K.WTtArr 12

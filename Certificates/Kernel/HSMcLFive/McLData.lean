module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.B3S3.Gen
public import CFSG.RankThree.Native.HSMcLFiveCheckInputs
public meta import CFSG.RankThree.Native.HSMcLFiveCheckInputs
public meta import Certificates.Kernel.B3S3.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelHSMcLFive

@[expose] def e0 : List (List Int) := CFSG.RankThree.Native.mcl275Case0Words.toList.drop 3

@[expose] def e1 : List (List Int) := CFSG.RankThree.Native.mcl275Case1Words.toList.drop 3

end CertificateChecks.KernelHSMcLFive

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelHSMcLFive.MF CFSG.RankThree.Native.mcl275FiveHex
#kmisc_hexflat CertificateChecks.KernelHSMcLFive.MF CFSG.RankThree.Native.mcl275FiveHex 3 275 9 76
#ks_chars CertificateChecks.KernelHSMcLFive.M0X CFSG.RankThree.Native.mcl275Case0Hex
#kmisc_hexflat CertificateChecks.KernelHSMcLFive.M0X CFSG.RankThree.Native.mcl275Case0Hex 3 275 9
  14
#ks_chars CertificateChecks.KernelHSMcLFive.M1X CFSG.RankThree.Native.mcl275Case1Hex
#kmisc_hexflat CertificateChecks.KernelHSMcLFive.M1X CFSG.RankThree.Native.mcl275Case1Hex 3 275 9
  16

#ks_rawchain CertificateChecks.KernelHSMcLFive.M0 275 9 55 CFSG.RankThree.Native.mcl275Case0Arrs
  CFSG.RankThree.Native.mcl275Case0BaseArr 3 CertificateChecks.KernelHSMcLFive.e0
#ks_rawchain CertificateChecks.KernelHSMcLFive.M1 275 9 55 CFSG.RankThree.Native.mcl275Case1Arrs
  CFSG.RankThree.Native.mcl275Case1BaseArr 3 CertificateChecks.KernelHSMcLFive.e1

#kb3_enum CertificateChecks.KernelHSMcLFive.NQ CFSG.RankThree.Native.mcl275FiveQGens
  CFSG.RankThree.Native.mcl275RBaseArr 275 9
#kb3_enum CertificateChecks.KernelHSMcLFive.NC0 CFSG.RankThree.Native.mcl275FiveC0Gens
  CFSG.RankThree.Native.mcl275RBaseArr 275 9
#kb3_enum CertificateChecks.KernelHSMcLFive.NC1 CFSG.RankThree.Native.mcl275FiveC1Gens
  CFSG.RankThree.Native.mcl275RBaseArr 275 9
#kb3_enum CertificateChecks.KernelHSMcLFive.NA0 CFSG.RankThree.Native.mcl275FiveA0Gens
  CFSG.RankThree.Native.mcl275RBaseArr 275 9
#kb3_enum CertificateChecks.KernelHSMcLFive.NA1 CFSG.RankThree.Native.mcl275FiveA1Gens
  CFSG.RankThree.Native.mcl275RBaseArr 275 9

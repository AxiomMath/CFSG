module

public import Certificates.Kernel.Sporadic.RawGenSchOJ
public meta import Certificates.Kernel.Sporadic.RawGenSchOJ
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.B3S3.Gen
public import CFSG.RankThree.Native.HSMcLFiveCheckInputs
public meta import CFSG.RankThree.Native.HSMcLFiveCheckInputs
public meta import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.B3S3.GenL
public meta import Certificates.Kernel.B3S3.GenL
public import Certificates.Kernel.B3S3.GenSl
public meta import Certificates.Kernel.B3S3.GenSl
public import CFSG.Certificates.Kernel.BfsPinSliceSound
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

#ks_rawchain_sl2_data CertificateChecks.KernelHSMcLFive.M0 275 9 28 55
  CFSG.RankThree.Native.mcl275Case0Arrs CFSG.RankThree.Native.mcl275Case0BaseArr 3
  CertificateChecks.KernelHSMcLFive.e0

#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M0 0 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M0 1 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M0 2 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M0 3 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M0 4 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M0 5 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M0 6 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M0 7 0 5

#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M0 1 0 4
#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M0 2 0 3
#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M0 3 0 2
#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M0 4 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M0 5 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M0 6 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M0 7 0 1

#ks_rawchain_sl2_osub CertificateChecks.KernelHSMcLFive.M0
#ks_rawchain_sl2_scho CertificateChecks.KernelHSMcLFive.M0 0 10

#ks_rawchain_sl2_joino CertificateChecks.KernelHSMcLFive.M0

#ks_rawchain_sl2_data CertificateChecks.KernelHSMcLFive.M1 275 9 28 55
  CFSG.RankThree.Native.mcl275Case1Arrs CFSG.RankThree.Native.mcl275Case1BaseArr 3
  CertificateChecks.KernelHSMcLFive.e1

#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M1 0 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M1 1 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M1 2 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M1 3 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M1 4 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M1 5 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M1 6 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelHSMcLFive.M1 7 0 5

#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M1 1 0 4
#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M1 2 0 2
#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M1 3 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M1 4 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M1 5 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M1 6 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelHSMcLFive.M1 7 0 1

#ks_rawchain_sl2_osub CertificateChecks.KernelHSMcLFive.M1
#ks_rawchain_sl2_scho CertificateChecks.KernelHSMcLFive.M1 0 10

#ks_rawchain_sl2_joino CertificateChecks.KernelHSMcLFive.M1

#kb3_enum_l CertificateChecks.KernelHSMcLFive.NQ CFSG.RankThree.Native.mcl275FiveQGens
  CFSG.RankThree.Native.mcl275RBaseArr 275 9
#kb3_enum_l CertificateChecks.KernelHSMcLFive.NC0 CFSG.RankThree.Native.mcl275FiveC0Gens
  CFSG.RankThree.Native.mcl275RBaseArr 275 9
#kb3_enum_sl CertificateChecks.KernelHSMcLFive.NC1 CFSG.RankThree.Native.mcl275FiveC1Gens
  CFSG.RankThree.Native.mcl275RBaseArr 275 9 100

namespace CertificateChecks.KernelHSMcLFive

theorem NC1.ok : CFSG.KC.BfsPin.bfsK 275 9 NC1.ng NC1.G NC1.N NC1.T NC1.E NC1.S = true :=
  CFSG.KC.BfsPin.bfsK_of_slices (L := 100) (K := 15) rfl (by decide) rfl NC1.g NC1.csAll NC1.t0
    NC1.dist (Nat.eq_of_beq_eq_true NC1.c0) (Nat.eq_of_beq_eq_true NC1.cK) NC1.rsAll

end CertificateChecks.KernelHSMcLFive
#kb3_enum_l CertificateChecks.KernelHSMcLFive.NA0 CFSG.RankThree.Native.mcl275FiveA0Gens
  CFSG.RankThree.Native.mcl275RBaseArr 275 9
#kb3_enum_l CertificateChecks.KernelHSMcLFive.NA1 CFSG.RankThree.Native.mcl275FiveA1Gens
  CFSG.RankThree.Native.mcl275RBaseArr 275 9

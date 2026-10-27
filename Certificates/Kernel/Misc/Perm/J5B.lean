module

public import Certificates.Kernel.Misc.Perm.CertBind
public import Certificates.Kernel.Misc.Perm.J5Data
public import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.Misc.Perm.J5Data
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.RankThree.PartOne.KS.OrbitCert
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.Sporadic.Schreier.PairJ2Check
meta import CFSG.RankThree.PartOne.KS.OrbitCert
meta import CFSG.RankThree.PartOne.KS.PKitLines
meta import CFSG.Sporadic.Schreier.PairJ2Check

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.J2F.JS CFSG.Sporadic.Schreier.PairNative.j2StrongHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.JS
  CFSG.Sporadic.Schreier.PairNative.j2StrongHex 4 315 9 7
#ks_chars CertificateChecks.KernelMisc.J2F.JU CFSG.Sporadic.SmallOddCore.j2CentHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.JU CFSG.Sporadic.SmallOddCore.j2CentHex
  3 315 9 1
#kmisc_packarrs CertificateChecks.KernelMisc.J2F.LX CFSG.RankThree.PartOne.j2FiveLineArrs 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2F.QG CFSG.RankThree.PartOne.j2FiveQGenArrs 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2F.CGP0 CertificateChecks.KernelMisc.J2F.CG0 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2F.CGP1 CertificateChecks.KernelMisc.J2F.CG1 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2F.CGP2 CertificateChecks.KernelMisc.J2F.CG2 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2F.CGP3 CertificateChecks.KernelMisc.J2F.CG3 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2F.CGP4 CertificateChecks.KernelMisc.J2F.CG4 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2F.CGP5 CertificateChecks.KernelMisc.J2F.CG5 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2F.DGP2 CertificateChecks.KernelMisc.J2F.DG2 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2F.DGP3 CertificateChecks.KernelMisc.J2F.DG3 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2F.DGP5 CertificateChecks.KernelMisc.J2F.DG5 9
#ks_chars CertificateChecks.KernelMisc.J2F.QP
  CFSG.RankThree.PartOne.j2FiveQLitPHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.QP
  CFSG.RankThree.PartOne.j2FiveQLitPHex 3 315 9 25
#ks_chars CertificateChecks.KernelMisc.J2F.QE
  CFSG.RankThree.PartOne.j2FiveQLitEHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.QE
  CFSG.RankThree.PartOne.j2FiveQLitEHex 3 2 12 25
#ks_chars CertificateChecks.KernelMisc.J2F.QR
  CFSG.RankThree.PartOne.j2FiveQLitRHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.QR
  CFSG.RankThree.PartOne.j2FiveQLitRHex 3 25 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.QL
  CFSG.RankThree.PartOne.j2FiveQLitLHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.QL
  CFSG.RankThree.PartOne.j2FiveQLitLHex 3 25 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.C0P
  CFSG.RankThree.PartOne.j2FiveCLit0PHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C0P
  CFSG.RankThree.PartOne.j2FiveCLit0PHex 3 315 9 50
#ks_chars CertificateChecks.KernelMisc.J2F.C0E
  CFSG.RankThree.PartOne.j2FiveCLit0EHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C0E
  CFSG.RankThree.PartOne.j2FiveCLit0EHex 3 2 12 50
#ks_chars CertificateChecks.KernelMisc.J2F.C0R
  CFSG.RankThree.PartOne.j2FiveCLit0RHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C0R
  CFSG.RankThree.PartOne.j2FiveCLit0RHex 3 50 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.C0L
  CFSG.RankThree.PartOne.j2FiveCLit0LHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C0L
  CFSG.RankThree.PartOne.j2FiveCLit0LHex 3 50 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.C1P
  CFSG.RankThree.PartOne.j2FiveCLit1PHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C1P
  CFSG.RankThree.PartOne.j2FiveCLit1PHex 3 315 9 50
#ks_chars CertificateChecks.KernelMisc.J2F.C1E
  CFSG.RankThree.PartOne.j2FiveCLit1EHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C1E
  CFSG.RankThree.PartOne.j2FiveCLit1EHex 3 2 12 50
#ks_chars CertificateChecks.KernelMisc.J2F.C1R
  CFSG.RankThree.PartOne.j2FiveCLit1RHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C1R
  CFSG.RankThree.PartOne.j2FiveCLit1RHex 3 50 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.C1L
  CFSG.RankThree.PartOne.j2FiveCLit1LHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C1L
  CFSG.RankThree.PartOne.j2FiveCLit1LHex 3 50 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.C2P
  CFSG.RankThree.PartOne.j2FiveCLit2PHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C2P
  CFSG.RankThree.PartOne.j2FiveCLit2PHex 3 315 9 300
#ks_chars CertificateChecks.KernelMisc.J2F.C2E
  CFSG.RankThree.PartOne.j2FiveCLit2EHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C2E
  CFSG.RankThree.PartOne.j2FiveCLit2EHex 3 3 12 300
#ks_chars CertificateChecks.KernelMisc.J2F.C2R
  CFSG.RankThree.PartOne.j2FiveCLit2RHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C2R
  CFSG.RankThree.PartOne.j2FiveCLit2RHex 3 300 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.C2L
  CFSG.RankThree.PartOne.j2FiveCLit2LHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C2L
  CFSG.RankThree.PartOne.j2FiveCLit2LHex 3 300 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.C3P
  CFSG.RankThree.PartOne.j2FiveCLit3PHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C3P
  CFSG.RankThree.PartOne.j2FiveCLit3PHex 3 315 9 300
#ks_chars CertificateChecks.KernelMisc.J2F.C3E
  CFSG.RankThree.PartOne.j2FiveCLit3EHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C3E
  CFSG.RankThree.PartOne.j2FiveCLit3EHex 3 2 12 300
#ks_chars CertificateChecks.KernelMisc.J2F.C3R
  CFSG.RankThree.PartOne.j2FiveCLit3RHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C3R
  CFSG.RankThree.PartOne.j2FiveCLit3RHex 3 300 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.C3L
  CFSG.RankThree.PartOne.j2FiveCLit3LHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C3L
  CFSG.RankThree.PartOne.j2FiveCLit3LHex 3 300 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.C4P
  CFSG.RankThree.PartOne.j2FiveCLit4PHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C4P
  CFSG.RankThree.PartOne.j2FiveCLit4PHex 3 315 9 50
#ks_chars CertificateChecks.KernelMisc.J2F.C4E
  CFSG.RankThree.PartOne.j2FiveCLit4EHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C4E
  CFSG.RankThree.PartOne.j2FiveCLit4EHex 3 3 12 50
#ks_chars CertificateChecks.KernelMisc.J2F.C4R
  CFSG.RankThree.PartOne.j2FiveCLit4RHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C4R
  CFSG.RankThree.PartOne.j2FiveCLit4RHex 3 50 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.C4L
  CFSG.RankThree.PartOne.j2FiveCLit4LHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C4L
  CFSG.RankThree.PartOne.j2FiveCLit4LHex 3 50 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.C5P
  CFSG.RankThree.PartOne.j2FiveCLit5PHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C5P
  CFSG.RankThree.PartOne.j2FiveCLit5PHex 3 315 9 300
#ks_chars CertificateChecks.KernelMisc.J2F.C5E
  CFSG.RankThree.PartOne.j2FiveCLit5EHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C5E
  CFSG.RankThree.PartOne.j2FiveCLit5EHex 3 3 12 300
#ks_chars CertificateChecks.KernelMisc.J2F.C5R
  CFSG.RankThree.PartOne.j2FiveCLit5RHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C5R
  CFSG.RankThree.PartOne.j2FiveCLit5RHex 3 300 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.C5L
  CFSG.RankThree.PartOne.j2FiveCLit5LHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.C5L
  CFSG.RankThree.PartOne.j2FiveCLit5LHex 3 300 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.D2P
  CFSG.RankThree.PartOne.j2FiveDLit2PHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.D2P
  CFSG.RankThree.PartOne.j2FiveDLit2PHex 3 315 9 60
#ks_chars CertificateChecks.KernelMisc.J2F.D2E
  CFSG.RankThree.PartOne.j2FiveDLit2EHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.D2E
  CFSG.RankThree.PartOne.j2FiveDLit2EHex 3 3 12 60
#ks_chars CertificateChecks.KernelMisc.J2F.D2R
  CFSG.RankThree.PartOne.j2FiveDLit2RHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.D2R
  CFSG.RankThree.PartOne.j2FiveDLit2RHex 3 60 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.D2L
  CFSG.RankThree.PartOne.j2FiveDLit2LHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.D2L
  CFSG.RankThree.PartOne.j2FiveDLit2LHex 3 60 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.D3P
  CFSG.RankThree.PartOne.j2FiveDLit3PHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.D3P
  CFSG.RankThree.PartOne.j2FiveDLit3PHex 3 315 9 60
#ks_chars CertificateChecks.KernelMisc.J2F.D3E
  CFSG.RankThree.PartOne.j2FiveDLit3EHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.D3E
  CFSG.RankThree.PartOne.j2FiveDLit3EHex 3 2 12 60
#ks_chars CertificateChecks.KernelMisc.J2F.D3R
  CFSG.RankThree.PartOne.j2FiveDLit3RHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.D3R
  CFSG.RankThree.PartOne.j2FiveDLit3RHex 3 60 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.D3L
  CFSG.RankThree.PartOne.j2FiveDLit3LHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.D3L
  CFSG.RankThree.PartOne.j2FiveDLit3LHex 3 60 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.D5P
  CFSG.RankThree.PartOne.j2FiveDLit5PHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.D5P
  CFSG.RankThree.PartOne.j2FiveDLit5PHex 3 315 9 60
#ks_chars CertificateChecks.KernelMisc.J2F.D5E
  CFSG.RankThree.PartOne.j2FiveDLit5EHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.D5E
  CFSG.RankThree.PartOne.j2FiveDLit5EHex 3 2 12 60
#ks_chars CertificateChecks.KernelMisc.J2F.D5R
  CFSG.RankThree.PartOne.j2FiveDLit5RHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.D5R
  CFSG.RankThree.PartOne.j2FiveDLit5RHex 3 60 12 1
#ks_chars CertificateChecks.KernelMisc.J2F.D5L
  CFSG.RankThree.PartOne.j2FiveDLit5LHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2F.D5L
  CFSG.RankThree.PartOne.j2FiveDLit5LHex 3 60 12 1

module

public import Certificates.Data.Kernel.ONanMirrorK
public import Certificates.Kernel.ONanMirror.Data

public section

namespace CertificateChecks.ONanMirror

open CFSG.OddStandard.ONanRec.CM CFSG.OddStandard.ONanRec.B2K CFSG.OddStandard.ONanRec.MirK
open CFSG.KD.ONanMirror

theorem ck6150_small : mSmallK = true := by decide +kernel

theorem ck6150_orb : orbK [yW, zW] ptsM 2520 orb = true := by decide +kernel

theorem ck6150_cent : mCentK cw = true := by decide +kernel

theorem ck6150_t0 : mT0K t0 = true := by decide +kernel

theorem ck6150_ff : eqB (fW ++ fW) [] = true := by decide +kernel

theorem ck6150_chain0 : mChainK (yW ++ wpow fW 0) 0 t0 cw hint0 = true := by decide +kernel

theorem ck6150_chain1 : mChainK (yW ++ wpow fW 1) 1 t0 cw hint1 = true := by decide +kernel

end CertificateChecks.ONanMirror

module

public import Certificates.Kernel.Fin76bOm.UData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDef

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelC24608

open CFSG.KC.Fin76bU CFSG.EvenSporadicStandard.Fin76b.W16

set_option maxHeartbeats 0 in
theorem j2U_chk : uChkU J2U.P 21 J2U.WS = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem j2U_tbl : ((List.range 32).all fun a => (List.range 32).all fun b =>
    mU J2U.P a b == mulE0 a b) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem j3U_chk : uChkU J3U.P 21 J3U.WS = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem j3U_tbl : ((List.range 32).all fun a => (List.range 32).all fun b =>
    mU J3U.P a b == mulEJ3 a b) = true := by decide +kernel

end CertificateChecks.KernelC24608

end

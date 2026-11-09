module

public import Certificates.Data.Kernel.M24L2.FC
public import Certificates.Data.Kernel.M24L2.FCLit
public import Certificates.Data.Kernel.M24L2.FCRec
public import Certificates.Kernel.M24L2.DataB

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fc_ok : fcTreeR dL fcLitK thCodesK fcRecK 3 [] = true := by decide +kernel

theorem dTwin_length : dTwin.all.length ≤ 2048 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fcLit_ok : (fcAllK3.map fcTupK == fcLitK.map fcTupK) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fcPos_ok : fcPosOk (treeFc dQ) = true := by decide +kernel

end CertificateChecks.KernelM24L2

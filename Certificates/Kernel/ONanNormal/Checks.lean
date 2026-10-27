module

public import Certificates.Data.Kernel.ONanNormalK
public import Certificates.Kernel.ONanNormal.Data
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.ONanNormal

open CFSG.OddStandard.ONanRec.B2K CFSG.OddStandard.ONanRec.NK CFSG.KD.ONanNormal

theorem ck6146_shape : shapeK gs ws rs wt = true := by decide +kernel

noncomputable def ch6146c (k : Nat) : Bool := chunkK gs ws ks rs wt k

#kc_each ch6146c 0 16

#kc_forall_chunks ck6146_chunks (fun k => chunkK gs ws ks rs wt k = true) 16
  CertificateChecks.ONanNormal.ch6146c 1

theorem ck6146_neg_wit :
    (!chunkK gs ws ks rs (wt.set 0 ((wt.getD 0 []).map fun t => t.set 2 0)) 0) = true := by
  decide +kernel

theorem ck6146_neg_cl :
    (!chunkK gs ws ks (rs.set 0 ((rs.getD 0 []).map fun r => r.set 0 ((r.getD 0 0 + 1) % 512)))
      wt 0) = true := by
  decide +kernel

theorem ck6146_neg_depth :
    (!chunkK gs ws ks (rs.set 0 ((rs.getD 0 []).map fun r => r.set 3 7)) wt 0) = true := by
  decide +kernel

theorem ck6146_neg_key : (!chunkK gs ws (ks.set 0 (ks.getD 0 []).reverse) rs wt 0) = true := by
  decide +kernel

theorem ck6146_neg_empty : (!shapeK gs ws rs (wt.set 1 ((wt.getD 1 []).map fun _ => []))) = true := by
  decide +kernel

end CertificateChecks.ONanNormal

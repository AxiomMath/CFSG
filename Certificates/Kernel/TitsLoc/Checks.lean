module

public import Certificates.Kernel.TitsLoc.Data
public import Certificates.Kernel.TwoF4Lie.Checks
public import Certificates.Data.Kernel.TitsLocK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsLoc

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsLocK CFSG.KD.TwoF4Lie CFSG.KD.TitsLoc
  CertificateChecks.KernelTwoF4Lie CertificateChecks.KernelMisc
  CertificateChecks.KernelSporSch.TitsAction CertificateChecks.KernelSporSch

@[expose] noncomputable def nodesD : List Nat :=
  nodeOf r0 :: nodeOf r1 :: fD.map nodeOf

theorem ch4182_tD : wordD tW = true := by quickRfl

theorem ch4182_q : qK F TGI lpK TitsZ (TTC 0) (TTC 1) qW = true := by quickRfl

theorem ch4182_for0 : forK F TGI TA TB lpK base (fD.take 71) [nodeOf r1, nodeOf r0] = true := by
  quickRfl

theorem ch4182_for1 : forK F TGI TA TB lpK base (fD.drop 71)
    (((fD.take 71).map nodeOf).reverse ++ [nodeOf r1, nodeOf r0]) = true := by quickRfl

theorem ch4182_forD : List.all fD (fun r => wordD (r.drop 4)) = true := by quickRfl

theorem ch4182_nodes : List.all nodes (fun k => memK k nodesD) = true := by quickRfl

theorem ch4182_loc0 : locK F TGI TA TB lpK base TitsZ r0 r1 (uR.take 12) pC eR 0 = true := by
  quickRfl

theorem ch4182_loc1 : locK F TGI TA TB lpK base TitsZ r0 r1 (uR.drop 12) pC eR 12 = true := by
  quickRfl

theorem ch4182_fix : fixK (TTC 0) (TTC 1) uR = true := by quickRfl

end CertificateChecks.KernelTitsLoc

end

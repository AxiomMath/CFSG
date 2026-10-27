module

public import Certificates.Kernel.NT44.Pack
public import Certificates.Kernel.NT44.Pack2
public import Certificates.Data.Kernel.Misc.ConjTab
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Certificates.SchreierChainData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CertificateChecks.KernelNT44

open CFSG.GH74.GLS.NT44.PermutationNative CFSG.KC.Misc.ConjTab
open CFSG.KC.Enum (permOK pidn)
open CFSG.KS (mask)
open CFSG.KS.Prim (wordEqK)
open CFSG.KC.LQT.P (allN)

theorem nt44_fwd : allN 2 (fun i => wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44KS nt44KSI 2
    (fwd ())[i]! (nt44V i)) = true := by quickRfl

theorem nt44_inv_v : allN 2 (fun i => permOK 2688 12 (mask 12) (2688 * 12) (nt44V i)
    (nt44VI i)) = true := by quickRfl

theorem nt44_cover : (CFSG.LieType.Multipliers.L34.coverWs.map
    (List.map CFSG.Certificates.schreierLetterCode)).all (fun r =>
      wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44V nt44VI 2 r (pidn 2688 12)) = true := by
  quickRfl

theorem nt44_z : wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44V nt44VI 2
    (CFSG.LieType.Multipliers.L34.zThree.map CFSG.Certificates.schreierLetterCode)
    (pidn 2688 12) = true := by
  quickRfl

theorem nt44_rev : allN 2 (fun i => wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44V nt44VI 2
    (rev ())[i]! (nt44KS i)) = true := by quickRfl

theorem nt44_pw : allN 9 (fun i => wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44KS nt44KSI 2
    (pw ())[i]! (nt44P0 i)) = true := by quickRfl

theorem nt44_norm : allN 4 (fun k => allN 2 fun j =>
    wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44KS nt44KSI 2 (nw ())[k]!.left[j]!
      (cj3 2688 12 (nt44L (k + 1)) (nt44KS j) (nt44LI (k + 1))) &&
    wordEqK 2688 12 (mask 12) (pidn 2688 12) nt44KS nt44KSI 2 (nw ())[k]!.inverse[j]!
      (cj3 2688 12 (nt44LI (k + 1)) (nt44KS j) (nt44L (k + 1)))) = true := by quickRfl

end CertificateChecks.KernelNT44

end

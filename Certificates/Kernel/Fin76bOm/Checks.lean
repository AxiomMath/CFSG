module

public import Certificates.Kernel.Fin76bOm.Data
public import Certificates.Kernel.Fin76bOm.J2
public import Certificates.Kernel.Fin76bOm.J3
public import Certificates.Data.Kernel.Fin76bOm.Twin
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDef
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelC24608

open CFSG.KC.YoshQ CFSG.KC.Fin76bOm CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.EvenSporadicStandard.Fin76b.W16

@[expose] noncomputable def j2Og : Array Table := (((List.range 4).map J2OmT).map (tabN 32 6)).toArray

@[expose] noncomputable def j3Og : Array Table := (((List.range 5).map J3OmT).map (tabN 80 7)).toArray

set_option maxHeartbeats 0 in
theorem j2Om_perm : CFSG.Sporadic.SmallOddCore.permOK 32 (tabN 32 6 (J2OmT 4)) = true ∧
    j2Og.all (fun x => CFSG.Sporadic.SmallOddCore.permOK 32 x) = true ∧
    ((J2E.GS.map (tabN 32 6)).toArray).all (fun x => CFSG.Sporadic.SmallOddCore.permOK 32 x) =
      true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem j2Om_facts : J2W.cnt = 1920 ∧ J2E.cnt = 32 ∧ J2E.GS.length = 20 ∧
    centEN 32 6 (J2OmT 4) J2E.GS J2W.RL = true ∧ J2W.BK < J2W.RL.length ∧
    betaN 32 6 J2E.RL (J2W.RL.getD J2W.BK 0) = true ∧ closedN 32 6 J2E.RL = true ∧
    J2E.RL.findIdx (fun x => eqN 32 6 x (J2OmT 4)) = 21 ∧
    eqN 32 6 (J2E.RL.getD 21 0) (J2OmT 4) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem j2Om_ord : ordTest 32 3 (tabN 32 6 (J2W.RL.getD J2W.BK 0)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem j2Om_tbl : ((List.range 32).all fun a => (List.range 32).all fun b =>
    mulIdxN 32 6 J2E.RL a b == mulE0 a b) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem j3Om_perm : CFSG.Sporadic.SmallOddCore.permOK 80 (tabN 80 7 (J3OmT 5)) = true ∧
    j3Og.all (fun x => CFSG.Sporadic.SmallOddCore.permOK 80 x) = true ∧
    ((J3E.GS.map (tabN 80 7)).toArray).all (fun x => CFSG.Sporadic.SmallOddCore.permOK 80 x) =
      true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem j3Om_facts : J3W.cnt = 1920 ∧ J3E.cnt = 32 ∧ J3E.GS.length = 20 ∧
    centEN 80 7 (J3OmT 5) J3E.GS J3W.RL = true ∧ J3W.BK < J3W.RL.length ∧
    betaN 80 7 J3E.RL (J3W.RL.getD J3W.BK 0) = true ∧ closedN 80 7 J3E.RL = true ∧
    J3E.RL.findIdx (fun x => eqN 80 7 x (J3OmT 5)) = 21 ∧
    eqN 80 7 (J3E.RL.getD 21 0) (J3OmT 5) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem j3Om_ord : ordTest 80 3 (tabN 80 7 (J3W.RL.getD J3W.BK 0)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem j3Om_tbl : ((List.range 32).all fun a => (List.range 32).all fun b =>
    mulIdxN 80 7 J3E.RL a b == mulEJ3 a b) = true := by
  decide +kernel

end CertificateChecks.KernelC24608

end

module

public import Certificates.Data.Kernel.CosetW.EnumW
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5Check
public import Certificates.Data.Kernel.CosetW.SegChain
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelYoshQ

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration CFSG.EvenSporadicStandard.M12Std.Yosh

set_option maxHeartbeats 0

@[expose] def six : List ℕ := [0, 1, 2, 3, 4, 5]

theorem b4 : checkW (mkParamsW (2 * 8) (invArrW 8) (codes (rel4 0 0))
      (codes ((subsetOf 8 six).map fun x => [(x, true)]))) 20000 4 = true ∧
    checkW (mkParamsW (2 * 8) (invArrW 8) (codes (rel4 0 1))
      (codes ((subsetOf 8 six).map fun x => [(x, true)]))) 20000 4 = true ∧
    checkW (mkParamsW (2 * 8) (invArrW 8) (codes (rel4 1 0))
      (codes ((subsetOf 8 six).map fun x => [(x, true)]))) 20000 4 = true ∧
    checkW (mkParamsW (2 * 8) (invArrW 8) (codes (rel4 1 1))
      (codes ((subsetOf 8 six).map fun x => [(x, true)]))) 20000 4 = true := by
  decide +kernel

abbrev P4r : Params :=
  mkParamsW (2 * (subsetOf 8 six).length) (invArrW (subsetOf 8 six).length)
    (codes (restrictWords (subsetOf 8 six) (rel4 0 0)))
    (codes ((subsetOf (subsetOf 8 six).length []).map fun x => [(x, true)]))

theorem b4r_hs : P4r.subs = [] := rfl

#kc_natval B4RT1 := (felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 1 (StW.init P4r.L 20000)).tab.t
#kc_natval B4RF1 := (felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 1 (StW.init P4r.L 20000)).fwd.t
#kc_natval B4RQ1 := (felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 1 (StW.init P4r.L 20000)).par.t
#kc_natval B4RN1 := (felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 1 (StW.init P4r.L 20000)).next

@[expose] noncomputable def b4rS1 : StW :=
  ⟨⟨(20000 + 1) * P4r.L, B4RT1⟩, ⟨20000 + 1, B4RF1⟩, ⟨20000 + 1, B4RQ1⟩, B4RN1, #[], #[], 0,
    false⟩

set_option maxHeartbeats 0 in
theorem b4r_h1 : felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 1 (StW.init P4r.L 20000) = b4rS1 :=
  StW.eq_of_eqB (by quickRfl)

#kc_natval B4RT2 := (felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 (1 + 96) b4rS1).tab.t
#kc_natval B4RF2 := (felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 (1 + 96) b4rS1).fwd.t
#kc_natval B4RQ2 := (felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 (1 + 96) b4rS1).par.t
#kc_natval B4RN2 := (felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 (1 + 96) b4rS1).next

@[expose] noncomputable def b4rS2 : StW :=
  ⟨⟨(20000 + 1) * P4r.L, B4RT2⟩, ⟨20000 + 1, B4RF2⟩, ⟨20000 + 1, B4RQ2⟩, B4RN2, #[], #[], 0,
    false⟩

set_option maxHeartbeats 0 in
theorem b4r_h2 : felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 (1 + 96) b4rS1 = b4rS2 :=
  StW.eq_of_eqB (by quickRfl)

#kc_natval B4RT3 := (felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 (1 + 96 + 96) b4rS2).tab.t
#kc_natval B4RF3 := (felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 (1 + 96 + 96) b4rS2).fwd.t
#kc_natval B4RQ3 := (felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 (1 + 96 + 96) b4rS2).par.t
#kc_natval B4RN3 := (felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 (1 + 96 + 96) b4rS2).next

@[expose] noncomputable def b4rS3 : StW :=
  ⟨⟨(20000 + 1) * P4r.L, B4RT3⟩, ⟨20000 + 1, B4RF3⟩, ⟨20000 + 1, B4RQ3⟩, B4RN3, #[], #[], 0,
    false⟩

set_option maxHeartbeats 0 in
theorem b4r_h3 : felschW P4r (64 * (20000 + 1) * (P4r.L + 1)) 96 (1 + 96 + 96) b4rS2 = b4rS3 :=
  StW.eq_of_eqB (by quickRfl)

set_option maxHeartbeats 0 in
theorem b4r_hc : checkFromW P4r (64 * (20000 + 1) * (P4r.L + 1)) 19713 (1 + 96 + 96 + 96) b4rS3 384 = true := by quickRfl

theorem b4r : checkW (mkParamsW (2 * (subsetOf 8 six).length) (invArrW (subsetOf 8 six).length)
      (codes (restrictWords (subsetOf 8 six) (rel4 0 0)))
      (codes ((subsetOf (subsetOf 8 six).length []).map fun x => [(x, true)]))) 20000 384 = true := by
  exact checkW_of_seg4 (P := P4r) (a₁ := 96) (a₂ := 96) (a₃ := 96) (r := 19713)
    b4r_hs rfl b4r_h1 b4r_h2 b4r_h3 b4r_hc

theorem b4eq : restrictWords (subsetOf 8 six) (rel4 0 1) = restrictWords (subsetOf 8 six) (rel4 0 0) ∧
    restrictWords (subsetOf 8 six) (rel4 1 0) = restrictWords (subsetOf 8 six) (rel4 0 0) ∧
    restrictWords (subsetOf 8 six) (rel4 1 1) = restrictWords (subsetOf 8 six) (rel4 0 0) := by
  decide +kernel

theorem bE : checkW (mkParamsW (2 * 6) (invArrW 6) (codes relE)
    (codes ((subsetOf 6 []).map fun x => [(x, true)]))) 20000 128 = true := by
  decide +kernel

theorem bN0 : checkW (mkParamsW (2 * 9) (invArrW 9) (codes (relN 0 0 0))
    (codes ((subsetOf 9 six).map fun x => [(x, true)]))) 20000 24 = true := by
  decide +kernel

theorem bN1 : checkW (mkParamsW (2 * 9) (invArrW 9) (codes (relN 0 0 1))
    (codes ((subsetOf 9 six).map fun x => [(x, true)]))) 20000 24 = true := by
  decide +kernel

theorem bN2 : checkW (mkParamsW (2 * 9) (invArrW 9) (codes (relN 1 1 0))
    (codes ((subsetOf 9 six).map fun x => [(x, true)]))) 20000 24 = true := by
  decide +kernel

theorem bN3 : checkW (mkParamsW (2 * 9) (invArrW 9) (codes (relN 1 1 1))
    (codes ((subsetOf 9 six).map fun x => [(x, true)]))) 20000 24 = true := by
  decide +kernel

theorem bN : checkW (mkParamsW (2 * 9) (invArrW 9) (codes (relN 0 0 0))
      (codes ((subsetOf 9 six).map fun x => [(x, true)]))) 20000 24 = true ∧
    checkW (mkParamsW (2 * 9) (invArrW 9) (codes (relN 0 0 1))
      (codes ((subsetOf 9 six).map fun x => [(x, true)]))) 20000 24 = true ∧
    checkW (mkParamsW (2 * 9) (invArrW 9) (codes (relN 1 1 0))
      (codes ((subsetOf 9 six).map fun x => [(x, true)]))) 20000 24 = true ∧
    checkW (mkParamsW (2 * 9) (invArrW 9) (codes (relN 1 1 1))
      (codes ((subsetOf 9 six).map fun x => [(x, true)]))) 20000 24 = true :=
  ⟨bN0, bN1, bN2, bN3⟩

theorem bNr : checkW (mkParamsW (2 * (subsetOf 9 six).length) (invArrW (subsetOf 9 six).length)
      (codes (restrictWords (subsetOf 9 six) (relN 0 0 0)))
      (codes ((subsetOf (subsetOf 9 six).length []).map fun x => [(x, true)]))) 20000 128 =
      true := by
  decide +kernel

theorem bNeq :
    restrictWords (subsetOf 9 six) (relN 0 0 1) = restrictWords (subsetOf 9 six) (relN 0 0 0) ∧
    restrictWords (subsetOf 9 six) (relN 1 1 0) = restrictWords (subsetOf 9 six) (relN 0 0 0) ∧
    restrictWords (subsetOf 9 six) (relN 1 1 1) = restrictWords (subsetOf 9 six) (relN 0 0 0) := by
  decide +kernel

end CertificateChecks.KernelYoshQ

end

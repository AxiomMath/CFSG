module

public import CFSG.Quasithin.Recognition.RuRank3RuParamDataInputs
public import Certificates.Kernel.SporSch.Ru.Cnt7048K
public import Certificates.Kernel.SporSch.Ru.Glue7046

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Glue7048

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.OrbLab CFSG.KS.RowTree
  CFSG.KS.RuTree CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.G2Ru7164 CFSG.Quasithin.RuRank3 CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.KC.BfsPin

theorem inD_eq {x : Nat} (hx : x < 4060) :
    (ruQLab[x]! == ruQLab[1]!) = (Ru7045.Row 0).testBit x := by
  rw [Q7307.qlab_get hx, Q7307.qlab_get (by norm_num), Bool.eq_iff_iff, beq_iff_eq,
    (Glue7045.rows 0 (by norm_num)).2 x hx, Glue7045.ti_zero hx]

theorem cntD_eq {v : Nat} (hv : v < 4060) : ruCntD (ruTI v) = Ru7048.cntD v := by
  unfold ruCntD Ru7048.cntD
  rw [Glue7045.popK_eq]
  apply List.countP_congr
  intro x hx
  have hx' := List.mem_range.1 hx
  rw [inD_eq hx', Glue7045.rowA_eq hv hx',
    show Nat.land (Ru7045.Row 0) (Ru7045.Row v) = Ru7045.Row 0 &&& Ru7045.Row v from rfl,
    Nat.testBit_and]

theorem common_eq {v : Nat} (hv : v < 4060) : ruCommonCnt ruTI1 (ruTI v) = Ru7048.cntC v := by
  unfold ruCommonCnt Ru7048.cntC
  rw [Glue7045.popK_eq]
  apply List.countP_congr
  intro x hx
  have hx' := List.mem_range.1 hx
  unfold ruInD
  rw [inD_eq hx', show ruTI1 = ruTI 1 from rfl, Glue7045.rowA_eq (by norm_num) hx',
    Glue7045.rowA_eq hv hx', show Nat.land (Nat.land (Ru7045.Row 0) (Ru7045.Row 1)) (Ru7045.Row v) =
      Ru7045.Row 0 &&& Ru7045.Row 1 &&& Ru7045.Row v from rfl, Nat.testBit_and, Nat.testBit_and]

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2.Native in
theorem c7048 :
    ruCntD ruTI1 = 730 ∧ ruCntD ruTIG0 = 780 :=
  ⟨by rw [show ruTI1 = ruTI 1 from rfl, cntD_eq (by norm_num)]; exact Ru7048.kD1,
    by rw [show ruTIG0 = ruTI 2808 from rfl, cntD_eq (by norm_num)]; exact Ru7048.kDG⟩

theorem lab_ok : (allLt 4060 fun x => (ruInD x && ruRowA ruTI1 x) ==
    (ruFLab[x]! == 2 || ruFLab[x]! == 6 || ruFLab[x]! == 7)) = true := by
  have hk := Ru7048.kLab
  unfold Ru7048.labOK at hk
  rw [sB_eq] at hk
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_
  have h := allN_spec hk x hx
  rw [Glue7045.eqB_eq, bt_eq, bt_eq,
    show Nat.land (Ru7045.Row 0) (Ru7045.Row 1) = Ru7045.Row 0 &&& Ru7045.Row 1 from rfl,
    Nat.testBit_and, beq_iff_eq] at h
  have hl := Glue7046.flab_lt hx
  unfold ruInD
  rw [inD_eq hx, show ruTI1 = ruTI 1 from rfl, Glue7045.rowA_eq (by norm_num) hx,
    Glue7046.flab_get hx, h]
  generalize F7046.Lf x = l at hl ⊢
  interval_cases l <;> decide

theorem labCount_eq (c : Nat) : labCount 4060 ruFLab c = F7046.cnt c := by
  unfold labCount F7046.cnt
  apply List.countP_congr
  intro x hx
  rw [Glue7046.flab_get (List.mem_range.1 hx), Q7307.nat_beq]

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem c7306 :
    (allLt 4060 fun x => (ruInD x && ruRowA ruTI1 x) ==
        (ruFLab[x]! == 2 || ruFLab[x]! == 6 || ruFLab[x]! == 7)) = true ∧
    labCount 4060 ruFLab 7 = 10 ∧ labCount 4060 ruFLab 6 = 80 ∧ labCount 4060 ruFLab 2 = 640 ∧
    ruFLab[2325]! = 7 ∧ ruFLab[149]! = 6 ∧ ruFLab[2]! = 2 ∧
    isInvA 4060 (ruTreeArr 2325) (ruTI 2325) = true ∧
    isInvA 4060 (ruTreeArr 149) (ruTI 149) = true ∧
    isInvA 4060 (ruTreeArr 2) (ruTI 2) = true ∧
    ruCommonCnt ruTI1 (ruTI 2325) = 217 ∧ ruCommonCnt ruTI1 (ruTI 149) = 345 ∧
    ruCommonCnt ruTI1 (ruTI 2) = 281 := by
  obtain ⟨-, -, c2, -, -, -, c6, c7⟩ := F7046.kCnt
  obtain ⟨l1, l2, l3⟩ := Ru7048.kL
  obtain ⟨k1, k2, k3⟩ := Ru7048.kC
  refine ⟨lab_ok, by rw [labCount_eq]; exact c7, by rw [labCount_eq]; exact c6,
    by rw [labCount_eq]; exact c2, by rw [Glue7046.flab_get (by norm_num)]; exact l1,
    by rw [Glue7046.flab_get (by norm_num)]; exact l2,
    by rw [Glue7046.flab_get (by norm_num)]; exact l3,
    Glue7045.isInv_tree (x := 2325) (by norm_num), Glue7045.isInv_tree (x := 149) (by norm_num),
    Glue7045.isInv_tree (x := 2) (by norm_num), by rw [common_eq (by norm_num)]; exact k1,
    by rw [common_eq (by norm_num)]; exact k2, by rw [common_eq (by norm_num)]; exact k3⟩

end CertificateChecks.KernelSporSch.Glue7048

end

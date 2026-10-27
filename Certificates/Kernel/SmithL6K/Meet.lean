module

public import Certificates.Kernel.SmithL6K.Pins
public import Certificates.Kernel.SmithL6K.PinsM
public import CFSG.Certificates.Kernel.SmithL6KMeet

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.Kernel

theorem wmk_length : wmk.length = 1395 := by decide +kernel

theorem wData_lt {i : Nat} (hi : i < 1395) : wData[i]! < 262144 := by
  rw [wData_get hi]
  exact of_decide_eq_true (List.all_eq_true.mp chk_wData _ (List.getElem_mem _))

theorem card_setM (M : Nat) : (setM M).card = (List.range 64).countP (fun x => M.testBit x) :=
  card_filter_range (fun x => M.testBit x) 64

theorem wMask_card {i : Nat} (hi : i < 1395) : (setM (wMask i)).card = 8 := by
  rw [card_setM, wMask_eq hi, getD_of_lt (by rw [wmk_length]; exact hi)]
  exact beq_iff_eq.mp (List.all_eq_true.mp chk_card _ (List.getElem_mem _))

theorem meetCard_formula {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    meetCard i j = ((setM (wMask i &&& wMask j)).card - 1) ^ 2 := by
  rw [meetCard_eq hi hj]
  exact meetCardK_formula (wData_lt hi) (wData_lt hj) (wMask_card hi) (wMask_card hj)

theorem meetCard_formula_countP {i j : Nat} (hi : i < 1395) (hj : j < 1395) :
    meetCard i j = ((List.range 64).countP (fun x => (wMask i &&& wMask j).testBit x) - 1) ^ 2 := by
  rw [meetCard_formula hi hj, card_setM]

end CertificateChecks.KernelSmithL6K

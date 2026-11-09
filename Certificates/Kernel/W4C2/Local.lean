module

public import Certificates.Kernel.W4C2.Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelW4C2

open CFSG.KC.W4C2K

theorem filter_drop_split {α : Type} (p : α → Bool) (l : List α) (c n d : Nat) (h : c + n = d) :
    (l.drop c).filter p = ((l.drop c).take n).filter p ++ (l.drop d).filter p := by
  subst h
  rw [← List.drop_drop, ← List.filter_append, List.take_append_drop]

theorem un0 : ((PN.drop 0).take 593).filter (isCommK PN) = [2216789025] := by
  decide +kernel

theorem un1 : ((PN.drop 593).take 7).filter (isCommK PN) = [2216920113] := by
  decide +kernel

theorem un2 : ((PN.drop 600).take 1).filter (isCommK PN) = [2217051425] := by
  decide +kernel

theorem un3 : ((PN.drop 601).take 87).filter (isCommK PN) = [2217182513] := by
  decide +kernel

theorem un4 : ((PN.drop 688).take 1).filter (isCommK PN) = [2217317409] := by
  decide +kernel

theorem un5 : ((PN.drop 689).take 7).filter (isCommK PN) = [2217448497] := by
  decide +kernel

theorem un6 : ((PN.drop 696).take 1).filter (isCommK PN) = [2217579809] := by
  decide +kernel

theorem un7 : (PN.drop 697).filter (isCommK PN) = [2217710897] := by decide +kernel

theorem ch330390un : (PN.filter (isCommK PN) == UN) = true := by
  have h : (PN.drop 0).filter (isCommK PN) = [2216789025, 2216920113, 2217051425, 2217182513,
      2217317409, 2217448497, 2217579809, 2217710897] := by
    rw [filter_drop_split _ _ 0 593 593 rfl, un0,
      filter_drop_split _ _ 593 7 600 rfl, un1,
      filter_drop_split _ _ 600 1 601 rfl, un2,
      filter_drop_split _ _ 601 87 688 rfl, un3,
      filter_drop_split _ _ 688 1 689 rfl, un4,
      filter_drop_split _ _ 689 7 696 rfl, un5,
      filter_drop_split _ _ 696 1 697 rfl, un6,
      un7]
    rfl
  rw [List.drop_zero] at h
  rw [h]
  decide +kernel

theorem ch330390cl : (PM.filter (isCommK PM) == CL) = true := by quickRfl

theorem ch330390chkN : chkNK PN UN = true := by quickRfl

theorem ch330390chkM : chkMK PM CL = true := by quickRfl

theorem ch330390orb : orbWK WIT = true := by quickRfl

end CertificateChecks.KernelW4C2

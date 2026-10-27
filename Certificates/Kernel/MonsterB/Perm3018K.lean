module

public import CFSG.Certificates.Kernel.SortTreeP
public import CFSG.Certificates.Kernel.SortTreeSlice
public import Certificates.Kernel.MonsterB.Perm3018Data
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Census.MonoData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SortTreeMul
public import Std.Data.HashMap

public section

namespace CertificateChecks.Perm3018

open CFSG.KC.SortTree CFSG.KLie.CT CFSG.Monster.B.TwoA.Census

set_option maxRecDepth 100000

@[expose] noncomputable def actS (k c : Nat) : Nat := amulP (fget GS k 120) c

@[expose] noncomputable def actO (k c : Nat) : Nat := conjP (fget GA k 120) (fget GAI k 120) c

@[expose] noncomputable def recS : Nat → Nat := recT S 6 140
@[expose] noncomputable def edgeS (i k : Nat) : Nat := fget (recT SE 6 100 i) k 10
@[expose] noncomputable def recO1 : Nat → Nat := recT O1 6 144
@[expose] noncomputable def edgeO1 (i k : Nat) : Nat := fget (recT O1E 6 28 i) k 14
@[expose] noncomputable def recO2 : Nat → Nat := recT O2 6 144
@[expose] noncomputable def edgeO2 (i k : Nat) : Nat := fget (recT O2E 6 32 i) k 15

@[expose] noncomputable def root1 : Nat := keyP (seedArr.getD 1 #[])

@[expose] noncomputable def root2 : Nat := keyP (seedArr.getD 2 #[])

theorem sT : treeOK actS 10 (fun _ => true) (keyP idArr) recS 1024 120 3 10 64 16 = true := by
  quickRfl

theorem sE : closeOK actS 10 recS edgeS 1024 120 64 16 = true := by quickRfl

theorem a1 : treeSl actO 2 (fun _ => true) root1 recO1 11385 120 6 14 64 0 89 = true := by quickRfl
theorem a2 : treeSl actO 2 (fun _ => true) root1 recO1 11385 120 6 14 64 89 89 = true := by
  quickRfl
theorem b1 : closeSl actO 2 recO1 edgeO1 11385 120 64 0 89 = true := by quickRfl
theorem b2 : closeSl actO 2 recO1 edgeO1 11385 120 64 89 89 = true := by quickRfl

theorem p1 : treeSl actO 2 (fun _ => true) root2 recO2 31878 120 6 15 64 0 100 = true := by
  quickRfl
theorem p2 : treeSl actO 2 (fun _ => true) root2 recO2 31878 120 6 15 64 100 100 = true := by
  quickRfl
theorem p3 : treeSl actO 2 (fun _ => true) root2 recO2 31878 120 6 15 64 200 100 = true := by
  quickRfl
theorem p4 : treeSl actO 2 (fun _ => true) root2 recO2 31878 120 6 15 64 300 100 = true := by
  quickRfl
theorem p5 : treeSl actO 2 (fun _ => true) root2 recO2 31878 120 6 15 64 400 99 = true := by
  quickRfl
theorem q1 : closeSl actO 2 recO2 edgeO2 31878 120 64 0 100 = true := by quickRfl
theorem q2 : closeSl actO 2 recO2 edgeO2 31878 120 64 100 100 = true := by quickRfl
theorem q3 : closeSl actO 2 recO2 edgeO2 31878 120 64 200 100 = true := by quickRfl
theorem q4 : closeSl actO 2 recO2 edgeO2 31878 120 64 300 100 = true := by quickRfl
theorem q5 : closeSl actO 2 recO2 edgeO2 31878 120 64 400 99 = true := by quickRfl

end CertificateChecks.Perm3018

end

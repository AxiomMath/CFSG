module

public import CFSG.Certificates.Kernel.SortTreeMul
public import CFSG.Certificates.Kernel.SortTreeSlice
public import Certificates.Kernel.MonsterB.Frame3055Data
public import CFSG.Monster.B.TwoA.Census.PermBFS
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Monster.Code.Weights
public import Mathlib.GroupTheory.Perm.Basic
public import Std.Data.HashMap

public section

namespace CertificateChecks.Frame3055

open CFSG.KC.SortTree CFSG.KLie.CT CFSG.Monster.B.TwoA.Census

set_option maxRecDepth 100000

@[expose] noncomputable def actM (k c : Nat) : Nat := amulK (fget GF k 120) c

@[expose] noncomputable def recF : Nat → Nat := recT F 6 136

@[expose] noncomputable def edgeF (i k : Nat) : Nat := fget (recT FE 6 128 i) k 14

theorem t0 : treeSl actM 9 (fun _ => true) (akey idArr) recF 11520 111 4 14 64 0 60 = true := by
  quickRfl
theorem t1 : treeSl actM 9 (fun _ => true) (akey idArr) recF 11520 111 4 14 64 60 60 = true := by
  quickRfl
theorem t2 : treeSl actM 9 (fun _ => true) (akey idArr) recF 11520 111 4 14 64 120 60 = true := by
  quickRfl

theorem c0 : closeSl actM 9 recF edgeF 11520 111 64 0 15 = true := by quickRfl
theorem c1 : closeSl actM 9 recF edgeF 11520 111 64 15 15 = true := by quickRfl
theorem c2 : closeSl actM 9 recF edgeF 11520 111 64 30 15 = true := by quickRfl
theorem c3 : closeSl actM 9 recF edgeF 11520 111 64 45 15 = true := by quickRfl
theorem c4 : closeSl actM 9 recF edgeF 11520 111 64 60 15 = true := by quickRfl
theorem c5 : closeSl actM 9 recF edgeF 11520 111 64 75 15 = true := by quickRfl
theorem c6 : closeSl actM 9 recF edgeF 11520 111 64 90 15 = true := by quickRfl
theorem c7 : closeSl actM 9 recF edgeF 11520 111 64 105 15 = true := by quickRfl
theorem c8 : closeSl actM 9 recF edgeF 11520 111 64 120 15 = true := by quickRfl
theorem c9 : closeSl actM 9 recF edgeF 11520 111 64 135 15 = true := by quickRfl
theorem c10 : closeSl actM 9 recF edgeF 11520 111 64 150 15 = true := by quickRfl
theorem c11 : closeSl actM 9 recF edgeF 11520 111 64 165 15 = true := by quickRfl

end CertificateChecks.Frame3055

end

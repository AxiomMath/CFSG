module

public import Certificates.Data.Kernel.S75Gen4.Check
public import Certificates.Kernel.S75Gen4.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelS75Gen4

open CFSG.KD.S5Ext CFSG.KD.S75Gen4

@[expose] def swL : List (List (Nat × Nat)) :=
  [[(6, 7), (8, 9)], [(4, 6), (5, 7)], [(0, 4), (1, 5), (2, 6), (3, 7)]]

theorem ch6132_id10 : idB 10 TAB10 = true := by quickRfl
theorem ch6132_id11 : idB 11 TAB11 = true := by quickRfl
theorem ch6132_inc10 : lanesB 10 TAB10 = true := by quickRfl
theorem ch6132_inc11 : lanesB 11 TAB11 = true := by quickRfl
theorem ch6132_sw10 : swB 10 TAB10 GI swL = true := by quickRfl
theorem ch6132_sw11 : swB 11 TAB11 GI swL = true := by quickRfl
theorem ch6132_mp10a : mpB 10 TAB10 MP 0 32 = true := by quickRfl
theorem ch6132_mp10b : mpB 10 TAB10 MP 32 32 = true := by quickRfl
theorem ch6132_mp10c : mpB 10 TAB10 MP 64 32 = true := by quickRfl
theorem ch6132_mp10d : mpB 10 TAB10 MP 96 32 = true := by quickRfl
theorem ch6132_mp11a : mpB 11 TAB11 MP 0 32 = true := by quickRfl
theorem ch6132_mp11b : mpB 11 TAB11 MP 32 32 = true := by quickRfl
theorem ch6132_mp11c : mpB 11 TAB11 MP 64 32 = true := by quickRfl
theorem ch6132_mp11d : mpB 11 TAB11 MP 96 32 = true := by quickRfl
theorem ch6132_tree :
    (treeG MP GI TREE 1).1 = true ∧ Nat.beq (treeG MP GI TREE 1).2 FULL = true := by
  constructor <;> quickRfl
theorem ch6132_inv : invB2 MP INVP = true := by quickRfl
theorem ch6132_sq : sqB MP SQP = true := by quickRfl
theorem ch6132_bnd : bndB CATP 576 = true := by quickRfl
theorem ch6132_one : Nat.beq (lC CATP 0) 1 = true := by quickRfl

end CertificateChecks.KernelS75Gen4

end

module

public import Certificates.Kernel.HN1408.Tr2Defs
public import Certificates.Kernel.HN1408.FctData
public import Certificates.Kernel.HN1408.FctDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.FixR

open CFSG.KC.Enum CFSG.KS CFSG.KD.HN1408.Tr2 CFSG.EvenSporadicStandard.HNRecog

theorem fct3_head : headK fix3.cent fix3.rep Fct3.G Fct3.T0 Fct3.T1 = true := by quickRfl
theorem fct3_keys : keysK 40 Fct3.T0 = true := by quickRfl
theorem fct3_tree : allN 40 (treeK 4 40 Fct3.G Fct3.T0 Fct3.P0) = true := by quickRfl
theorem fct3_sch : allN 3 (schK 4 40 Fct3.G Fct3.T0 Fct3.S Fct3.SR) = true := by quickRfl
theorem fct3_t1 : allN 36 (t1K 3 Fct3.S Fct3.T1 Fct3.P1) = true := by quickRfl

theorem fct5a_head : headK cent5aW rep5aW Fct5a.G Fct5a.T0 Fct5a.T1 = true := by quickRfl
theorem fct5a_keys : keysK 1000 Fct5a.T0 = true := by quickRfl
theorem fct5a_tree0 : allN 500 (treeK 4 1000 Fct5a.G Fct5a.T0 Fct5a.P0) = true := by quickRfl
theorem fct5a_tree1 : allN 500 (fun i => treeK 4 1000 Fct5a.G Fct5a.T0 Fct5a.P0 (Nat.add 500 i)) =
    true := by quickRfl
theorem fct5a_sch : allN 1 (schK 4 1000 Fct5a.G Fct5a.T0 Fct5a.S Fct5a.SR) = true := by quickRfl
theorem fct5a_t1 : allN 2 (t1K 1 Fct5a.S Fct5a.T1 Fct5a.P1) = true := by quickRfl

theorem fct5b_head : headK fix5B.cent fix5B.rep Fct5b.G Fct5b.T0 Fct5b.T1 = true := by quickRfl
theorem fct5b_keys : keysK 4 Fct5b.T0 = true := by quickRfl
theorem fct5b_tree : allN 4 (treeK 2 4 Fct5b.G Fct5b.T0 Fct5b.P0) = true := by quickRfl
theorem fct5b_sch : allN 2 (schK 2 4 Fct5b.G Fct5b.T0 Fct5b.S Fct5b.SR) = true := by quickRfl
theorem fct5b_t1 : allN 25 (t1K 2 Fct5b.S Fct5b.T1 Fct5b.P1) = true := by quickRfl

theorem fct5c_head : headK fix5C.cent fix5C.rep Fct5c.G Fct5c.T0 Fct5c.T1 = true := by quickRfl
theorem fct5c_keys : keysK 48 Fct5c.T0 = true := by quickRfl
theorem fct5c_tree : allN 48 (treeK 3 48 Fct5c.G Fct5c.T0 Fct5c.P0) = true := by quickRfl
theorem fct5c_sch : allN 2 (schK 3 48 Fct5c.G Fct5c.T0 Fct5c.S Fct5c.SR) = true := by quickRfl
theorem fct5c_t1 : allN 25 (t1K 2 Fct5c.S Fct5c.T1 Fct5c.P1) = true := by quickRfl

theorem fct7_head : headK fix7.cent fix7.rep Fct7.G Fct7.T0 Fct7.T1 = true := by quickRfl
theorem fct7_keys : keysK 4 Fct7.T0 = true := by quickRfl
theorem fct7_tree : allN 4 (treeK 2 4 Fct7.G Fct7.T0 Fct7.P0) = true := by quickRfl
theorem fct7_sch : allN 1 (schK 2 4 Fct7.G Fct7.T0 Fct7.S Fct7.SR) = true := by quickRfl
theorem fct7_t1 : allN 7 (t1K 1 Fct7.S Fct7.T1 Fct7.P1) = true := by quickRfl

end CFSG.KD.HN1408.FixR

end

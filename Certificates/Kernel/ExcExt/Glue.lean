module

public import CFSG.Certificates.Kernel.ExcExt.Sound
public import Certificates.Kernel.ExcExt.TabChecks
public import Certificates.Kernel.ExcExt.TabChecksE8
public import Certificates.Kernel.ExcExt.Lines
public import Certificates.Kernel.ExcExt.LinesE8a
public import Certificates.Kernel.ExcExt.LinesE8b
public import Certificates.Kernel.ExcExt.LinesE8c

public section

namespace CFSG.ExcExtK

open CFSG.StandardType.GGQ2Frame.ExcRaw

theorem tabsOK_D0 : TabsOK 0 D.T0 D.fx0 D.hx0 D.fx0 D.hx0 :=
  TabsOK.of_bool (m' := 0) (by decide) ch712526tab0 fun c hc =>
    zm_of_range ch712526zm0 (Nat.zero_le c) (by have : (3 : Nat) ^ dim 0 = 81 := (by decide); omega)

theorem tabsOK_D1 : TabsOK 1 D.T1 D.fx1 D.hx1 D.fx1 D.hx1 :=
  TabsOK.of_bool (m' := 1) (by decide) ch712526tab1 fun c hc =>
    zm_of_range ch712526zm1 (Nat.zero_le c) (by have : (3 : Nat) ^ dim 1 = 81 := (by decide); omega)

theorem tabsOK_D2 : TabsOK 2 D.T2 D.fx2 D.hx2 D.fx2 D.hx2 :=
  TabsOK.of_bool (m' := 2) (by decide) ch712526tab2 fun c hc =>
    zm_of_range ch712526zm2 (Nat.zero_le c) (by have : (3 : Nat) ^ dim 2 = 729 := (by decide); omega)

theorem tabsOK_D3 : TabsOK 3 D.T3 D.fx3 D.hx3 D.fx2 D.hx2 :=
  TabsOK.of_bool (m' := 2) (by decide) ch712526tab3 fun c hc =>
    zm_of_range ch712526zm3 (Nat.zero_le c) (by have : (3 : Nat) ^ dim 3 = 243 := (by decide); omega)

theorem tabsOK_D4 : TabsOK 4 D.T4 D.fx4 D.hx4 D.fx4 D.hx4 :=
  TabsOK.of_bool (m' := 4) (by decide) ch712526tab4 fun c hc =>
    zm_of_range ch712526zm4 (Nat.zero_le c) (by have : (3 : Nat) ^ dim 4 = 2187 := (by decide); omega)

theorem tabsOK_D5 : TabsOK 5 D.T5 D.fx5 D.hx5 D.fx5 D.hx5 :=
  TabsOK.of_bool (m' := 5) (by decide) ch712526tab5 fun c hc =>
    zm_all_of_chunks (K := D.T5) (w := 729) (q := 9)
      (fun j hj =>
        match j, hj with
        | 0, _ => ch712526zm5_0
        | 1, _ => ch712526zm5_1
        | 2, _ => ch712526zm5_2
        | 3, _ => ch712526zm5_3
        | 4, _ => ch712526zm5_4
        | 5, _ => ch712526zm5_5
        | 6, _ => ch712526zm5_6
        | 7, _ => ch712526zm5_7
        | 8, _ => ch712526zm5_8
        | _ + 9, h => absurd h (by omega))
      c (by have : (3 : Nat) ^ dim 5 = 6561 := (by decide); omega)

theorem tabsOK0 : Chk.tabsOK 0 (tabsK 0 D.T0) = true := tabsOK_tabsK tabsOK_D0
theorem tabsOK1 : Chk.tabsOK 1 (tabsK 1 D.T1) = true := tabsOK_tabsK tabsOK_D1
theorem tabsOK2 : Chk.tabsOK 2 (tabsK 2 D.T2) = true := tabsOK_tabsK tabsOK_D2
theorem tabsOK3 : Chk.tabsOK 3 (tabsK 3 D.T3) = true := tabsOK_tabsK tabsOK_D3
theorem tabsOK4 : Chk.tabsOK 4 (tabsK 4 D.T4) = true := tabsOK_tabsK tabsOK_D4
theorem tabsOK5 : Chk.tabsOK 5 (tabsK 5 D.T5) = true := tabsOK_tabsK tabsOK_D5

theorem ext0_0 : ExtLineOK 0 D.T0 D0.L0 := scanLineK_sound tabsOK_D0 ch712526l0_0
theorem ext0_1 : ExtLineOK 0 D.T0 D0.L1 := scanLineK_sound tabsOK_D0 ch712526l0_1
theorem ext0_5 : ExtLineOK 0 D.T0 D0.L5 := scanLineK_sound tabsOK_D0 ch712526l0_5
theorem ext0_9 : ExtLineOK 0 D.T0 D0.L9 := scanLineK_sound tabsOK_D0 ch712526l0_9

theorem ext1_0 : ExtLineOK 1 D.T1 D1.L0 := scanLineK_sound tabsOK_D1 ch712526l1_0
theorem ext1_1 : ExtLineOK 1 D.T1 D1.L1 := scanLineK_sound tabsOK_D1 ch712526l1_1
theorem ext1_5 : ExtLineOK 1 D.T1 D1.L5 := scanLineK_sound tabsOK_D1 ch712526l1_5
theorem ext1_9 : ExtLineOK 1 D.T1 D1.L9 := scanLineK_sound tabsOK_D1 ch712526l1_9

theorem ext2_0 : ExtLineOK 2 D.T2 D2.L0 := scanLineK_sound tabsOK_D2 ch712526l2_0
theorem ext2_1 : ExtLineOK 2 D.T2 D2.L1 := scanLineK_sound tabsOK_D2 ch712526l2_1
theorem ext2_2 : ExtLineOK 2 D.T2 D2.L2 := scanLineK_sound tabsOK_D2 ch712526l2_2
theorem ext2_3 : ExtLineOK 2 D.T2 D2.L3 := scanLineK_sound tabsOK_D2 ch712526l2_3
theorem ext2_4 : ExtLineOK 2 D.T2 D2.L4 := scanLineK_sound tabsOK_D2 ch712526l2_4
theorem ext2_8 : ExtLineOK 2 D.T2 D2.L8 := scanLineK_sound tabsOK_D2 ch712526l2_8
theorem ext2_13 : ExtLineOK 2 D.T2 D2.L13 := scanLineK_sound tabsOK_D2 ch712526l2_13
theorem ext2_27 : ExtLineOK 2 D.T2 D2.L27 := scanLineK_sound tabsOK_D2 ch712526l2_27

theorem ext3_0 : ExtLineOK 3 D.T3 D3.L0 := scanLineK_sound tabsOK_D3 ch712526l3_0
theorem ext3_1 : ExtLineOK 3 D.T3 D3.L1 := scanLineK_sound tabsOK_D3 ch712526l3_1
theorem ext3_4 : ExtLineOK 3 D.T3 D3.L4 := scanLineK_sound tabsOK_D3 ch712526l3_4
theorem ext3_11 : ExtLineOK 3 D.T3 D3.L11 := scanLineK_sound tabsOK_D3 ch712526l3_11

theorem ext4_0 : ExtLineOK 4 D.T4 D4.L0 := scanLineK_sound tabsOK_D4 ch712526l4_0
theorem ext4_1 : ExtLineOK 4 D.T4 D4.L1 := scanLineK_sound tabsOK_D4 ch712526l4_1
theorem ext4_4 : ExtLineOK 4 D.T4 D4.L4 := scanLineK_sound tabsOK_D4 ch712526l4_4
theorem ext4_11 : ExtLineOK 4 D.T4 D4.L11 := scanLineK_sound tabsOK_D4 ch712526l4_11
theorem ext4_14 : ExtLineOK 4 D.T4 D4.L14 := scanLineK_sound tabsOK_D4 ch712526l4_14
theorem ext4_416 : ExtLineOK 4 D.T4 D4.L416 := scanLineK_sound tabsOK_D4 ch712526l4_416

theorem ext5_0 : ExtLineOK 5 D.T5 D5.L0 := scanLineK_sound tabsOK_D5 ch712526l5_0
theorem ext5_1 : ExtLineOK 5 D.T5 D5.L1 := scanLineK_sound tabsOK_D5 ch712526l5_1
theorem ext5_4 : ExtLineOK 5 D.T5 D5.L4 := scanLineK_sound tabsOK_D5 ch712526l5_4
theorem ext5_11 : ExtLineOK 5 D.T5 D5.L11 := scanLineK_sound tabsOK_D5 ch712526l5_11
theorem ext5_14 : ExtLineOK 5 D.T5 D5.L14 := scanLineK_sound tabsOK_D5 ch712526l5_14

end CFSG.ExcExtK

end

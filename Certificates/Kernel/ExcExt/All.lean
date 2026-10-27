module

public import Certificates.Kernel.ExcExt.Glue
public import Certificates.Kernel.ExcExt.OrbitChecks
public import CFSG.Certificates.Kernel.ExcExt.OrbitSound

public section

namespace CFSG.ExcExtK

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw

theorem extCasesVx0 (vx : V 0) : ExtCasesVx (excRaw 0) vx := by
  refine extCasesVx_of_orbit tabsOK_D0 tabsOK0 (B := O.B0) (reps := [0, 1, 5, 9])
    (orbOK_all (w := 81) (q := 1) (by decide) fun j hj => ?_) (fun c hc => ?_) vx
  · obtain rfl : j = 0 := by omega
    exact ch712526orb0
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact extCasesVx_of_line tabsOK0 ext0_0 rfl (by decide)
    · exact extCasesVx_of_line tabsOK0 ext0_1 rfl (by decide)
    · exact extCasesVx_of_line tabsOK0 ext0_5 rfl (by decide)
    · exact extCasesVx_of_line tabsOK0 ext0_9 rfl (by decide)

theorem extCasesVx1 (vx : V 1) : ExtCasesVx (excRaw 1) vx := by
  refine extCasesVx_of_orbit tabsOK_D1 tabsOK1 (B := O.B1) (reps := [0, 1, 5, 9])
    (orbOK_all (w := 81) (q := 1) (by decide) fun j hj => ?_) (fun c hc => ?_) vx
  · obtain rfl : j = 0 := by omega
    exact ch712526orb1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact extCasesVx_of_line tabsOK1 ext1_0 rfl (by decide)
    · exact extCasesVx_of_line tabsOK1 ext1_1 rfl (by decide)
    · exact extCasesVx_of_line tabsOK1 ext1_5 rfl (by decide)
    · exact extCasesVx_of_line tabsOK1 ext1_9 rfl (by decide)

theorem extCasesVx2 (vx : V 2) : ExtCasesVx (excRaw 2) vx := by
  refine extCasesVx_of_orbit tabsOK_D2 tabsOK2 (B := O.B2) (reps := [0, 1, 2, 3, 4, 8, 13, 27])
    (orbOK_all (w := 729) (q := 1) (by decide) fun j hj => ?_) (fun c hc => ?_) vx
  · obtain rfl : j = 0 := by omega
    exact ch712526orb2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact extCasesVx_of_line tabsOK2 ext2_0 rfl (by decide)
    · exact extCasesVx_of_line tabsOK2 ext2_1 rfl (by decide)
    · exact extCasesVx_of_line tabsOK2 ext2_2 rfl (by decide)
    · exact extCasesVx_of_line tabsOK2 ext2_3 rfl (by decide)
    · exact extCasesVx_of_line tabsOK2 ext2_4 rfl (by decide)
    · exact extCasesVx_of_line tabsOK2 ext2_8 rfl (by decide)
    · exact extCasesVx_of_line tabsOK2 ext2_13 rfl (by decide)
    · exact extCasesVx_of_line tabsOK2 ext2_27 rfl (by decide)

theorem extCasesVx3 (vx : V 3) : ExtCasesVx (excRaw 3) vx := by
  refine extCasesVx_of_orbit tabsOK_D3 tabsOK3 (B := O.B3) (reps := [0, 1, 4, 11])
    (orbOK_all (w := 243) (q := 1) (by decide) fun j hj => ?_) (fun c hc => ?_) vx
  · obtain rfl : j = 0 := by omega
    exact ch712526orb3
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact extCasesVx_of_line tabsOK3 ext3_0 rfl (by decide)
    · exact extCasesVx_of_line tabsOK3 ext3_1 rfl (by decide)
    · exact extCasesVx_of_line tabsOK3 ext3_4 rfl (by decide)
    · exact extCasesVx_of_line tabsOK3 ext3_11 rfl (by decide)

theorem extCasesVx4 (vx : V 4) : ExtCasesVx (excRaw 4) vx := by
  refine extCasesVx_of_orbit tabsOK_D4 tabsOK4 (B := O.B4) (reps := [0, 1, 4, 11, 14, 416])
    (orbOK_all (w := 729) (q := 3) (by decide) fun j hj => ?_) (fun c hc => ?_) vx
  · match j, hj with
    | 0, _ => exact ch712526orb4_0
    | 1, _ => exact ch712526orb4_1
    | 2, _ => exact ch712526orb4_2
    | _ + 3, h => exact absurd h (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact extCasesVx_of_line tabsOK4 ext4_0 rfl (by decide)
    · exact extCasesVx_of_line tabsOK4 ext4_1 rfl (by decide)
    · exact extCasesVx_of_line tabsOK4 ext4_4 rfl (by decide)
    · exact extCasesVx_of_line tabsOK4 ext4_11 rfl (by decide)
    · exact extCasesVx_of_line tabsOK4 ext4_14 rfl (by decide)
    · exact extCasesVx_of_line tabsOK4 ext4_416 rfl (by decide)

theorem extCasesVx5 (vx : V 5) : ExtCasesVx (excRaw 5) vx := by
  refine extCasesVx_of_orbit tabsOK_D5 tabsOK5 (B := O.B5) (reps := [0, 1, 4, 11, 14])
    (orbOK_all (w := 729) (q := 9) (by decide) fun j hj => ?_) (fun c hc => ?_) vx
  · match j, hj with
    | 0, _ => exact ch712526orb5_0
    | 1, _ => exact ch712526orb5_1
    | 2, _ => exact ch712526orb5_2
    | 3, _ => exact ch712526orb5_3
    | 4, _ => exact ch712526orb5_4
    | 5, _ => exact ch712526orb5_5
    | 6, _ => exact ch712526orb5_6
    | 7, _ => exact ch712526orb5_7
    | 8, _ => exact ch712526orb5_8
    | _ + 9, h => exact absurd h (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact extCasesVx_of_line tabsOK5 ext5_0 rfl (by decide)
    · exact extCasesVx_of_line tabsOK5 ext5_1 rfl (by decide)
    · exact extCasesVx_of_line tabsOK5 ext5_4 rfl (by decide)
    · exact extCasesVx_of_line tabsOK5 ext5_11 rfl (by decide)
    · exact extCasesVx_of_line tabsOK5 ext5_14 rfl (by decide)

end CFSG.ExcExtK

end

module

public import Certificates.Kernel.ExcExt.Glue
public import Certificates.Kernel.ExcExt.OrbitChecks
public import Certificates.Kernel.ExcExt.CensusLines
public import Certificates.Kernel.ExcExt.CensusLinesE8a
public import Certificates.Kernel.ExcExt.CensusLinesE8b
public import CFSG.Certificates.Kernel.ExcExt.CensusSound
public import CFSG.Certificates.Kernel.ExcExt.OrbitSoundP
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusLine

public section

namespace CFSG.ExcExtK

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw

theorem censusCasesVx_of_line {m : Fin 6} {K : KT} (hT : Chk.tabsOK m (tabsK m K) = true)
    {L : KCLine} (h : CensusLineOK m K L) {c : ℕ} (hcv : L.cv = c) (hc : c < 3 ^ dim m) :
    CensusCasesVx (excRaw m) (vec m c) := by
  subst hcv
  refine censusCasesVx_of_scanLineN hT (X := csearchOf m L) ?_
  rw [code_vec m hc]
  exact h

theorem cen0_0 : CensusLineOK 0 D.T0 C0.L0 := scanLineCK_sound tabsOK_D0 ch712511l0_0
theorem cen0_1 : CensusLineOK 0 D.T0 C0.L1 := scanLineCK_sound tabsOK_D0 ch712511l0_1
theorem cen0_5 : CensusLineOK 0 D.T0 C0.L5 := scanLineCK_sound tabsOK_D0 ch712511l0_5
theorem cen0_9 : CensusLineOK 0 D.T0 C0.L9 := scanLineCK_sound tabsOK_D0 ch712511l0_9

theorem cen1_0 : CensusLineOK 1 D.T1 C1.L0 := scanLineCK_sound tabsOK_D1 ch712511l1_0
theorem cen1_1 : CensusLineOK 1 D.T1 C1.L1 := scanLineCK_sound tabsOK_D1 ch712511l1_1
theorem cen1_5 : CensusLineOK 1 D.T1 C1.L5 := scanLineCK_sound tabsOK_D1 ch712511l1_5
theorem cen1_9 : CensusLineOK 1 D.T1 C1.L9 := scanLineCK_sound tabsOK_D1 ch712511l1_9

theorem cen2_0 : CensusLineOK 2 D.T2 C2.L0 := scanLineCK_sound tabsOK_D2 ch712511l2_0
theorem cen2_1 : CensusLineOK 2 D.T2 C2.L1 := scanLineCK_sound tabsOK_D2 ch712511l2_1
theorem cen2_2 : CensusLineOK 2 D.T2 C2.L2 := scanLineCK_sound tabsOK_D2 ch712511l2_2
theorem cen2_3 : CensusLineOK 2 D.T2 C2.L3 := scanLineCK_sound tabsOK_D2 ch712511l2_3
theorem cen2_4 : CensusLineOK 2 D.T2 C2.L4 := scanLineCK_sound tabsOK_D2 ch712511l2_4
theorem cen2_8 : CensusLineOK 2 D.T2 C2.L8 := scanLineCK_sound tabsOK_D2 ch712511l2_8
theorem cen2_13 : CensusLineOK 2 D.T2 C2.L13 := scanLineCK_sound tabsOK_D2 ch712511l2_13
theorem cen2_27 : CensusLineOK 2 D.T2 C2.L27 := scanLineCK_sound tabsOK_D2 ch712511l2_27

theorem cen3_0 : CensusLineOK 3 D.T3 C3.L0 := scanLineCK_sound tabsOK_D3 ch712511l3_0
theorem cen3_1 : CensusLineOK 3 D.T3 C3.L1 := scanLineCK_sound tabsOK_D3 ch712511l3_1
theorem cen3_4 : CensusLineOK 3 D.T3 C3.L4 := scanLineCK_sound tabsOK_D3 ch712511l3_4
theorem cen3_11 : CensusLineOK 3 D.T3 C3.L11 := scanLineCK_sound tabsOK_D3 ch712511l3_11

theorem cen4_0 : CensusLineOK 4 D.T4 C4.L0 := scanLineCK_sound tabsOK_D4 ch712511l4_0
theorem cen4_1 : CensusLineOK 4 D.T4 C4.L1 := scanLineCK_sound tabsOK_D4 ch712511l4_1
theorem cen4_4 : CensusLineOK 4 D.T4 C4.L4 := scanLineCK_sound tabsOK_D4 ch712511l4_4
theorem cen4_11 : CensusLineOK 4 D.T4 C4.L11 := scanLineCK_sound tabsOK_D4 ch712511l4_11
theorem cen4_14 : CensusLineOK 4 D.T4 C4.L14 := scanLineCK_sound tabsOK_D4 ch712511l4_14
theorem cen4_416 : CensusLineOK 4 D.T4 C4.L416 := scanLineCK_sound tabsOK_D4 ch712511l4_416

theorem cen5_0 : CensusLineOK 5 D.T5 C5.L0 := scanLineCK_sound tabsOK_D5 ch712511l5_0
theorem cen5_1 : CensusLineOK 5 D.T5 C5.L1 := scanLineCK_sound tabsOK_D5 ch712511l5_1
theorem cen5_4 : CensusLineOK 5 D.T5 C5.L4 := scanLineCK_sound tabsOK_D5 ch712511l5_4
theorem cen5_11 : CensusLineOK 5 D.T5 C5.L11 := scanLineCK_sound tabsOK_D5 ch712511l5_11
theorem cen5_14 : CensusLineOK 5 D.T5 C5.L14 := scanLineCK_sound tabsOK_D5 ch712511l5_14

theorem censusCasesVx0 (vx : V 0) : CensusCasesVx (excRaw 0) vx := by
  refine of_orbit tabsOK_D0 _ (fun u v h => censusCasesVx_reflection tabsOK0 u h)
    (B := O.B0) (reps := [0, 1, 5, 9])
    (orbOK_all (w := 81) (q := 1) (by decide) fun j hj => ?_) (fun c hc => ?_) vx
  · obtain rfl : j = 0 := by omega
    exact ch712526orb0
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact censusCasesVx_of_line tabsOK0 cen0_0 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK0 cen0_1 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK0 cen0_5 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK0 cen0_9 rfl (by decide)

theorem censusCasesVx1 (vx : V 1) : CensusCasesVx (excRaw 1) vx := by
  refine of_orbit tabsOK_D1 _ (fun u v h => censusCasesVx_reflection tabsOK1 u h)
    (B := O.B1) (reps := [0, 1, 5, 9])
    (orbOK_all (w := 81) (q := 1) (by decide) fun j hj => ?_) (fun c hc => ?_) vx
  · obtain rfl : j = 0 := by omega
    exact ch712526orb1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact censusCasesVx_of_line tabsOK1 cen1_0 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK1 cen1_1 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK1 cen1_5 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK1 cen1_9 rfl (by decide)

theorem censusCasesVx2 (vx : V 2) : CensusCasesVx (excRaw 2) vx := by
  refine of_orbit tabsOK_D2 _ (fun u v h => censusCasesVx_reflection tabsOK2 u h)
    (B := O.B2) (reps := [0, 1, 2, 3, 4, 8, 13, 27])
    (orbOK_all (w := 729) (q := 1) (by decide) fun j hj => ?_) (fun c hc => ?_) vx
  · obtain rfl : j = 0 := by omega
    exact ch712526orb2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact censusCasesVx_of_line tabsOK2 cen2_0 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK2 cen2_1 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK2 cen2_2 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK2 cen2_3 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK2 cen2_4 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK2 cen2_8 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK2 cen2_13 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK2 cen2_27 rfl (by decide)

theorem censusCasesVx3 (vx : V 3) : CensusCasesVx (excRaw 3) vx := by
  refine of_orbit tabsOK_D3 _ (fun u v h => censusCasesVx_reflection tabsOK3 u h)
    (B := O.B3) (reps := [0, 1, 4, 11])
    (orbOK_all (w := 243) (q := 1) (by decide) fun j hj => ?_) (fun c hc => ?_) vx
  · obtain rfl : j = 0 := by omega
    exact ch712526orb3
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact censusCasesVx_of_line tabsOK3 cen3_0 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK3 cen3_1 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK3 cen3_4 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK3 cen3_11 rfl (by decide)

theorem censusCasesVx4 (vx : V 4) : CensusCasesVx (excRaw 4) vx := by
  refine of_orbit tabsOK_D4 _ (fun u v h => censusCasesVx_reflection tabsOK4 u h)
    (B := O.B4) (reps := [0, 1, 4, 11, 14, 416])
    (orbOK_all (w := 729) (q := 3) (by decide) fun j hj => ?_) (fun c hc => ?_) vx
  · match j, hj with
    | 0, _ => exact ch712526orb4_0
    | 1, _ => exact ch712526orb4_1
    | 2, _ => exact ch712526orb4_2
    | _ + 3, h => exact absurd h (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact censusCasesVx_of_line tabsOK4 cen4_0 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK4 cen4_1 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK4 cen4_4 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK4 cen4_11 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK4 cen4_14 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK4 cen4_416 rfl (by decide)

theorem censusCasesVx5 (vx : V 5) : CensusCasesVx (excRaw 5) vx := by
  refine of_orbit tabsOK_D5 _ (fun u v h => censusCasesVx_reflection tabsOK5 u h)
    (B := O.B5) (reps := [0, 1, 4, 11, 14])
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
    · exact censusCasesVx_of_line tabsOK5 cen5_0 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK5 cen5_1 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK5 cen5_4 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK5 cen5_11 rfl (by decide)
    · exact censusCasesVx_of_line tabsOK5 cen5_14 rfl (by decide)

end CFSG.ExcExtK

end

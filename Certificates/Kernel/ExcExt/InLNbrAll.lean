
module

public import Certificates.Kernel.ExcExt.Glue
public import Certificates.Kernel.ExcExt.OrbitChecks
public import Certificates.Kernel.ExcExt.InLNbrChecks
public import CFSG.Certificates.Kernel.ExcExt.InLNbrSound
public import CFSG.Certificates.Kernel.ExcExt.OrbitSoundP
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusLine
public import CFSG.LocalAnalysis.StandardType.GGQ2InLCommonMainBase
public import CFSG.LocalAnalysis.StandardType.GGQ2TableBNbrExcBase

public section

namespace CFSG.ExcExtK

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw

variable {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat}

theorem inLCommonCasesVx_of_lineK (hK : TabsOK m K fx hx fx' hx') {L : KILine}
    (h : scanLineIK K L = true) {c : ℕ} (hcv : L.cv = c) (hc : c < 3 ^ dim m) :
    InLCommonCasesVx (excRaw m) (vec m c) := by
  subst hcv
  refine inLCommonCasesVx_of_scanLineN (tabsOK_tabsK hK) (X := isearchOf m L) ?_
  rw [code_vec m hc]
  exact scanLineIK_sound hK hc h

theorem nbrWeylDataVx_of_lineK (hK : TabsOK m K fx hx fx' hx') {c : ℕ} {cs : List KComp}
    (h : nbrLineK K c cs = true) (hc : c < 3 ^ dim m) : NbrWeylDataVx (excRaw m) (vec m c) := by
  refine nbrWeylDataVx_of_nbrLineOK (tabsOK_tabsK hK) (X := nsearchOf cs) ?_
  rw [code_vec m hc]
  exact nbrLineK_sound hK hc h

theorem nbrWeylDataVx_zero (m : Fin 6) : NbrWeylDataVx (excRaw m) (vec m 0) := by
  intro k hv
  exact absurd (vec_zero m) hv

theorem inLCommonCasesVx4 (vx : V 4) : InLCommonCasesVx (excRaw 4) vx := by
  refine of_orbit tabsOK_D4 _ (fun u v h => inLCommonCasesVx_reflection tabsOK4 u h)
    (B := O.B4) (reps := [0, 1, 4, 11, 14, 416])
    (orbOK_all (w := 729) (q := 3) (by decide) fun j hj => ?_) (fun c hc => ?_) vx
  · match j, hj with
    | 0, _ => exact ch712526orb4_0
    | 1, _ => exact ch712526orb4_1
    | 2, _ => exact ch712526orb4_2
    | _ + 3, h => exact absurd h (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact inLCommonCasesVx_of_lineK tabsOK_D4 ch712525l4_0 rfl (by decide)
    · exact inLCommonCasesVx_of_lineK tabsOK_D4 ch712525l4_1 rfl (by decide)
    · exact inLCommonCasesVx_of_lineK tabsOK_D4 ch712525l4_4 rfl (by decide)
    · exact inLCommonCasesVx_of_lineK tabsOK_D4 ch712525l4_11 rfl (by decide)
    · exact inLCommonCasesVx_of_lineK tabsOK_D4 ch712525l4_14 rfl (by decide)
    · exact inLCommonCasesVx_of_lineK tabsOK_D4 ch712525l4_416 rfl (by decide)

theorem nbrWeylDataVx0 (v : V 0) : NbrWeylDataVx (excRaw 0) v := by
  refine of_orbit tabsOK_D0 _ (fun u v h => nbrWeylDataVx_reflection tabsOK0 u h)
    (B := O.B0) (reps := [0, 1, 5, 9])
    (orbOK_all (w := 81) (q := 1) (by decide) fun j hj => ?_) (fun c hc => ?_) v
  · obtain rfl : j = 0 := by omega
    exact ch712526orb0
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact nbrWeylDataVx_zero 0
    · exact nbrWeylDataVx_of_lineK tabsOK_D0 ch712550n0_1 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D0 ch712550n0_5 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D0 ch712550n0_9 (by decide)

theorem nbrWeylDataVx1 (v : V 1) : NbrWeylDataVx (excRaw 1) v := by
  refine of_orbit tabsOK_D1 _ (fun u v h => nbrWeylDataVx_reflection tabsOK1 u h)
    (B := O.B1) (reps := [0, 1, 5, 9])
    (orbOK_all (w := 81) (q := 1) (by decide) fun j hj => ?_) (fun c hc => ?_) v
  · obtain rfl : j = 0 := by omega
    exact ch712526orb1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact nbrWeylDataVx_zero 1
    · exact nbrWeylDataVx_of_lineK tabsOK_D1 ch712550n1_1 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D1 ch712550n1_5 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D1 ch712550n1_9 (by decide)

theorem nbrWeylDataVx2 (v : V 2) : NbrWeylDataVx (excRaw 2) v := by
  refine of_orbit tabsOK_D2 _ (fun u v h => nbrWeylDataVx_reflection tabsOK2 u h)
    (B := O.B2) (reps := [0, 1, 2, 3, 4, 8, 13, 27])
    (orbOK_all (w := 729) (q := 1) (by decide) fun j hj => ?_) (fun c hc => ?_) v
  · obtain rfl : j = 0 := by omega
    exact ch712526orb2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact nbrWeylDataVx_zero 2
    · exact nbrWeylDataVx_of_lineK tabsOK_D2 ch712550n2_1 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D2 ch712550n2_2 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D2 ch712550n2_3 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D2 ch712550n2_4 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D2 ch712550n2_8 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D2 ch712550n2_13 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D2 ch712550n2_27 (by decide)

theorem nbrWeylDataVx3 (v : V 3) : NbrWeylDataVx (excRaw 3) v := by
  refine of_orbit tabsOK_D3 _ (fun u v h => nbrWeylDataVx_reflection tabsOK3 u h)
    (B := O.B3) (reps := [0, 1, 4, 11])
    (orbOK_all (w := 243) (q := 1) (by decide) fun j hj => ?_) (fun c hc => ?_) v
  · obtain rfl : j = 0 := by omega
    exact ch712526orb3
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact nbrWeylDataVx_zero 3
    · exact nbrWeylDataVx_of_lineK tabsOK_D3 ch712550n3_1 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D3 ch712550n3_4 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D3 ch712550n3_11 (by decide)

theorem nbrWeylDataVx4 (v : V 4) : NbrWeylDataVx (excRaw 4) v := by
  refine of_orbit tabsOK_D4 _ (fun u v h => nbrWeylDataVx_reflection tabsOK4 u h)
    (B := O.B4) (reps := [0, 1, 4, 11, 14, 416])
    (orbOK_all (w := 729) (q := 3) (by decide) fun j hj => ?_) (fun c hc => ?_) v
  · match j, hj with
    | 0, _ => exact ch712526orb4_0
    | 1, _ => exact ch712526orb4_1
    | 2, _ => exact ch712526orb4_2
    | _ + 3, h => exact absurd h (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact nbrWeylDataVx_zero 4
    · exact nbrWeylDataVx_of_lineK tabsOK_D4 ch712550n4_1 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D4 ch712550n4_4 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D4 ch712550n4_11 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D4 ch712550n4_14 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D4 ch712550n4_416 (by decide)

theorem nbrWeylDataVx5 (v : V 5) : NbrWeylDataVx (excRaw 5) v := by
  refine of_orbit tabsOK_D5 _ (fun u v h => nbrWeylDataVx_reflection tabsOK5 u h)
    (B := O.B5) (reps := [0, 1, 4, 11, 14])
    (orbOK_all (w := 729) (q := 9) (by decide) fun j hj => ?_) (fun c hc => ?_) v
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
    · exact nbrWeylDataVx_zero 5
    · exact nbrWeylDataVx_of_lineK tabsOK_D5 ch712550n5_1 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D5 ch712550n5_4 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D5 ch712550n5_11 (by decide)
    · exact nbrWeylDataVx_of_lineK tabsOK_D5 ch712550n5_14 (by decide)

theorem nbrWeylData_all (m : Fin 6) : NbrWeylData (excRaw m) := by
  rw [nbrWeylData_iff_forall]
  fin_cases m
  · exact nbrWeylDataVx0
  · exact nbrWeylDataVx1
  · exact nbrWeylDataVx2
  · exact nbrWeylDataVx3
  · exact nbrWeylDataVx4
  · exact nbrWeylDataVx5

end CFSG.ExcExtK

end

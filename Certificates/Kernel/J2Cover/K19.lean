
module

public import Certificates.Kernel.J2Cover.K19A
public import Certificates.Kernel.J2Cover.K19E
public import Certificates.Kernel.J2Cover.K19R
public import Certificates.Kernel.J2Cover.K19O
public import Certificates.Kernel.J2Cover.EncTab
public import CFSG.Certificates.Kernel.J2EnumSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover CFSG.KC.J2Enum
open CFSG.KC.Misc.ArrEnum
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Th.Native (Table ap idT)
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem sumF_congr {f g : Nat → Nat} : ∀ m, (∀ a < m, f a = g a) → sumF m f = sumF m g
  | 0, _ => rfl
  | m + 1, h => by
    have e : ∀ r : Nat → Nat, sumF (m + 1) r = sumF m r + r m := fun r => by
      change strictN (sumF m r) (fun s' => Nat.add s' (r m)) = _
      rw [strictN_eq']
      rfl
    rw [e, e, sumF_congr m fun a ha => h a (by omega), h m (by omega)]

theorem kL0 : Nat.beq (rcnt (PA.LR 0)) 315 = true := by quickRfl

theorem sum0 : sumF (rcnt (PA.LR 0)) (blkCnt 315 9 PA.LR PA.TR PA.BP (pidn 315 9) (PA.S 0) TA) =
    sumF 315 (lget E0) := by
  rw [Nat.eq_of_beq_eq_true kL0]
  exact sumF_congr 315 fun a ha => Nat.eq_of_beq_eq_true
    (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) E0B.all a ha)

theorem sumU : sumF (rcnt (PA.LR 0)) (blkCntU 315 9 PA.LR PA.TR PA.BP OU) = sumF 315 (lget EU) := by
  rw [Nat.eq_of_beq_eq_true kL0]
  exact sumF_congr 315 fun a ha => Nat.eq_of_beq_eq_true
    (CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) EUB.all a ha)

theorem k0 : Nat.beq (fld20 (sumF 315 (lget E0)) 0) 2835 = true := by quickRfl
theorem k1 : Nat.beq (fld20 (sumF 315 (lget E0)) 1) 17360 = true := by quickRfl
theorem k2 : Nat.beq (fld20 (sumF 315 (lget E0)) 2) 480 = true := by quickRfl
theorem k3 : Nat.beq (fld20 (sumF 315 (lget E0)) 3) 0 = true := by quickRfl
theorem kU : Nat.beq (sumF 315 (lget EU)) 1800 = true := by quickRfl

theorem chainPA : ChainOK3 315 9 7 2 PA.BP 20 16 PA.S PA.SI PA.LR PA.TR PA.TRI autD autStrong
    autBase :=
  ⟨binds, PA.head, PA.hl, by norm_num, PA.hs, perm⟩

theorem k20 : rcnt (PA.LR 0) * rcnt (PA.LR 1) * rcnt (PA.LR 2) < 2 ^ 20 := by
  have h0 : Nat.beq (rcnt (PA.LR 0)) 315 = true := by quickRfl
  have h1 : Nat.beq (rcnt (PA.LR 1)) 160 = true := by quickRfl
  have h2 : Nat.beq (rcnt (PA.LR 2)) 12 = true := by quickRfl
  rw [Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  norm_num

theorem len2 : (orderTablesOf (idT 315) 2).length = 2835 := by
  unfold orderTablesOf autTables
  rw [(enumCnt_sound chainPA k20 ⟨cPA 0 (by omega), by quickRfl⟩ ⟨cTA, by quickRfl⟩).1, sum0,
    Nat.eq_of_beq_eq_true k0]

theorem len3 : (orderTablesOf (idT 315) 3).length = 17360 := by
  unfold orderTablesOf autTables
  rw [(enumCnt_sound chainPA k20 ⟨cPA 0 (by omega), by quickRfl⟩ ⟨cTA, by quickRfl⟩).2.1, sum0,
    Nat.eq_of_beq_eq_true k1]

theorem cnt2 : (orderTablesOf (idT 315) 3).countP
    (pairTest 315 7 12 2 3 (arrTable 315 (unpack 315 9 (PA.S 0)))) = 480 := by
  unfold orderTablesOf autTables
  rw [(enumCnt_sound chainPA k20 ⟨cPA 0 (by omega), by quickRfl⟩ ⟨cTA, by quickRfl⟩).2.2.1, sum0,
    Nat.eq_of_beq_eq_true k2]

theorem cnt3 : (orderTablesOf (idT 315) 3).countP
    (pairTest 315 7 12 2 3 (arrTable 315 (unpack 315 9 TA))) = 0 := by
  unfold orderTablesOf autTables
  rw [(enumCnt_sound chainPA k20 ⟨cPA 0 (by omega), by quickRfl⟩ ⟨cTA, by quickRfl⟩).2.2.2, sum0,
    Nat.eq_of_beq_eq_true k3]

theorem hU : tblU = arrTable 315 (unpack 315 9 OU) := by
  unfold tblU
  rw [hou]

theorem uNotP' : (!siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 OU) = true := by
  quickRfl

theorem uNotP : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 OU = false := by
  have h := uNotP'
  revert h
  cases siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 OU <;> simp

theorem lenU : (orderTablesOf tblU 2).length = 1800 := by
  unfold orderTablesOf autTables
  rw [hU, enumCntU_sound chainPA cOU (fun j hj => by interval_cases j <;> quickRfl) (by quickRfl)
    uNotP, sumU, Nat.eq_of_beq_eq_true kU]

theorem gA : RC.GP 0 = PA.S 0 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem gB : RC.GP 1 = PA.S 1 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem gAi : RC.GIP 0 = PA.SI 0 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem gBi : RC.GIP 1 = PA.SI 1 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem vA : RV.GP 0 = PA.S 0 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem vB : RV.GP 1 = PA.S 1 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem vAi : RV.GIP 0 = PA.SI 0 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem vBi : RV.GIP 1 = PA.SI 1 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem tA_eq : tblA = arrTable 315 (unpack 315 9 (PA.S 0)) := by unfold tblA; rw [ha]
theorem tB_eq : tblB = arrTable 315 (unpack 315 9 (PA.S 1)) := by unfold tblB; rw [hb']
theorem tAi_eq : tblAInv = arrTable 315 (unpack 315 9 (PA.SI 0)) := by
  unfold tblAInv
  rw [ha, (invEqK_sound (allN_spec perm 0 (by omega))).1]
theorem tBi_eq : tblBInv = arrTable 315 (unpack 315 9 (PA.SI 1)) := by
  unfold tblBInv
  rw [hb', (invEqK_sound (allN_spec perm 1 (by omega))).1]

theorem gensP (GP GIP : Nat → Nat) (h0 : GP 0 = PA.S 0) (h1 : GP 1 = PA.S 1) (i0 : GIP 0 = PA.SI 0)
    (i1 : GIP 1 = PA.SI 1) :
    (#[tblA, tblB] : Array Table).size = 2 ∧ (#[tblAInv, tblBInv] : Array Table).size = 2 ∧
      ∀ l < 2, (#[tblA, tblB] : Array Table)[l]! = arrTable 315 (unpack 315 9 (GP l)) ∧
        (#[tblAInv, tblBInv] : Array Table)[l]! = arrTable 315 (unpack 315 9 (GIP l)) := by
  refine ⟨rfl, rfl, fun l hl => ?_⟩
  interval_cases l
  · refine ⟨?_, ?_⟩
    · rw [h0, ← tA_eq]
      rfl
    · rw [i0, ← tAi_eq]
      rfl
  · refine ⟨?_, ?_⟩
    · rw [h1, ← tB_eq]
      rfl
    · rw [i1, ← tBi_eq]
      rfl

theorem gcP (GP GIP : Nat → Nat) (h0 : GP 0 = PA.S 0) (h1 : GP 1 = PA.S 1) (i0 : GIP 0 = PA.SI 0)
    (i1 : GIP 1 = PA.SI 1) : ∀ l < 2, CnN 315 9 (GP l) ∧ CnN 315 9 (GIP l) := by
  intro l hl
  interval_cases l
  · rw [h0, i0]
    exact ⟨by quickRfl, by quickRfl⟩
  · rw [h1, i1]
    exact ⟨by quickRfl, by quickRfl⟩

theorem rcAll (j : Nat) (hj : j < RC.N) : repK 315 9 RC.GP RC.GIP 2 RC.CS RC.OFF RC.CI RC.E RC.P
    RC.L RC.K RC.S RC.SI RC.N 4000 j = true :=
  CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) RCBJ2.all j (by
    have e : RC.N = 2835 := rfl
    rw [e] at hj
    exact hj)

theorem rvAll (j : Nat) (hj : j < RV.N) : repK 315 9 RV.GP RV.GIP 2 RV.CS RV.OFF RV.CI RV.E RV.P
    RV.L RV.K RV.S RV.SI RV.N 4000 j = true :=
  CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) RVB.all j (by
    have e : RV.N = 1800 := rfl
    rw [e] at hj
    exact hj)

theorem eRC0 : RC.E (lget RC.OFF 0) = PA.S 0 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem eRC1 : RC.E (lget RC.OFF 1) = TA := Nat.eq_of_beq_eq_true (by quickRfl)
theorem eRV0 : RV.E (lget RV.OFF 0) = OU := Nat.eq_of_beq_eq_true (by quickRfl)

theorem repsC : [tblA, tblTwoA] = (List.range RC.CS.length).map fun i =>
    arrTable 315 (unpack 315 9 (RC.E (lget RC.OFF i))) := by
  have hl : RC.CS.length = 2 := rfl
  have hr : List.range 2 = [0, 1] := rfl
  rw [hl, hr]
  simp only [List.map_cons, List.map_nil]
  rw [eRC0, eRC1, ← tA_eq]
  unfold tblTwoA
  rw [hta]

theorem repsV : [tblU] = (List.range RV.CS.length).map fun i =>
    arrTable 315 (unpack 315 9 (RV.E (lget RV.OFF i))) := by
  have hl : RV.CS.length = 1 := rfl
  have hr : List.range 1 = [0] := rfl
  rw [hl, hr]
  simp only [List.map_cons, List.map_nil]
  rw [eRV0, hU]

theorem ordRep (i : Nat) (hi : i < RC.CS.length) :
    canonK 315 9 (mask 9) (315 * 9) (RC.E (lget RC.OFF i)) = true ∧
      siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 (RC.E (lget RC.OFF i)) =
        true ∧ ordTest 315 2 (arrTable 315 (unpack 315 9 (RC.E (lget RC.OFF i)))) = true := by
  have hl : RC.CS.length = 2 := rfl
  rw [hl] at hi
  interval_cases i
  · rw [eRC0]
    exact ⟨cPA 0 (by omega), by quickRfl, by rw [ordT_ofE (by norm_num) (cPA 0 (by omega))]; quickRfl⟩
  · rw [eRC1]
    exact ⟨cTA, by quickRfl, by rw [ordT_ofE (by norm_num) cTA]; quickRfl⟩

theorem gpC (l : Nat) (hl : l < 2) : RC.GP l = PA.S l ∧ RC.GIP l = PA.SI l := by
  interval_cases l
  · exact ⟨gA, gAi⟩
  · exact ⟨gB, gBi⟩

theorem lenN : (filterProducts 315 (ordTest 315 2) (chainTables 315 autStrong autBase) (idT 315)
    []).length = RC.N := by
  have : RC.N = 2835 := rfl
  have h := len2
  unfold orderTablesOf autTables at h
  rw [h, this]

theorem classOKC : classOK 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf (idT 315) 2) 4000 =
    true :=
  (classes_sound (g := 2) (cap := 4000) (r := 7) (s := 12) (my := 3) chainPA (le_refl 2)
    (gensP RC.GP RC.GIP gA gB gAi gBi) gpC (le_refl 2) (by quickRfl) rcAll ordRep lenN).1

theorem totalC : classTotal 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf (idT 315) 2)
    (orderTablesOf (idT 315) 3) 4000 7 12 2 3 = 1209600 := by
  unfold orderTablesOf autTables
  rw [(classes_sound (g := 2) (cap := 4000) (r := 7) (s := 12) (my := 3) chainPA (le_refl 2)
    (gensP RC.GP RC.GIP gA gB gAi gBi) gpC (le_refl 2) (by quickRfl) rcAll ordRep lenN).2]
  have hl : RC.CS.length = 2 := rfl
  have c0 : lget RC.CS 0 = 2520 := rfl
  have c1 : lget RC.CS 1 = 315 := rfl
  have hr : List.range 2 = [0, 1] := rfl
  rw [hl, hr]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have h2 := cnt2
  have h3 := cnt3
  unfold orderTablesOf autTables at h2 h3
  rw [c0, c1, eRC0, eRC1, h2, h3]
  norm_num

theorem repsOKC : repsOK 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf (idT 315) 2)
    [tblA, tblTwoA] 4000 = true :=
  repsOK_sound (gensP RC.GP RC.GIP gA gB gAi gBi) (gcP RC.GP RC.GIP gA gB gAi gBi) repsC
    (by quickRfl) (by quickRfl) (by have : RC.N = 2835 := rfl; rw [len2, this]) rcAll

theorem sizesC : repSizes 315 #[tblA, tblB] #[tblAInv, tblBInv] [tblA, tblTwoA] 4000 = [2520, 315] :=
  (repSizes_sound (gensP RC.GP RC.GIP gA gB gAi gBi) (gcP RC.GP RC.GIP gA gB gAi gBi) repsC
    (by quickRfl) (by quickRfl) rcAll).trans rfl

theorem repsOKU : repsOK 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf tblU 2) [tblU] 4000 =
    true :=
  repsOK_sound (gensP RV.GP RV.GIP vA vB vAi vBi) (gcP RV.GP RV.GIP vA vB vAi vBi) repsV
    (by quickRfl) (by quickRfl) (by have : RV.N = 1800 := rfl; rw [lenU, this]) rvAll

theorem sizesU : repSizes 315 #[tblA, tblB] #[tblAInv, tblBInv] [tblU] 4000 = [1800] :=
  (repSizes_sound (gensP RV.GP RV.GIP vA vB vAi vBi) (gcP RV.GP RV.GIP vA vB vAi vBi) repsV
    (by quickRfl) (by quickRfl) rvAll).trans rfl

theorem pairAB : pairTest 315 7 12 2 3 tblA tblB = true := by
  have c0 := cPA 0 (by omega)
  have c1 := cPA 1 (by omega)
  have hc : ∀ Z ∈ [PA.S 0, PA.S 1, PA.S 0, PA.S 1, PA.S 1], CnN 315 9 Z := by
    intro Z hZ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hZ
    rcases hZ with rfl | rfl | rfl | rfl | rfl <;> assumption
  have h1 := CFSG.KC.J2Cover.ordW_unpack (n := 315) (w := 9) (m := 7) (ws := [PA.S 0, PA.S 1])
    (by norm_num) (canon2 c0 c1)
  have h2 := CFSG.KC.J2Cover.ordW_unpack (n := 315) (w := 9) (m := 12)
    (ws := [PA.S 0, PA.S 1, PA.S 0, PA.S 1, PA.S 1]) (by norm_num) hc
  rw [tA_eq, tB_eq]
  unfold pairTest
  change ordW 315 ([PA.S 0, PA.S 1].map fun X => arrTable 315 (unpack 315 9 X)) 7 &&
    ordW 315 ([PA.S 0, PA.S 1, PA.S 0, PA.S 1, PA.S 1].map fun X => arrTable 315 (unpack 315 9 X))
      12 = true
  rw [h1, h2]
  quickRfl

theorem ordA : ordTest 315 2 tblA = true := by
  rw [tA_eq, ordT_ofE (by norm_num) (cPA 0 (by omega))]
  quickRfl

theorem ordB' : ordTest 315 3 tblB = true := by
  rw [tB_eq, ordT_ofE (by norm_num) (cPA 1 (by omega))]
  quickRfl

theorem facts10019 :
    (rawChainOK 315 (autStrong.extract 0 2) autStrong autBase autWords 4 = true ∧
      rawOrbitSizes 315 autStrong autBase = [315, 160, 12])
    ∧ (allLt 315 (fun i => ap (CFSG.Sporadic.J2.Native.orbitData ()).alpha i ==
        (autStrong[0]!)[i]! && ap (CFSG.Sporadic.J2.Native.orbitData ()).beta i ==
          (autStrong[1]!)[i]!) = true)
    ∧ (ordTest 315 2 tblA = true ∧ ordTest 315 3 tblB = true ∧
      pairTest 315 7 12 2 3 tblA tblB = true ∧
      (orderTablesOf (idT 315) 2).length = 2835 ∧ (orderTablesOf (idT 315) 3).length = 17360 ∧
      classOK 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf (idT 315) 2) 4000 = true ∧
      classTotal 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf (idT 315) 2)
        (orderTablesOf (idT 315) 3) 4000 7 12 2 3 = 1209600)
    ∧ (inP outerArr = false ∧ inP (compA 315 outerArr (compA 315 autStrong[0]! outerArr)) = true ∧
      inP (compA 315 outerArr (compA 315 autStrong[1]! outerArr)) = true)
    ∧ (inP twoAArr = true ∧
      repsOK 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf (idT 315) 2) [tblA, tblTwoA]
        4000 = true ∧
      repSizes 315 #[tblA, tblB] #[tblAInv, tblBInv] [tblA, tblTwoA] 4000 = [2520, 315] ∧
      repsOK 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf tblU 2) [tblU] 4000 = true ∧
      repSizes 315 #[tblA, tblB] #[tblAInv, tblBInv] [tblU] 4000 = [1800])
    ∧ (rawChainOK 315 (cent2BStrong.extract 0 2) cent2BStrong cent2BBase cent2BWords 4 = true ∧
      rawOrbitSizes 315 cent2BStrong cent2BBase = [60, 4] ∧
      inP cent2BStrong[0]! = true ∧ inP cent2BStrong[1]! = true ∧
      commA cent2BStrong[0]! autStrong[0]! = true ∧ commA cent2BStrong[1]! autStrong[0]! = true ∧
      oddWitnessOK 315 15
        (filterProducts 315 allTrue (chainTables 315 cent2BStrong cent2BBase) (idT 315) []) =
        true)
    ∧ (rawChainOK 315 (cent2AStrong.extract 0 2) cent2AStrong cent2ABase cent2AWords 4 = true ∧
      rawOrbitSizes 315 cent2AStrong cent2ABase = [160, 4, 3] ∧
      inP cent2AStrong[0]! = true ∧ inP cent2AStrong[1]! = true ∧
      commA cent2AStrong[0]! twoAArr = true ∧ commA cent2AStrong[1]! twoAArr = true ∧
      oddWitnessOK 315 15
        (filterProducts 315 allTrue (chainTables 315 cent2AStrong cent2ABase) (idT 315) []) =
        true)
    ∧ (rawChainOK 315 (centOuterStrong.extract 0 2) centOuterStrong centOuterBase centOuterWords 4 =
        true ∧
      rawOrbitSizes 315 centOuterStrong centOuterBase = [42, 8] ∧
      inP centOuterStrong[0]! = true ∧ inP centOuterStrong[1]! = true ∧
      commA centOuterStrong[0]! outerArr = true ∧ commA centOuterStrong[1]! outerArr = true ∧
      oddWitnessOK 315 21
        (filterProducts 315 allTrue (chainTables 315 centOuterStrong centOuterBase) (idT 315) []) =
        true)
    ∧ (rawChainOK 315 (sylowStrong.extract 0 3) sylowStrong sylowBase sylowWords 4 = true ∧
      rawOrbitSizes 315 sylowStrong sylowBase = [64, 4] ∧
      inP (compA 315 sylowStrong[0]! outerArr) = true ∧
      inP (compA 315 sylowStrong[1]! outerArr) = true ∧
      inP (compA 315 sylowStrong[2]! outerArr) = true) :=
  ⟨autChain, orbC, ⟨ordA, ordB', pairAB, len2, len3, classOKC, totalC⟩, outerC,
    ⟨twoA_in, repsOKC, sizesC, repsOKU, sizesU⟩,
    ⟨c2B_chain.1, c2B_chain.2, c2B_gens.1, c2B_gens.2.1, c2B_gens.2.2.1, c2B_gens.2.2.2, oddC2B⟩,
    ⟨c2A_chain.1, c2A_chain.2, c2A_gens.1, c2A_gens.2.1, c2A_gens.2.2.1, c2A_gens.2.2.2, oddC2A⟩,
    ⟨cOu_chain.1, cOu_chain.2, cOu_gens.1, cOu_gens.2.1, cOu_gens.2.2.1, cOu_gens.2.2.2, oddCOU⟩,
    sylowC⟩

end CertificateChecks.KernelJ2Cover

end

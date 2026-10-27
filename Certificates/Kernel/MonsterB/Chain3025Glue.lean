module

public import Certificates.Kernel.MonsterB.Chain3025Bind
public import CFSG.Certificates.Kernel.SporSch.MatSchSound
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.Chain3025

open CFSG.KS.Raw CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.KS.MatSch CFSG.KS.Co2Stab CFSG.Certificates.ChainArrays
  CFSG.KS.Raw.Orb

attribute [local irreducible] Native.chainStrong Native.pairPerms Native.chainOrbits

theorem unpack_get' {n w X k : Nat} (hk : k < n) :
    (unpack n w X)[k]! = pg w (CFSG.KS.mask w) X k := by
  rw [unpack, getElem!_pos _ _ (by simpa using hk), Array.getElem_ofFn]

theorem strong_size : (chainStrong ()).size = 20 := by
  unfold chainStrong
  exact Array.size_ofFn

theorem strong_get {j : Nat} (hj : j < 20) : (chainStrong ())[j]! = unpack 2300 12 (Co2M.S j) := by
  unfold chainStrong
  rw [getElem!_pos _ _ (by simpa using hj), Array.getElem_ofFn]
  change hexTable 3 2300 (2300 * j) chainStrongHex = _
  rw [KernelMonB.Co2S.eq, CFSG.KC.Misc.HexFlat.hexTable_sound KernelMonB.Co2S.all j hj,
    Nat.eq_of_beq_eq_true (Orb.allN_iff.1 strong_ok j hj)]

theorem binds : Binds 2300 12 Co2M.S 20 10 Co2M.BP (chainStrong ()) chainBase :=
  ⟨by norm_num, by norm_num, by norm_num, strong_size, fun j hj => strong_get hj, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (Orb.allN_iff.1 base_ok t ht)⟩

theorem lanes22 : (11908528498073666995947969347157480251659827695481117700305989184378417062648132460131015248306064568667840854116287251142124832390176047105 : Nat) =
    CFSG.RankThree.Native.F2.lanes 22 := by decide

theorem idM22 : (24973991379659707467621756579723706896969316949376236904045051527405272766968242940994766581490570014503808294292943339053779062356439532262391809 : Nat) =
    CFSG.RankThree.Native.F2.idM 22 := by decide

theorem rawChainOK_co2 : rawChainOK 2300 ((chainStrong ()).extract 0 2) (chainStrong ()) chainBase
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 20 co2Der) 8 = true :=
  rawChainMK_sound binds Co2M.head Co2M.tl Co2M.hst (by norm_num) (by norm_num) lanes22 idM22
    Co2M.vec Co2M.bind Co2M.tr Co2M.hs

theorem chainLevels_eq : chainLevels () = rawLevels 2300 (chainStrong ()) chainBase := rfl

theorem chainSteps_eq (i : Nat) : chainSteps i = rawSteps 2300 (chainStrong ()) chainBase i := rfl

theorem strongInv_eq : strongInv () = rawInvs 2300 (chainStrong ()) := rfl

theorem words_eq : chainWords () = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 20 co2Der := by
  decide +kernel

theorem pairPerms_size : (pairPerms ()).size = 2 := by
  unfold pairPerms
  exact Array.size_ofFn

theorem pairPerms_get {j : Nat} (hj : j < 2) : (pairPerms ())[j]! = (chainStrong ())[j]! := by
  rw [KernelMonB.pairPerms_getElem! hj, strong_get (by omega),
    Nat.eq_of_beq_eq_true (Orb.allN_iff.1 pair_ok j hj)]

theorem eqA_self (n : Nat) (t : Array Nat) : eqA n t t = true :=
  allLt_iff.2 fun _ _ => beq_self_eq_true _

theorem chainCheck_true : chainCheck 8 = true := by
  have hR := rawChainOK_co2
  unfold rawChainOK at hR
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hR
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, h3⟩, _⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hR
  have hO : ((chainStrong ()).extract 0 2).size = 2 := by simp [strong_size]
  rw [hO] at h5
  have hS := strong_size
  unfold chainCheck
  simp only [deg, chainLevels_eq, chainSteps_eq, strongInv_eq, Bool.and_eq_true, beq_iff_eq,
    and_assoc]
  refine ⟨pairPerms_size, hS, rfl, rfl, by rw [chainLevels_size]; rfl, ?_, h3, ?_, ?_, ?_, h6,
    h7, ?_, h9⟩
  · refine allLt_iff.2 fun j hj => ?_
    rw [pairPerms_get hj, ← rawInvs_get (by rw [hS]; omega)]
    exact allLt_spec h3 (by rw [hS]; omega)
  · rw [pairPerms_get (by omega)]
    exact eqA_self _ _
  · rw [pairPerms_get (by omega)]
    exact eqA_self _ _
  · rw [words_eq]
    exact h5
  · refine allLt_iff.2 fun i hi => ?_
    rw [Bool.and_eq_true, beq_iff_eq]
    refine ⟨allLt_spec h8 hi, ?_⟩
    rw [levels_cnt binds Co2M.head Co2M.tl hi]
    exact Nat.eq_of_beq_eq_true (Orb.allN_iff.1 sizes_ok i hi)

theorem hexTable_slice {w m N k₀ k : Nat} {s : String} (hk : k < m) (hN : k₀ + k < N) :
    (hexTable w m k₀ s)[k]! = (hexTable w N 0 s)[k₀ + k]! := by
  unfold hexTable
  rw [getElem!_pos _ _ (by simpa using hk), getElem!_pos _ _ (by simpa using hN),
    Array.getElem_ofFn, Array.getElem_ofFn, Nat.zero_add]

theorem orbs_size : (chainOrbits ()).size = 3 := by
  unfold chainOrbits
  rfl

theorem orbs_size' {t : Nat} (ht : t < 3) : ((chainOrbits ())[t]!).size = szT t := by
  unfold chainOrbits
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;>
    simp [hexTable, szT]

theorem orbs_get {t k : Nat} (ht : t < 3) (hk : k < szT t) :
    ((chainOrbits ())[t]!)[k]! = at12 (KernelMonB.Co2O.F 0) (offT t + k) := by
  have hfull : hexTable 3 2300 0 chainOrbitsHex = unpack 2300 12 (KernelMonB.Co2O.F 0) := by
    have h := CFSG.KC.Misc.HexFlat.hexTable_sound KernelMonB.Co2O.all 0 (by decide)
    rw [← KernelMonB.Co2O.eq] at h
    exact h
  have hlt := (lab_off ht hk).2
  have e : ((chainOrbits ())[t]!)[k]! = (hexTable 3 2300 0 chainOrbitsHex)[offT t + k]! := by
    unfold chainOrbits
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
    · have hk' : k < 1 := by simpa [szT] using hk
      exact hexTable_slice hk' (by omega)
    · have hk' : k < 891 := by simpa [szT] using hk
      exact hexTable_slice hk' (by omega)
    · have hk' : k < 1408 := by simpa [szT] using hk
      exact hexTable_slice hk' (by omega)
  rw [e, hfull, unpack_get' hlt]
  rfl

theorem stabIdx_get : ∀ j < 18, chainStabIdx[j]! = j + 2 := by decide

theorem stabIdx_size : chainStabIdx.size = 18 := rfl

theorem stabIdx_contains : ∀ j < 20, chainStabIdx.contains j = decide (2 ≤ j) := by
  intro j hj
  rw [Bool.eq_iff_iff, Array.contains_iff_mem, decide_eq_true_iff]
  simp only [chainStabIdx, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro h
    omega
  · intro h
    omega

theorem stabGens_size : (stabGens ()).size = 18 := by
  unfold stabGens
  simp [chainStabIdx]

theorem stabGens_get {j x : Nat} (hj : j < 18) (hx : x < 2300) :
    ((stabGens ())[j]!)[x]! = at12 (Co2M.S (j + 2)) x := by
  have e : (stabGens ())[j]! = (chainStrong ())[j + 2]! := by
    unfold stabGens
    rw [getElem!_pos _ _ (by simp [chainStabIdx]; omega), Array.getElem_map,
      ← getElem!_pos chainStabIdx j (by simp [chainStabIdx]; omega), stabIdx_get j hj]
  rw [e, strong_get (by omega), unpack_get' hx]
  rfl

theorem gens_lt {j x : Nat} (hj : j < 18) (hx : x < 2300) : at12 (Co2M.S (j + 2)) x < 2300 := by
  have hp := (CFSG.KS.Raw.Orb.head_facts Co2M.head).1
  have hj2 : j + 2 < 20 := by omega
  exact (permOK_facts (n := 2300) (w := 12) (Orb.allN_iff.1 hp (j + 2) hj2)).2.2 x hx |>.1

theorem strong_zero {j : Nat} (hj : j < 20) :
    ((chainStrong ())[j]!)[0]! = at12 (Co2M.S j) 0 := by
  rw [strong_get hj, unpack_get' (by norm_num)]
  rfl

theorem stabCheck_true : stabCheck () = true := by
  have F := stabF_of stab_ok
  have hO := orbitsOK_of (gens := stabGens ()) (orbs := chainOrbits ()) F stabGens_size
    (fun j hj x hx => stabGens_get hj hx) (fun j hj x hx => gens_lt hj hx) orbs_size
    (fun t ht => orbs_size' ht) (fun t ht k hk => orbs_get ht hk) (sizes := chainOrbitSizes)
    rfl (fun t ht => by
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl <;> rfl)
  unfold stabCheck
  simp only [deg, Bool.and_eq_true, beq_iff_eq, and_assoc]
  refine ⟨rfl, ?_, ?_, ?_, ?_, hO⟩
  · rw [orbs_get (by omega) (by simp [szT])]
    exact first_ok
  · rw [strong_size]
    refine allLt_iff.2 fun k hk => ?_
    rw [stabIdx_size] at hk
    rw [stabIdx_get k hk, decide_eq_true_iff]
    omega
  · refine allLt_iff.2 fun k hk => ?_
    rw [stabIdx_size] at hk
    rw [stabIdx_get k (by omega), stabIdx_get (k + 1) (by omega), decide_eq_true_iff]
    omega
  · rw [strong_size]
    refine allLt_iff.2 fun j hj => ?_
    rw [strong_zero hj, stabIdx_contains j hj]
    have e := Orb.allN_iff.1 fix_ok j hj
    by_cases hz : at12 (Co2M.S j) 0 = 0
    · rw [hz] at e ⊢
      have e' : Nat.ble 2 j = true := e
      simp [Nat.ble_eq.mp e']
    · have e1 : Nat.beq (at12 (Co2M.S j) 0) 0 = false := by
        rw [Bool.eq_false_iff]
        exact fun e2 => hz (Nat.eq_of_beq_eq_true e2)
      rw [e1] at e
      have e' : Nat.ble 2 j = false := by simpa using e
      have : ¬ 2 ≤ j := fun h => by rw [Nat.ble_eq_true_of_le h] at e'; exact Bool.noConfusion e'
      simp [hz, this]

theorem co2ChainCertOK_true : co2ChainCertOK () = true := by
  unfold co2ChainCertOK
  rw [chainCheck_true, stabCheck_true]
  rfl

end CertificateChecks.Chain3025

end

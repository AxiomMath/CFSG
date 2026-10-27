module

public import Certificates.Kernel.Sporadic.OddCore.HNAK
public import Certificates.Kernel.Sporadic.OddCore.HNAG0
public import CFSG.Certificates.Kernel.Spor.HNAOrbSound
public import CFSG.Certificates.Kernel.LocalQTNatsXSound
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.BfsPinSliceSound
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HNAS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KS.HNA CFSG.KC.LQT.NP
open CFSG.ComponentClassification.RankTwoSporadic.HN CFSG.Sporadic.HNOddCore.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CertificateChecks.KernelSpor

theorem hsz : szOK 1100 11 = true := by
  have k := kHead
  simp only [Bool.and_eq_true] at k
  exact k.1.1.1.1

theorem parse_eq {s : String} {cs : List Char} {L : List Nat} (hs : s = String.ofList cs)
    (h : natsOK cs L = true) : parseNatsHN s = L.toArray := by
  unfold parseNatsHN
  rw [hs]
  exact congrArg List.toArray (natsX_sound cs L h)

theorem prog_eq : decodePairsO hnAProgStr = (List.range 2875).map fun t => (pA t, pB t) := by
  unfold decodePairsO
  rw [parse_eq HNAT.Prog.eq pProg, List.toList_toArray, listUp_eq,
    show (5750 : Nat) = 2 * 2875 from rfl, pairsOf_map_range]
  rfl

theorem pool_eq : decodePairsO hnAPoolStr =
    (List.range 48).map fun f => (HNAT.QN (2 * f), HNAT.QN (2 * f + 1)) := by
  unfold decodePairsO
  rw [parse_eq HNAT.Pool.eq pPool, List.toList_toArray, listUp_eq,
    show (96 : Nat) = 2 * 48 from rfl, pairsOf_map_range]

theorem wits_eq : decodeAO hnAWitStr = ((List.range 1024).map (awOf HNAW.C HNAW.F HNAW.M)).toArray := by
  unfold decodeAO
  rw [parse_eq HNAT.Wit.eq pWit, List.size_toArray, List.toList_toArray,
    witsOf_of_wbRun _ _ 0 (Nat.le_refl _) bWit, Nat.sub_zero, ← List.range_eq_range']

theorem pp_hsg {s : Nat} (hs : s < 12) : PP 1100 11 (HSG s) :=
  PP_of_permOK hsz (allN_spec HN2092.gP s hs)

theorem base_get {s : Nat} (hs : s < 12) :
    HNAR.X s = HSG s ∧ HNAR.X (12 + s) = pinvS 1100 11 (mask 11) (HSG s) := by
  have h := allN_spec kBase s hs
  simp only [bAnd_eq', Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, h.2⟩

theorem steps : ∀ t < 2875, stepK 1100 11 24 HNAR.X pA pB t = true :=
  of_slices' (L := 25) (K := 115) (by decide) fun s hs => stK.all s hs

theorem regs_facts : (regsA 1100 om0Gens (decodePairsO hnAProgStr)).size = 2899 ∧
    ∀ i < 2899, (regsA 1100 om0Gens (decodePairsO hnAProgStr))[i]! = unpack 1100 11 (HNAR.X i) ∧
      PP 1100 11 (HNAR.X i) := by
  obtain ⟨hgs, hg⟩ := HNAG0.g_get
  have h0 : (om0Gens ++ om0Gens.map (invCand 1100)).size = 24 + 0 := by
    rw [Array.size_append, Array.size_map, hgs]
  have hR0 : ∀ i < 24 + 0, (om0Gens ++ om0Gens.map (invCand 1100))[i]! =
      unpack 1100 11 (HNAR.X i) ∧ PP 1100 11 (HNAR.X i) := by
    intro i hi
    by_cases hlt : i < 12
    · rw [getElem!_pos _ i (by rw [h0]; omega), Array.getElem_append_left (by rw [hgs]; exact hlt),
        ← getElem!_pos om0Gens i (by rw [hgs]; exact hlt), hg i hlt, (base_get hlt).1]
      exact ⟨rfl, pp_hsg hlt⟩
    · obtain ⟨s, rfl⟩ : ∃ s, i = 12 + s := ⟨i - 12, by omega⟩
      have hs : s < 12 := by omega
      have e2 : 12 + s - om0Gens.size = s := by rw [hgs]; omega
      rw [getElem!_pos _ (12 + s) (by rw [h0]; omega),
        Array.getElem_append_right (by rw [hgs]; omega), Array.getElem_map]
      simp only [e2]
      rw [← getElem!_pos om0Gens s (by rw [hgs]; exact hs), hg s hs, invCand_PP (pp_hsg hs),
        (base_get hs).2]
      exact ⟨rfl, (pp_hsg hs).inv⟩
  have h := regsFrom_unpack (n := 1100) (w := 11) (m := 24) (X := HNAR.X) (A := pA) (B := pB)
    2875 0 _ h0 hR0 fun t ht => by rw [Nat.zero_add]; exact steps t ht
  unfold regsA
  rw [prog_eq, List.range_eq_range']
  exact ⟨h.1, fun i hi => h.2 i hi⟩

@[reducible, expose] def R : Array (Array Nat) := regsA 1100 om0Gens (decodePairsO hnAProgStr)

@[reducible, expose] def gs : Array (Array Nat) := (hnAPregs.map fun i => R[i]!).toArray

theorem reg_get {i : Nat} (hi : i < 2899) : R[i]! = unpack 1100 11 (HNAR.X i) ∧
    PP 1100 11 (HNAR.X i) := regs_facts.2 i hi

theorem gs_size : gs.size = 5 := rfl

theorem gens_get : ∀ k < 5, gs[k]! = unpack 1100 11 (HNAE.G k) ∧ PP 1100 11 (HNAE.G k) := by
  have k := kGens
  simp only [bAnd_eq', Bool.and_eq_true, Nat.beq_eq] at k
  obtain ⟨k0, k1, k2, k3, k4⟩ := k
  intro j hj
  interval_cases j
  · rw [k0]; exact reg_get (by decide)
  · rw [k1]; exact reg_get (by decide)
  · rw [k2]; exact reg_get (by decide)
  · rw [k3]; exact reg_get (by decide)
  · rw [k4]; exact reg_get (by decide)

theorem gens_perm : ∀ k < 5,
    permOK 1100 11 (mask 11) (1100 * 11) (HNAE.G k) (pinvS 1100 11 (mask 11) (HNAE.G k)) = true :=
  fun k hk => CFSG.KS.PinvS.permOK_pinvS (gens_get k hk).2.1 (gens_get k hk).2.2

theorem hk : bfsK 1100 11 5 HNAE.G 1024 HNAE.T HNAE.E HNAE.S = true := by
  have k := kHead
  simp only [Bool.and_eq_true] at k
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := k
  exact bfsK_of_slices (L := 32) (K := 32) (C := HNAE.C) rfl (by decide) h1 h2 csK.all h3 kDist
    (Nat.eq_of_beq_eq_true h4) (Nat.eq_of_beq_eq_true h5) rsK.all

theorem ps_lt : ∀ p ∈ psO, p < 1100 := by decide

theorem pts_eq : (enumBfs 1100 gs psO (2 * 1024)).pts =
    Array.ofFn (n := 1024) fun i => unpack 1100 11 (HNAE.T i.val) :=
  enumBfs_pts_base gs_size (fun k hk => (gens_get k hk).1) hk ps_lt keys (by decide)

theorem enum_ok : enumOK 1100 gs psO (enumBfs 1100 gs psO (2 * 1024)) = true :=
  enumOK_of_bfsK_base gs_size (fun k hk => (gens_get k hk).1) gens_perm hk ps_lt keys (by decide)

theorem pt_get {i : Nat} (hi : i < 1024) :
    (enumBfs 1100 gs psO (2 * 1024)).pts[i]! = unpack 1100 11 (HNAE.T i) := by
  rw [pts_eq, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem pp_pts : ∀ i < 1024, PP 1100 11 (HNAE.T i) := PP_pts hk gens_perm

@[reducible, expose] def pool : Array (Nat × Nat) := (decodePairsO hnAPoolStr).toArray

@[reducible, expose] def cms : Array (Array Nat) :=
  pool.map fun gh => commutatorA 1100 R[gh.1]! R[gh.2]!

theorem pool_get {f : Nat} (hf : f < 48) : pool[f]! = (HNAT.QN (2 * f), HNAT.QN (2 * f + 1)) := by
  unfold pool
  rw [pool_eq, getElem!_pos _ f (by simpa using hf)]
  simp

theorem pool_size : pool.size = 48 := by
  unfold pool
  rw [pool_eq]
  simp

theorem pool_lt {f : Nat} (hf : f < 48) : HNAT.QN (2 * f) < 2899 ∧ HNAT.QN (2 * f + 1) < 2899 ∧
    HNAC.C f = commP 1100 11 (HNAR.X (HNAT.QN (2 * f))) (HNAR.X (HNAT.QN (2 * f + 1))) := by
  have h := allN_spec kPool f hf
  unfold poolK at h
  simp only [bAnd_eq', Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem cms_size : cms.size = 48 := by
  unfold cms
  rw [Array.size_map, pool_size]

theorem cms_get : ∀ f < 48, cms[f]! = unpack 1100 11 (HNAC.C f) ∧ PP 1100 11 (HNAC.C f) := by
  intro f hf
  obtain ⟨h1, h2, h3⟩ := pool_lt hf
  have ha := reg_get h1
  have hb := reg_get h2
  unfold cms
  rw [getElem!_pos _ f (by rw [Array.size_map, pool_size]; exact hf), Array.getElem_map,
    ← getElem!_pos pool f (by rw [pool_size]; exact hf), pool_get hf]
  dsimp only
  rw [ha.1, hb.1, h3]
  exact commutatorA_unpack ha.2 hb.2

theorem wits_all : ∀ i < 1024,
    witK 1100 11 (pidn 1100 11) HNAE.T HNAC.C HNAW.C HNAW.F HNAW.M 48 i = true := by
  refine of_slices' (L := 16) (K := 64) (by decide) fun s hs => ?_
  have h := wtK.all s hs
  unfold wt witSl at h
  rwa [strictB_app'] at h

theorem hnAO_ok : hnAOCheck (decodePairsO hnAProgStr) hnAPregs (decodePairsO hnAPoolStr).toArray
    (decodeAO hnAWitStr) = true := by
  obtain ⟨hgs, hg⟩ := HNAG0.g_get
  obtain ⟨hRs, -⟩ := regs_facts
  unfold hnAOCheck aCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro s hs
    rw [hgs] at hs
    rw [hg s hs]
    exact validA_unpack (allN_spec HN2092.gP s hs)
  · rw [hgs, prog_eq, List.range_eq_range']
    refine progOK_of 2875 0 24 fun t ht => ?_
    have h := steps t ht
    unfold stepK at h
    simp only [bAnd_eq', Bool.and_eq_true, Nat.blt_eq, Nat.add_eq] at h
    rw [Nat.zero_add]
    exact ⟨h.1, h.2.1⟩
  · rw [hRs]
    decide
  · rw [Array.all_eq_true_iff_forall_mem]
    intro gh hgh
    obtain ⟨f, hf, rfl⟩ := Array.mem_iff_getElem.1 hgh
    have hf' : f < 48 := by
      have := pool_size
      unfold pool at this
      omega
    have e := pool_get hf'
    unfold pool at e
    rw [← getElem!_pos _ f hf, e]
    obtain ⟨h1, h2, -⟩ := pool_lt hf'
    obtain ⟨ha, hpa⟩ := reg_get h1
    obtain ⟨hb, hpb⟩ := reg_get h2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨by rw [hRs]; exact h1, by rw [hRs]; exact h2⟩, ?_⟩, ?_⟩
    · change validA 1100 R[HNAT.QN (2 * f)]! = true
      rw [ha]
      exact validA_unpack (CFSG.KS.PinvS.permOK_pinvS hpa.1 hpa.2)
    · change validA 1100 R[HNAT.QN (2 * f + 1)]! = true
      rw [hb]
      exact validA_unpack (CFSG.KS.PinvS.permOK_pinvS hpb.1 hpb.2)
  · rw [allLt_iff]
    intro f hf
    change f < cms.size at hf
    rw [cms_size] at hf
    change validA 1100 cms[f]! = true
    obtain ⟨e, hp⟩ := cms_get f hf
    rw [e]
    exact validA_unpack (CFSG.KS.PinvS.permOK_pinvS hp.1 hp.2)
  · decide
  · exact enum_ok
  · change (enumBfs 1100 gs psO (2 * 1024)).pts.size = 1024
    rw [pts_eq, Array.size_ofFn]
  · rw [wits_eq]
    simp
  · unfold aLoop
    rw [allLt_iff]
    intro i hi
    change aWitOK 1100 cms (enumBfs 1100 gs psO (2 * 1024)).pts[i]! (decodeAO hnAWitStr)[i]! = true
    rw [pt_get hi, wits_eq, getElem!_pos _ i (by simpa using hi)]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
    exact aWitOK_of_witK hsz cms_size cms_get (pp_pts i hi) (wits_all i hi)

end CertificateChecks.KernelSpor.HNAS

end

module

public import Certificates.Kernel.SporSch.PairJ3.Tab
public import Certificates.Kernel.SporSch.PairJ3.Rels
public import Certificates.Kernel.SporSch.PairJ3.ClTab
public import Certificates.Kernel.SporSch.PairJ3.ClRec
public import Certificates.Kernel.SporSch.PairJ3.ClRun
public import CFSG.Certificates.Kernel.SporSch.PairKSound
public import CFSG.Certificates.Kernel.SporSch.RuPresSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Bounds.J3Alt.RelsTC
public import CFSG.Sporadic.Presentation.J3
public import Certificates.Kernel.J3.Bridge
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Monster.B.Mathieu.ChainCheck
public import CFSG.Sporadic.Schreier.PairJ3CheckInputs
public meta import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Certificates.Kernel.SporSch.PairClTProof
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.PresCard
public import CFSG.Sporadic.Presentation.Common

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PJ3Check

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Pres CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairJ3
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Mathieu CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
open CertificateChecks.KernelSporSch

theorem arr_eq (j : Nat) (hj : j < 5) : j3StrongArrs[j]! = unpack 6156 13 (PJ3.S j) := by
  have h := hexTabK_sound tab j hj
  rw [← PJ3Text.eq] at h
  rw [j3StrongArrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact h

theorem binds : Binds 6156 13 PJ3.S 5 4 PJ3.BP j3StrongArrs baseArr :=
  ⟨by decide, by decide, by decide, by simp [j3StrongArrs], arr_eq, by decide, by decide⟩

theorem words_eq : j3Words = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 5 PJ3Words.D := by
  decide

@[expose] noncomputable def g (k : Nat) : Equiv.Perm (Fin 6156) :=
  permOfArr 6156 (unpack 6156 13 (PJ3.S k))

theorem rep_g (k : Nat) (hk : k < 5) : Rep 6156 (unpack 6156 13 (PJ3.S k)) (g k) ∧
    Rep 6156 (unpack 6156 13 (PJ3.SI k)) (g k)⁻¹ :=
  rep_permOfArr (invEqK_sound (allN_spec perm k hk)).2

theorem idParts : canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13) = true ∧
    idK 6156 13 (mask 13) = true :=
  (bAnd_iff (canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13)) (idK 6156 13 (mask 13))).1 idOK

theorem hidA : idA 6156 = unpack 6156 13 (pidn 6156 13) := (idK_sound idParts.2).symm

theorem hGi (i : Nat) : G i = PJ3.S (if i = 0 then 0 else 1) ∧
    GI i = PJ3.SI (if i = 0 then 0 else 1) := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    exact ⟨rfl, rfl⟩
  · have hb : Nat.beq i 0 = false := by cases i with | zero => omega | succ k => rfl
    unfold G GI
    rw [hb, ite_eq_right_iff.2 (fun h => absurd h (by omega))]
    exact ⟨rfl, rfl⟩

theorem hi (i : Nat) : img2 (g 0) (g 1) i = g (if i = 0 then 0 else 1) := by
  unfold img2
  split <;> rfl

theorem gen_facts (i : Nat) : Rep 6156 (unpack 6156 13 (G i)) (img2 (g 0) (g 1) i) ∧
    Rep 6156 (unpack 6156 13 (GI i)) (img2 (g 0) (g 1) i)⁻¹ ∧
    canonK 6156 13 (mask 13) (6156 * 13) (G i) = true ∧
    canonK 6156 13 (mask 13) (6156 * 13) (GI i) = true := by
  have hk : (if i = 0 then 0 else 1) < 2 := by split <;> omega
  rw [hi, (hGi i).1, (hGi i).2]
  obtain ⟨c1, c2⟩ := (bAnd_iff _ _).1 (allN_spec canonOK _ hk)
  exact ⟨(rep_g _ (by omega)).1, (rep_g _ (by omega)).2, c1, c2⟩

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by simpa [Nat.blt_eq] using h

theorem word_rep {r : Nat} (hr : r < 8) :
    Rep 6156 (unpack 6156 13 (PJ3R.TT (16 * r))) (wordProd (img2 (g 0) (g 1))
      (wAt CFSG.KC.J3A.rels r)) := by
  obtain ⟨hk, he⟩ := (bAnd_iff _ _).1 (EC.all r (by change r < 8; exact hr))
  have hlen : (wAt CFSG.KC.J3A.rels r).length ≤ 4 * KK r := by
    rw [← lenL_eq]
    change lenL (wAt CFSG.KC.J3A.rels r) ≤ 4 * ((lenL (wAt CFSG.KC.J3A.rels r) + 3) / 4)
    omega
  have hK : KK r ≤ 16 := Nat.le_of_ble_eq_true hk
  have hid := idParts.1
  refine (word_chain (fun i => (gen_facts i).1) (fun i => (gen_facts i).2.1)
    (fun i => ⟨(gen_facts i).2.2.1, (gen_facts i).2.2.2⟩) hid hidA
    (T := fun q => PJ3R.TT (16 * r + q)) hlen (Nat.eq_of_beq_eq_true he) fun q hq => ?_).1
  have h := JC.all (16 * r + q) (by change 16 * r + q < 128; omega)
  unfold jobF at h
  rw [strictB_eq', strictB_eq'] at h
  have e1 : Nat.div (16 * r + q) 16 = r := by
    change (16 * r + q) / 16 = r
    omega
  have e2 : Nat.mod (16 * r + q) 16 = q := by
    change (16 * r + q) % 16 = q
    omega
  rw [e1, e2, blt_true hq] at h
  rw [← takeL_eq, ← dropL_eq]
  exact Nat.eq_of_beq_eq_true h

theorem relators : ∀ v ∈ TauCeti.Sporadic.j3Presentation.relatorLetters,
    wordProd (img2 (g 0) (g 1)) v = 1 := by
  rw [CFSG.KC.J3A.rels_eq]
  intro v hv
  obtain ⟨r, hr, hrv⟩ := List.getElem_of_mem hv
  have hlen : CFSG.KC.J3A.rels.length = 8 := rfl
  have hr8 : r < 8 := hlen ▸ hr
  have hw : wAt CFSG.KC.J3A.rels r = v := by
    rw [wAt_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some, hrv]
  have h := word_rep hr8
  have e : PJ3R.TT (16 * r) = pidn 6156 13 := Nat.eq_of_beq_eq_true (allN_spec tgtRel r hr8)
  rw [hw, e, ← hidA] at h
  exact h.unique rep_idA

theorem generatorCount_eq : TauCeti.Sporadic.j3Presentation.generatorCount = 2 := by
  simp [TauCeti.GroupPresentation.generatorCount]

theorem orbits : rawOrbitSizes 6156 j3StrongArrs baseArr = [6156, 1360, 2, 3] := by
  rw [rawOrbitSizesK_orb binds perm PJ3.ho (by norm_num)]
  decide

theorem range_two (f : Nat → Equiv.Perm (Fin 6156)) :
    (Set.range fun j : Fin 2 => f j.val) = {f 0, f 1} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff,
    Fin.val_zero, Fin.val_one]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem card_le :
    Nat.card (Subgroup.closure (Set.range fun j : Fin 2 =>
      permOfArr 6156 j3StrongArrs[j.val]!)) ≤
      (rawOrbitSizes 6156 j3StrongArrs baseArr).prod := by
  have hb := CertificateChecks.KernelJ3.j3
  have hfin : Finite TauCeti.Sporadic.j3Presentation.Group := hb.1
  have hc : Nat.card TauCeti.Sporadic.j3Presentation.Group ≤ 50232960 := hb.2
  rw [range_two (fun j => permOfArr 6156 j3StrongArrs[j]!), arr_eq 0 (by norm_num),
    arr_eq 1 (by norm_num), orbits]
  exact (card_closure_le TauCeti.Sporadic.j3Presentation generatorCount_eq relators).trans
    (hc.trans (by norm_num))

theorem perm2 : allN 5 (fun j => permOK 6156 13 (mask 13) (6156 * 13) (PJ3.S j) (PJ3.SI j)) =
    true := perm

theorem inv_eq (l : Nat) (hl : l < 5) : (rawInvs 6156 j3StrongArrs)[l]! = unpack 6156 13 (PJ3.SI l) := by
  have hI := (invEqK_sound (allN_spec perm l hl)).1
  have hsz : j3StrongArrs.size = 5 := by simp [j3StrongArrs]
  rw [← hI, ← arr_eq l hl, rawInvs, getElem!_pos (j3StrongArrs.map (invCand 6156)) l
    (by simp [hsz]; omega), getElem!_pos j3StrongArrs l (by omega), Array.getElem_map]

theorem letter_eq (l : Nat) (hl : l < 2) : letterK PJ3.S PJ3.SI 5 (PJ3Cl.gl l) = PJ3.S l ∧
    letterK PJ3.S PJ3.SI 5 (invL 5 (PJ3Cl.gl l)) = PJ3.SI l := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem gens_get (l : Nat) (hl : l < 2) :
    gens[l]! = j3StrongArrs[l]! ∧ gensInv[l]! = (rawInvs 6156 j3StrongArrs)[l]! := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact ⟨by simp only [gens, List.getElem!_toArray, List.getElem!_cons_zero],
      by simp only [gensInv, List.getElem!_toArray, List.getElem!_cons_zero]⟩
  · exact ⟨by simp only [gens, List.getElem!_toArray, List.getElem!_cons_succ,
      List.getElem!_cons_zero], by simp only [gensInv, List.getElem!_toArray,
      List.getElem!_cons_succ, List.getElem!_cons_zero]⟩

theorem hg : gens.size = 2 ∧ gensInv.size = 2 ∧
    ∀ l < 2, gens[l]! = unpack 6156 13 (letterK PJ3.S PJ3.SI 5 (PJ3Cl.gl l)) ∧
      gensInv[l]! = unpack 6156 13 (letterK PJ3.S PJ3.SI 5 (invL 5 (PJ3Cl.gl l))) := by
  refine ⟨rfl, rfl, fun l hl => ?_⟩
  rw [(letter_eq l hl).1, (letter_eq l hl).2, (gens_get l hl).1, (gens_get l hl).2]
  exact ⟨arr_eq l (by omega), inv_eq l (by omega)⟩

theorem wA_eq : wA = [unpack 6156 13 (PJ3.S 0)] := by
  rw [wA, arr_eq 0 (by omega)]

theorem wB_eq : wB = [unpack 6156 13 (PJ3.S 1)] := by
  rw [wB, arr_eq 1 (by omega)]

theorem tabs : TabsT 6156 13 5 4 PJ3.BP PJ3T.NR PJ3T.NR PJ3.S PJ3.SI PJ3.LR PJ3T.Ts PJ3T.LT
    PJ3T.PT PJ3T.QT 61 1024 7 1024 :=
  ⟨by decide, by decide, by decide, by decide, PJ3Cl.TS.all, PJ3Cl.LTc.all, PJ3Cl.ptB_all,
    PJ3Cl.qtB_all⟩

theorem ok0 : ClosNFT 6156 13 5 4 PJ3T.NR PJ3T.NR PJ3.LR PJ3T.LT PJ3T.PT PJ3T.QT bs 2 PJ3Cl.gl
    PJ3Cl.RP0 PJ3T.c 30000 103 8 32 52 64 PJ3Cl.X PJ3Cl.W PJ3Cl.K PJ3T.C PJ3Cl.SO PJ3Cl.SOI :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    PJ3Cl.canon0, PJ3Cl.ltbs, PJ3Cl.st0, PJ3Cl.k0, PJ3Cl.recB_all, PJ3Cl.srtB_all,
    Nat.eq_of_beq_eq_true PJ3Cl.c00, Nat.eq_of_beq_eq_true PJ3Cl.c0N, PJ3Cl.runB_all⟩

theorem rep_eq : wA = PJ3Cl.RP0.map (unpack 6156 13) := wA_eq

theorem cl_eq : cl = [(wA, closureOf wA)] := rfl

theorem o1 : ordWK 6156 13 bs [PJ3.S 0] 2 = true := by quickRfl
theorem o2 : ordWK 6156 13 bs [PJ3.S 1] 3 = true := by quickRfl
theorem o3 : ordWK 6156 13 bs [PJ3.S 1, PJ3.S 0] 19 = true := by quickRfl
theorem o4 : ordWK 6156 13 bs [PJ3.S 1, PJ3.S 1, PJ3.S 0, PJ3.S 1, PJ3.S 0] 9 = true := by
  quickRfl

set_option maxHeartbeats 2000000 in
theorem facts :
    (rawChainOK 6156 (j3StrongArrs.extract 0 2) j3StrongArrs baseArr j3Words 4 = true ∧
      rawOrbitSizes 6156 j3StrongArrs baseArr = [6156, 1360, 2, 3])
    ∧ (ordB bs wA 2 = true ∧ ordB bs wB 3 = true ∧ ordB bs (patW wA wB [false, true]) 19 = true ∧
      ordB bs (patW wA wB commPat) 9 = true)
    ∧ ((∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 6156 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 26163) := by
  have cl0 := ClTP.closNFT_proved (bs := bs) (rep := wA) binds perm PJ3.ho (by decide) tabs rfl hg rep_eq
    ok0
  have srt := keysK_sound (cs := [(PJ3T.c, PJ3Cl.K)]) (by simp) (by decide) PJ3Cl.srtB_all
  have hcl : closureOf wA = conjClosureNF 6156 (rawLevels 6156 j3StrongArrs baseArr) bs gens gensInv
      (decodeNF (rawLevels 6156 j3StrongArrs baseArr) (baseImgs bs wA).toArray) 30000 := rfl
  have hlv : PairJ3.levels = rawLevels 6156 j3StrongArrs baseArr := rfl
  have oA : ordB bs wA 2 = true := by
    rw [rep_eq]
    exact ordWK_sound o1
  generalize conjClosureNF 6156 (rawLevels 6156 j3StrongArrs baseArr) bs gens gensInv
    (decodeNF (rawLevels 6156 j3StrongArrs baseArr) (baseImgs bs wA).toArray) 30000 = E at cl0 hcl
  refine ⟨⟨?_, orbits⟩, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [words_eq]
    exact rawChainK_of_card_orb 4 binds PJ3.head PJ3.ho (by decide) card_le
  · have e3 : patW [unpack 6156 13 (PJ3.S 0)] [unpack 6156 13 (PJ3.S 1)] [false, true] =
        [PJ3.S 1, PJ3.S 0].map (unpack 6156 13) := rfl
    have e4 : patW [unpack 6156 13 (PJ3.S 0)] [unpack 6156 13 (PJ3.S 1)] commPat =
        [PJ3.S 1, PJ3.S 1, PJ3.S 0, PJ3.S 1, PJ3.S 0].map (unpack 6156 13) := rfl
    have e2 : [unpack 6156 13 (PJ3.S 1)] = [PJ3.S 1].map (unpack 6156 13) := rfl
    refine ⟨oA, ?_, ?_, ?_⟩
    · rw [wB_eq, e2]
      exact ordWK_sound o2
    · rw [wA_eq, wB_eq, e3]
      exact ordWK_sound o3
    · rw [wA_eq, wB_eq, e4]
      exact ordWK_sound o4
  · intro c hc
    rw [cl_eq, List.mem_singleton] at hc
    rw [hc]
    exact oA
  · intro c hc
    rw [cl_eq, List.mem_singleton] at hc
    rw [hc]
    dsimp only
    rw [hcl, hlv]
    exact cl0.1
  · rw [cl_eq, List.map_singleton, hcl, hlv]
    unfold keysDistinctNF
    rw [List.flatMap_singleton, cl0.2.2]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using srt
  · rw [cl_eq, List.map_singleton, List.sum_singleton, hcl, cl0.2.1]
    exact Nat.eq_of_beq_eq_true PJ3Cl.cSz

end CertificateChecks.KernelSporSch.PJ3Check

end

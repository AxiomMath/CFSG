module

public import Certificates.Kernel.SporSch.PairHS.Tab
public import Certificates.Kernel.SporSch.PairHS.Rels
public import Certificates.Kernel.SporSch.PairHS.ClTab
public import Certificates.Kernel.SporSch.PairHS.ClRecA
public import Certificates.Kernel.SporSch.PairHS.ClRecB
public import Certificates.Kernel.SporSch.PairHS.ClRunA
public import Certificates.Kernel.SporSch.PairHS.ClRun
public import CFSG.Certificates.Kernel.SporSch.PairKSound
public import CFSG.Certificates.Kernel.SporSch.RuPresSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Bounds.HSAlt.RelsTC
public import CFSG.Sporadic.Presentation.HSExact
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Monster.B.Mathieu.ChainCheck
public import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import CFSG.Sporadic.Schreier.PairHSCert
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

namespace CertificateChecks.KernelSporSch.PHSCheck

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Pres CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairHS
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Mathieu CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
open CertificateChecks.KernelSporSch

theorem arr_eq (j : Nat) (hj : j < 8) : hsStrongArrs[j]! = unpack 3850 12 (PHSC.S j) := by
  rw [PHSCert.arr_eq j hj, Nat.eq_of_beq_eq_true (allN_spec sEq j hj)]

theorem binds : Binds 3850 12 PHSC.S 8 4 PHSC.BP hsStrongArrs baseArr :=
  ⟨by decide, by decide, by decide, by simp [hsStrongArrs], arr_eq, by decide, by decide⟩

theorem words_eq : hsWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 8 PHSWords.D := by
  decide

@[expose] noncomputable def g (k : Nat) : Equiv.Perm (Fin 3850) :=
  permOfArr 3850 (unpack 3850 12 (PHSC.S k))

theorem rep_g (k : Nat) (hk : k < 8) : Rep 3850 (unpack 3850 12 (PHSC.S k)) (g k) ∧
    Rep 3850 (unpack 3850 12 (PHSC.SI k)) (g k)⁻¹ :=
  rep_permOfArr (invEqK_sound (allN_spec perm k hk)).2

theorem idParts : canonK 3850 12 (mask 12) (3850 * 12) (pidn 3850 12) = true ∧
    idK 3850 12 (mask 12) = true :=
  (bAnd_iff (canonK 3850 12 (mask 12) (3850 * 12) (pidn 3850 12)) (idK 3850 12 (mask 12))).1 idOK

theorem hidA : idA 3850 = unpack 3850 12 (pidn 3850 12) := (idK_sound idParts.2).symm

theorem hGi (i : Nat) : G i = PHSC.S (if i = 0 then 0 else 1) ∧
    GI i = PHSC.SI (if i = 0 then 0 else 1) := by
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

theorem gen_facts (i : Nat) : Rep 3850 (unpack 3850 12 (G i)) (img2 (g 0) (g 1) i) ∧
    Rep 3850 (unpack 3850 12 (GI i)) (img2 (g 0) (g 1) i)⁻¹ ∧
    canonK 3850 12 (mask 12) (3850 * 12) (G i) = true ∧
    canonK 3850 12 (mask 12) (3850 * 12) (GI i) = true := by
  have hk : (if i = 0 then 0 else 1) < 2 := by split <;> omega
  rw [hi, (hGi i).1, (hGi i).2]
  obtain ⟨c1, c2⟩ := (bAnd_iff _ _).1 (allN_spec canonOK _ hk)
  exact ⟨(rep_g _ (by omega)).1, (rep_g _ (by omega)).2, c1, c2⟩

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by simpa [Nat.blt_eq] using h

theorem word_rep {r : Nat} (hr : r < 13) :
    Rep 3850 (unpack 3850 12 (PHSR.TT (10 * r))) (wordProd (img2 (g 0) (g 1))
      (wAt CFSG.KC.HSK.relsLit r)) := by
  obtain ⟨hk, he⟩ := (bAnd_iff _ _).1 (EC.all r (by change r < 13; exact hr))
  have hlen : (wAt CFSG.KC.HSK.relsLit r).length ≤ 4 * KK r := by
    rw [← lenL_eq]
    change lenL (wAt CFSG.KC.HSK.relsLit r) ≤ 4 * ((lenL (wAt CFSG.KC.HSK.relsLit r) + 3) / 4)
    omega
  have hK : KK r ≤ 10 := Nat.le_of_ble_eq_true hk
  have hid := idParts.1
  refine (word_chain (fun i => (gen_facts i).1) (fun i => (gen_facts i).2.1)
    (fun i => ⟨(gen_facts i).2.2.1, (gen_facts i).2.2.2⟩) hid hidA
    (T := fun q => PHSR.TT (10 * r + q)) hlen (Nat.eq_of_beq_eq_true he) fun q hq => ?_).1
  have h := JC.all (10 * r + q) (by change 10 * r + q < 130; omega)
  unfold jobF at h
  rw [strictB_eq', strictB_eq'] at h
  have e1 : Nat.div (10 * r + q) 10 = r := by
    change (10 * r + q) / 10 = r
    omega
  have e2 : Nat.mod (10 * r + q) 10 = q := by
    change (10 * r + q) % 10 = q
    omega
  rw [e1, e2, blt_true hq] at h
  rw [← takeL_eq, ← dropL_eq]
  exact Nat.eq_of_beq_eq_true h

theorem relators : ∀ v ∈ TauCeti.Sporadic.hsPresentation.relatorLetters,
    wordProd (img2 (g 0) (g 1)) v = 1 := by
  rw [CFSG.KC.HSK.rels_eq]
  intro v hv
  obtain ⟨r, hr, hrv⟩ := List.getElem_of_mem hv
  have hlen : CFSG.KC.HSK.relsLit.length = 13 := rfl
  have hr13 : r < 13 := hlen ▸ hr
  have hw : wAt CFSG.KC.HSK.relsLit r = v := by
    rw [wAt_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some, hrv]
  have h := word_rep hr13
  have e : PHSR.TT (10 * r) = pidn 3850 12 := Nat.eq_of_beq_eq_true (allN_spec tgtRel r hr13)
  rw [hw, e, ← hidA] at h
  exact h.unique rep_idA

theorem generatorCount_eq : TauCeti.Sporadic.hsPresentation.generatorCount = 2 := by
  simp [TauCeti.GroupPresentation.generatorCount]

theorem orbits : rawOrbitSizes 3850 hsStrongArrs baseArr = [3850, 960, 6, 2] := by
  rw [rawOrbitSizesK_orb binds perm PHSC.ho (by norm_num)]
  decide

theorem range_two (f : Nat → Equiv.Perm (Fin 3850)) :
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
      permOfArr 3850 hsStrongArrs[j.val]!)) ≤
      (rawOrbitSizes 3850 hsStrongArrs baseArr).prod := by
  have hb := CFSG.Sporadic.Presentation.HS.finite_card_le
  have hfin : Finite TauCeti.Sporadic.hsPresentation.Group := hb.1
  have hc : Nat.card TauCeti.Sporadic.hsPresentation.Group ≤ 44352000 := hb.2
  rw [range_two (fun j => permOfArr 3850 hsStrongArrs[j]!), arr_eq 0 (by norm_num),
    arr_eq 1 (by norm_num), orbits]
  exact (card_closure_le TauCeti.Sporadic.hsPresentation generatorCount_eq relators).trans
    (hc.trans (by norm_num))

theorem inv_eq (l : Nat) (hl : l < 8) :
    (rawInvs 3850 hsStrongArrs)[l]! = unpack 3850 12 (PHSC.SI l) := by
  have hI := (invEqK_sound (allN_spec perm l hl)).1
  have hsz : hsStrongArrs.size = 8 := by simp [hsStrongArrs]
  rw [← hI, ← arr_eq l hl, rawInvs, getElem!_pos (hsStrongArrs.map (invCand 3850)) l
    (by simp [hsz]; omega), getElem!_pos hsStrongArrs l (by omega), Array.getElem_map]

theorem letter_eq (l : Nat) (hl : l < 2) : letterK PHSC.S PHSC.SI 8 (PHSCl.gl l) = PHSC.S l ∧
    letterK PHSC.S PHSC.SI 8 (invL 8 (PHSCl.gl l)) = PHSC.SI l := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem gens_get (l : Nat) (hl : l < 2) :
    gens[l]! = hsStrongArrs[l]! ∧ gensInv[l]! = (rawInvs 3850 hsStrongArrs)[l]! := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact ⟨by simp only [gens, List.getElem!_toArray, List.getElem!_cons_zero],
      by simp only [gensInv, List.getElem!_toArray, List.getElem!_cons_zero]⟩
  · exact ⟨by simp only [gens, List.getElem!_toArray, List.getElem!_cons_succ,
      List.getElem!_cons_zero], by simp only [gensInv, List.getElem!_toArray,
      List.getElem!_cons_succ, List.getElem!_cons_zero]⟩

theorem hg : gens.size = 2 ∧ gensInv.size = 2 ∧
    ∀ l < 2, gens[l]! = unpack 3850 12 (letterK PHSC.S PHSC.SI 8 (PHSCl.gl l)) ∧
      gensInv[l]! = unpack 3850 12 (letterK PHSC.S PHSC.SI 8 (invL 8 (PHSCl.gl l))) := by
  refine ⟨rfl, rfl, fun l hl => ?_⟩
  rw [(letter_eq l hl).1, (letter_eq l hl).2, (gens_get l hl).1, (gens_get l hl).2]
  exact ⟨arr_eq l (by omega), inv_eq l (by omega)⟩

theorem wA_eq : wA = [unpack 3850 12 (PHSC.S 0)] := by
  rw [wA, arr_eq 0 (by omega)]

theorem wB_eq : wB = [unpack 3850 12 (PHSC.S 1)] := by
  rw [wB, arr_eq 1 (by omega)]

theorem tabs : TabsT 3850 12 8 4 PHSC.BP PHST.NR PHST.NR PHSC.S PHSC.SI PHSC.LR PHST.Ts PHST.LT
    PHST.PT PHST.QT 61 1024 4 1024 :=
  ⟨by decide, by decide, by decide, by decide, PHSCl.TS.all, PHSCl.LTc.all, PHSCl.ptB_all,
    PHSCl.qtB_all⟩

theorem okA : ClosNFT 3850 12 8 4 PHST.NR PHST.NR PHSC.LR PHST.LT PHST.PT PHST.QT bs 2 PHSCl.gl
    PHSCl.RPA PHST.c 20000 23 8 32 12 64 PHSCl.XA PHSCl.WA PHSCl.KA PHST.C PHSCl.SOA PHSCl.SOIA :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    PHSCl.canonA, PHSCl.ltbs, PHSCl.stA, PHSCl.kA, PHSCl.recA_all, PHSCl.srtA_all,
    Nat.eq_of_beq_eq_true PHSCl.cA0, Nat.eq_of_beq_eq_true PHSCl.cAN, PHSCl.runA_all⟩

theorem okB : ClosNFT 3850 12 8 4 PHST.NR PHST.NR PHSC.LR PHST.LT PHST.PT PHST.QT bs 2 PHSCl.gl
    PHSCl.RPB PHSU.c 20000 61 8 32 31 64 PHSCl.XB PHSCl.WB PHSCl.KB PHSU.C PHSCl.SOB PHSCl.SOIB :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    PHSCl.canonB, PHSCl.ltbs, PHSCl.stB, PHSCl.kB, PHSCl.recB_all, PHSCl.srtB_all,
    Nat.eq_of_beq_eq_true PHSCl.cB0, Nat.eq_of_beq_eq_true PHSCl.cBN, PHSCl.runB_all⟩

theorem repA_eq : wA = PHSCl.RPA.map (unpack 3850 12) := wA_eq

theorem repB_eq : wC = PHSCl.RPB.map (unpack 3850 12) := by
  rw [wC, wA_eq, wB_eq]
  rfl

theorem cl_eq : cl = [(wA, closureOf wA), (wC, closureOf wC)] := rfl

theorem o1 : ordWK 3850 12 bs [PHSC.S 0] 2 = true := by quickRfl
theorem o2 : ordWK 3850 12 bs [PHSC.S 1] 5 = true := by quickRfl
theorem o3 : ordWK 3850 12 bs [PHSC.S 1, PHSC.S 0] 11 = true := by quickRfl
theorem o4 : ordWK 3850 12 bs [PHSC.S 1, PHSC.S 1, PHSC.S 1, PHSC.S 1, PHSC.S 0, PHSC.S 1,
    PHSC.S 0] 5 = true := by
  quickRfl
theorem oC : ordWK 3850 12 bs PHSCl.RPB 2 = true := by quickRfl

private theorem sum_two {w₀ w₁ : List (Array Nat)}
    {C₀ C₁ : Array (Array Nat) × Array Nat × Array Nat} {s : Nat}
    (h : C₀.1.size + C₁.1.size = s) : ([(w₀, C₀), (w₁, C₁)].map fun c => c.2.1.size).sum = s := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  exact h

set_option maxHeartbeats 4000000 in
theorem facts :
    (rawChainOK 3850 (hsStrongArrs.extract 0 2) hsStrongArrs baseArr hsWords 4 = true ∧
      rawOrbitSizes 3850 hsStrongArrs baseArr = [3850, 960, 6, 2])
    ∧ (ordB bs wA 2 = true ∧ ordB bs wB 5 = true ∧ ordB bs (patW wA wB [false, true]) 11 = true ∧
      ordB bs (patW wA wB commPat) 5 = true)
    ∧ ((∀ c ∈ cl, ordB bs c.1 2 = true) ∧
      (∀ c ∈ cl, closureOK levels bs gens gensInv c.1 c.2.1 c.2.2.1 c.2.2.2 = true) ∧
      keysDistinctNF 3850 levels bs (cl.map fun c => c.2.1) = true ∧
      (cl.map fun c => c.2.1.size).sum = 21175) := by
  have clA := ClTP.closNFT_proved (bs := bs) (rep := wA) binds perm PHSC.ho (by decide) tabs rfl hg
    repA_eq okA
  have clB := ClTP.closNFT_proved (bs := bs) (rep := wC) binds perm PHSC.ho (by decide) tabs rfl hg
    repB_eq okB
  have srt := keysK_sound (cs := [(PHST.c, PHSCl.KA), (PHSU.c, PHSCl.KB)]) (nB := 42) (R := 8)
    (B := 64) (by simp) (by decide) PHSCl.jsrt_all
  have hA : closureOf wA = conjClosureNF 3850 (rawLevels 3850 hsStrongArrs baseArr) bs gens gensInv
      (decodeNF (rawLevels 3850 hsStrongArrs baseArr) (baseImgs bs wA).toArray) 20000 := rfl
  have hC : closureOf wC = conjClosureNF 3850 (rawLevels 3850 hsStrongArrs baseArr) bs gens gensInv
      (decodeNF (rawLevels 3850 hsStrongArrs baseArr) (baseImgs bs wC).toArray) 20000 := rfl
  have hlv : PairHS.levels = rawLevels 3850 hsStrongArrs baseArr := rfl
  have oA : ordB bs wA 2 = true := by
    rw [repA_eq]
    exact ordWK_sound o1
  have oB : ordB bs wC 2 = true := by
    rw [repB_eq]
    exact ordWK_sound oC
  generalize conjClosureNF 3850 (rawLevels 3850 hsStrongArrs baseArr) bs gens gensInv
    (decodeNF (rawLevels 3850 hsStrongArrs baseArr) (baseImgs bs wA).toArray) 20000 = EA at clA hA
  generalize conjClosureNF 3850 (rawLevels 3850 hsStrongArrs baseArr) bs gens gensInv
    (decodeNF (rawLevels 3850 hsStrongArrs baseArr) (baseImgs bs wC).toArray) 20000 = EB at clB hC
  refine ⟨⟨?_, orbits⟩, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [words_eq]
    exact rawChainK_of_card_orb 4 binds PHSC.head PHSC.ho (by decide) card_le
  · have e3 : patW [unpack 3850 12 (PHSC.S 0)] [unpack 3850 12 (PHSC.S 1)] [false, true] =
        [PHSC.S 1, PHSC.S 0].map (unpack 3850 12) := rfl
    have e4 : patW [unpack 3850 12 (PHSC.S 0)] [unpack 3850 12 (PHSC.S 1)] commPat =
        [PHSC.S 1, PHSC.S 1, PHSC.S 1, PHSC.S 1, PHSC.S 0, PHSC.S 1, PHSC.S 0].map
          (unpack 3850 12) := rfl
    have e2 : [unpack 3850 12 (PHSC.S 1)] = [PHSC.S 1].map (unpack 3850 12) := rfl
    refine ⟨oA, ?_, ?_, ?_⟩
    · rw [wB_eq, e2]
      exact ordWK_sound o2
    · rw [wA_eq, wB_eq, e3]
      exact ordWK_sound o3
    · rw [wA_eq, wB_eq, e4]
      exact ordWK_sound o4
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact oA
    · exact oB
  · intro c hc
    rw [cl_eq] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · dsimp only
      rw [hA, hlv]
      exact clA.1
    · dsimp only
      rw [hC, hlv]
      exact clB.1
  · rw [cl_eq]
    simp only [List.map_cons, List.map_nil]
    rw [hA, hC, hlv]
    unfold keysDistinctNF
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [clA.2.2, clB.2.2]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using srt
  · rw [cl_eq]
    refine sum_two ?_
    rw [hA, hC, clA.2.1, clB.2.1, Nat.eq_of_beq_eq_true PHSCl.cASz,
      Nat.eq_of_beq_eq_true PHSCl.cBSz]

end CertificateChecks.KernelSporSch.PHSCheck

end

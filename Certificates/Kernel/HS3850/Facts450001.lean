module

public import Certificates.Kernel.HS3850.C450001E
public import Certificates.Kernel.HS3850.Kit
public import CFSG.Sporadic.SmallOddCore.HSThreeCentInputs
public import Certificates.Kernel.LocalQT.HSAut.F4146

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HS3850.T450001

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.C4126
open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.KD.LQT.HO (Cn cIdn)

theorem hd3 : EK.cnt = 720 ∧ penumHdK idn EK.cnt 720 EK.T EK.PL = true ∧
    EK.G 0 = wfoldR lb [0] ∧ EK.G 1 = wfoldR lb [4, 1] ∧ EK.G 2 = wfoldR lb [3, 4, 1, 3, 2] ∧
    wfoldR lb [3, 2, 4, 3, 4, 2, 4, 1, 3] = HC.F 32 ∧
    pc (pc (HC.F 32) (HC.F 32)) (HC.F 32) = idn ∧ Nat.beq (HC.F 32) idn = false ∧
    allN 3 (fun j => Nat.beq (pc (HC.F 32) (EK.G j)) (pc (EK.G j) (HC.F 32))) = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := (by simpa only [bAnd_iff] using hd_ok :
    Nat.beq EK.cnt 720 = true ∧ _ ∧ Nat.beq (EK.G 0) _ = true ∧ Nat.beq (EK.G 1) _ = true ∧
      Nat.beq (EK.G 2) _ = true ∧ Nat.beq (wfoldR lb _) _ = true ∧ Nat.beq (pc _ _) _ = true ∧
      (Nat.beq (HC.F 32) idn).not = true ∧ _)
  exact ⟨Nat.eq_of_beq_eq_true h1, h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7,
    by simpa using h8, h9⟩

theorem base_get {l : Nat} (hl : l < 5) : hsThreeBase[l]! = unpack 3850 12 (lb l) ∧ Cn (lb l) := by
  have e : hsThreeBase[l]! = natArr (hsCentTbl (l + 21)) := by
    unfold hsThreeBase
    rw [getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn]
  have e2 : lb l = HC.F (l + 21) := by
    unfold lb
    rw [Nat.add_comm]
    rfl
  rw [e, e2]
  exact cent_parts (by omega)

theorem bWord {ls : List Nat} (hls : ∀ l ∈ ls, l < 5) :
    wordTabS 3850 hsThreeBase ls = unpack 3850 12 (wfoldR lb ls) ∧ Cn (wfoldR lb ls) :=
  wordTabS_unp ls fun l hl => base_get (hls l hl)

theorem x0_eq : natArr (hsCentTbl 32) = unpack 3850 12 (HC.F 32) ∧ Cn (HC.F 32) :=
  cent_parts (by omega)

theorem words_lt : ∀ j < 3, ∀ i ∈ hsThreeWords.getD j [], i < 5 := by decide

theorem eG_eq {j : Nat} (hj : j < 3) : EK.G j = wfoldR lb (hsThreeWords.getD j []) := by
  obtain ⟨-, -, e0, e1, e2, -⟩ := hd3
  interval_cases j
  · exact e0
  · exact e1
  · exact e2

theorem gens_get {j : Nat} (hj : j < 3) :
    hsThreeGens[j]! = unpack 3850 12 (EK.G j) ∧ Cn (EK.G j) := by
  have e : hsThreeGens[j]! = wordTabS 3850 hsThreeBase (hsThreeWords.getD j []) := by
    unfold hsThreeGens
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  rw [e, eG_eq hj]
  exact bWord (words_lt j hj)

theorem gensK : GensOK 3850 12 3 EK.G hsThreeGens :=
  ⟨by simp [hsThreeGens], fun j hj => gens_get hj⟩

theorem ptK : ∀ i < EK.cnt, penumPtK 3850 12 (mask 12) (3850 * 12) false EK.G EK.GI 3 EK.cnt EK.T
    EK.PL EK.POS EK.SRT EK.SRI i = true := by
  intro i hi
  have hi' : i < 720 := hd3.1 ▸ hi
  have hs : i / 32 < 23 := by omega
  exact penumSl_spec (EK.all (i / 32) hs) i (by change i / 32 * 32 ≤ i; omega)
    (by change i < i / 32 * 32 + 32; omega) hi

theorem encK : enumBFS 3850 hsThreeGens 720 = penumRec 3850 12 EK.cnt EK.T EK.PL ∧
    enumOK 3850 hsThreeGens (penumRec 3850 12 EK.cnt EK.T EK.PL) = true :=
  penumK_left_sound (by decide) gensK hd3.2.1 ptK

theorem commAll_x0 : commAll 3850 hsThreeGens (natArr (hsCentTbl 32)) = true := by
  unfold commAll
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  have hs : hsThreeGens.size = 3 := by simp [hsThreeGens]
  rw [hs]
  intro j hj
  obtain ⟨hq, cq⟩ := gens_get hj
  rw [hq, x0_eq.1, comp_pc' x0_eq.2 cq, comp_pc' cq x0_eq.2,
    beq_pc' (cn_pc x0_eq.2 cq) (cn_pc cq x0_eq.2)]
  exact allN_spec hd3.2.2.2.2.2.2.2.2 j hj

theorem hsThree_true : ((∀ k < 5, permOK 3850 (hsCentTbl (k + 21)) = true ∧
        (natArr (hsCentTbl (k + 21))).size = 3850) ∧
      (permOK 3850 (hsCentTbl 32) = true ∧ (natArr (hsCentTbl 32)).size = 3850) ∧
      (∀ i ∈ hsThreeX0Word, i < 5) ∧ (∀ j < 3, ∀ i ∈ hsThreeWords.getD j [], i < 5)) ∧
    (wordTabS 3850 hsThreeBase hsThreeX0Word = natArr (hsCentTbl 32) ∧
      comp 3850 (comp 3850 (natArr (hsCentTbl 32)) (natArr (hsCentTbl 32)))
        (natArr (hsCentTbl 32)) = idTab 3850 ∧
      natArr (hsCentTbl 32) ≠ idTab 3850) ∧
    (enumOK 3850 hsThreeGens hsThreeEnum = true ∧ hsThreeEnum.tabs.size = 720 ∧
      commAll 3850 hsThreeGens (natArr (hsCentTbl 32)) = true) := by
  obtain ⟨hc, -, -, -, -, hx, hcube, hne, -⟩ := hd3
  have hsz : ∀ k < 43, (natArr (hsCentTbl k)).size = 3850 := fun k hk => by
    rw [(cent_parts hk).1]
    exact unpack_size 3850 12 _
  refine ⟨⟨fun k hk => ⟨CFSG.KD.LQT.HN.cent_perm (by omega) (cent_parts (by omega)).2,
      hsz _ (by omega)⟩, ⟨CFSG.KD.LQT.HN.cent_perm (by omega) x0_eq.2, hsz 32 (by omega)⟩,
      by decide, words_lt⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, commAll_x0⟩
  · rw [(bWord (by decide)).1, x0_eq.1]
    unfold hsThreeX0Word
    rw [hx]
  · rw [x0_eq.1, comp_pc' x0_eq.2 x0_eq.2, comp_pc' (cn_pc x0_eq.2 x0_eq.2) x0_eq.2, hcube,
      idTab_idn]
  · intro h
    rw [x0_eq.1, idTab_idn, ← beq_iff_eq, beq_pc' x0_eq.2 cIdn, hne] at h
    exact Bool.false_ne_true h
  · unfold hsThreeEnum
    rw [encK.1]
    exact encK.2
  · unfold hsThreeEnum
    rw [encK.1]
    simp [penumRec, hc]

end CFSG.KD.HS3850.T450001

end

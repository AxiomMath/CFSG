module

public import Certificates.Kernel.Fi22Syl.ChainChecks
public import Certificates.Kernel.Fi22.Letters
public import CFSG.Certificates.Kernel.Spor.PChainSound
public import Certificates.Data.CFSGNative.Fi22.Classes
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases
public import Mathlib.GroupTheory.Perm.Basic

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelFi22S.swAll CertificateChecks.KernelFi22S.swS 11
#kon_join CertificateChecks.KernelFi22S.t0All CertificateChecks.KernelFi22S.t0Sl 16
#kon_join CertificateChecks.KernelFi22S.sch0All CertificateChecks.KernelFi22S.sch0Sl 64

namespace CertificateChecks.KernelFi22S

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.TW CFSG.KS.Fi22L
  CFSG.KS.Fi22S CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

noncomputable abbrev LSN : Array Table := sylLetters (chainLetters orbL)

theorem sl_spec {n cnt r lo len : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} (h : tbfsSlK n cnt r L LV PTS POS PAR LAB TI lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < cnt → tbfsPtK n cnt r L LV PTS POS PAR LAB TI k = true := by
  intro k h1 h2 h3
  have h' := Raw.Orb.allN_iff.1 h (k - lo) (by omega)
  rw [Raw.Orb.strictB_eq] at h'
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rw [e, Eq.mpr Nat.blt_eq h3] at h'
  exact h'

theorem cnts : CNTS 0 = 1024 ∧ CNTS 1 = 128 := by
  have h := sizes_ok
  unfold sizesK at h
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem pt_of {i c : Nat} (h : ptSl i c = true) : ∀ k, 64 * c ≤ k → k < 64 * c + 64 → k < CNTS i →
    tbfsPtK 3510 (CNTS i) (lvK LSK BS 22 i).length LSK (lvAt LSK BS 22 i) (PTSS i) (POSS i)
      (PARS i) (LABS i) (TIS i) k = true := by
  intro k h1 h2 h3
  unfold ptSl at h
  exact sl_spec h k (by change c * 64 ≤ k; omega) (by change k < c * 64 + 64; omega) h3

theorem tree_spec {i : Nat} (hi : i < 2) :
    tbfsHdK 3510 (BS i) (CNTS i) (PTSS i) (POSS i) (PARS i) (LABS i) = true ∧
      ∀ k < CNTS i, tbfsPtK 3510 (CNTS i) (lvK LSK BS 22 i).length LSK (lvAt LSK BS 22 i) (PTSS i)
        (POSS i) (PARS i) (LABS i) (TIS i) k = true := by
  refine ⟨Raw.Orb.allN_iff.1 hd_ok i hi, fun k hk => ?_⟩
  obtain ⟨c0, c1⟩ := cnts
  have h1 := t1_ok
  unfold t1K at h1
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h1
  interval_cases i
  · rw [c0] at hk
    have hs : k / 64 < 16 := by omega
    exact pt_of (t0All (k / 64) hs) k (by omega) (by omega) (by rw [c0]; exact hk)
  · rw [c1] at hk
    rcases (by omega : k < 64 ∨ 64 ≤ k) with hk' | hk'
    · exact pt_of h1.1 k (by omega) (by omega) (by rw [c1]; exact hk)
    · exact pt_of h1.2 k (by omega) (by omega) (by rw [c1]; exact hk)

theorem LSN_size : LSN.size = 22 := by
  unfold LSN sylLetters buildLetters
  simp only [Array.size_ofFn]
  rfl

theorem LSN_get {l : Nat} (hl : l < 22) : LSN[l]! =
    if l % 2 = 0 then wordT 3510 (jGen (chainLetters orbL)) (sylWords ())[l / 2]!
    else invT 3510 (wordT 3510 (jGen (chainLetters orbL)) (sylWords ())[l / 2]!) := by
  rw [getElem!_pos _ l (by rw [LSN_size]; exact hl)]
  simp only [LSN, sylLetters, buildLetters, Array.getElem_ofFn]

theorem sw_eq : ∀ j < 11, ((sylWords ())[j]!).map Int.toNat = swL.getD j [] ∧
    ∀ z ∈ (sylWords ())[j]!, z.toNat < 32 := by
  decide

theorem wJ_eq (w : List Int) (x : Nat) :
    wJ (w.map Int.toNat) x = w.foldr (fun z y => LJk ljPacked slpPacked z.toNat y) x := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    change strictN (wJ (w.map Int.toNat) x) (LJk ljPacked slpPacked z.toNat) = _
    rw [Raw.Orb.strictN_eq, ih]
    rfl

theorem even_TR {j : Nat} (hj : j < 11) :
    TR 3510 (wordT 3510 (jGen (chainLetters orbL)) (sylWords ())[j]!) (LSK (2 * j)) := by
  obtain ⟨hw, hb⟩ := sw_eq j hj
  have hT := wordT_TR (n := 3510) (by norm_num) (gens := jGen (chainLetters orbL))
    (G := fun z => LJk ljPacked slpPacked z.toNat) (sylWords ())[j]! fun z hz =>
      CertificateChecks.KernelFi22.Letters.letters.2.1 _ (hb z hz)
  refine TR_congr hT fun x hx => ?_
  have h0 := swAll j hj
  unfold swS swChk at h0
  have h := Raw.Orb.allN_iff.1 h0 x hx
  rw [← hw, Nat.beq_eq] at h
  change _ = LSK (Nat.mul 2 j) x
  rw [h, wJ_eq]

theorem letters_TR {l : Nat} (hl : l < 22) : TR 3510 LSN[l]! (LSK l) := by
  rw [LSN_get hl]
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · have e1 : 2 * j % 2 = 0 := by omega
    have e2 : 2 * j / 2 = j := by omega
    simp only [e1, e2, ↓reduceIte]
    exact even_TR (by omega)
  · have e1 : ¬ (2 * j + 1) % 2 = 0 := by omega
    have e2 : (2 * j + 1) / 2 = j := by omega
    simp only [e1, e2, ↓reduceIte]
    have hj : j < 22 / 2 := by omega
    refine invT_TR (by norm_num) (even_TR (by omega)) fun x hx => ?_
    obtain ⟨-, a2, -⟩ := invK_spec inv_ok hj hx
    refine ⟨a2, pair_inv (fun y hy => (invK_spec inv_ok hj hy).1)
      (fun y hy => (invK_spec inv_ok hj hy).2.2) x hx, (invK_spec inv_ok hj hx).2.2⟩

theorem schSl_spec {i lo len : Nat}
    (h : schSlK LSK BS 22 PTSS POSS PARS LABS CNTS QB QL 2 i lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < CNTS i → ∀ t < (lvK LSK BS 22 i).length,
      schK LSK PTSS POSS PARS LABS CNTS QB QL 2 i (lvAt LSK BS 22 i t) k = true := by
  intro k h1 h2 h3 t ht
  unfold schSlK at h
  rw [Raw.Orb.strictB_eq] at h
  have h' := Raw.Orb.allN_iff.1 h (k - lo) (by omega)
  rw [Raw.Orb.strictB_eq] at h'
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  have hb : Nat.blt k (CNTS i) = true := Eq.mpr Nat.blt_eq h3
  rw [e, Raw.Orb.bIf_eq] at h'
  simp only [hb, ↓reduceIte] at h'
  exact Raw.Orb.allN_iff.1 h' t ht

theorem sch_spec : ∀ i < 2, ∀ k < CNTS i, ∀ t < (lvK LSK BS 22 i).length,
    schK LSK PTSS POSS PARS LABS CNTS QB QL 2 i (lvAt LSK BS 22 i t) k = true := by
  intro i hi k hk
  obtain ⟨c0, c1⟩ := cnts
  interval_cases i
  · rw [c0] at hk
    have hs : k / 16 < 64 := by omega
    have h := sch0All (k / 16) hs
    unfold sch0Sl at h
    exact schSl_spec h k (by change k / 16 * 16 ≤ k; omega) (by change k < k / 16 * 16 + 16; omega)
      (by rw [c0]; exact hk)
  · rw [c1] at hk
    exact schSl_spec sch1_ok k (Nat.zero_le k) (by change k < 128; omega) (by rw [c1]; exact hk)

theorem chain_hyp : ChainHyp 3510 22 2 LSN sylBase chainQ sylQb LSK BS QL QB CNTS
    PTSS POSS PARS LABS TIS where
  letters := ⟨LSN_size, fun l hl x hx => ((letters_TR hl).2 x hx).1⟩
  inv := ⟨rfl, inv_ok⟩
  base := ⟨rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide⟩⟩
  chk := ⟨rfl, by decide, rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide, rfl⟩⟩
  tree := fun i hi => tree_spec hi

theorem chain_eq : chainTrees 3510 LSN sylBase =
      Array.ofFn (n := 2) (fun i => tbfsRec 3510 (CNTS i.val) (PTSS i.val) (POSS i.val)
        (PARS i.val) (LABS i.val)) ∧
    ∀ chunks, chainOK 3510 LSN sylBase chainQ sylQb (chainTrees 3510 LSN sylBase) chunks = true :=
  pchainK_sound chain_hyp sch_spec term_ok

theorem sizes : orbitSizes (chainTrees 3510 LSN sylBase) = [1024, 128] := by
  obtain ⟨c0, c1⟩ := cnts
  rw [chain_eq.1]
  simp only [orbitSizes, tbfsRec, Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero, List.map_cons,
    List.map_nil, Array.size_ofFn]
  change [CNTS 0, CNTS 1] = _
  rw [c0, c1]

end CertificateChecks.KernelFi22S

end

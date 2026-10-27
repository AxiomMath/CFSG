module

public import Certificates.Kernel.HSA312.Struct
public import Certificates.Kernel.HSA312.CY1
public import CFSG.Quasithin.Background.A312SporHSKInputs
public import Certificates.Kernel.J4Count.Suborb

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HSA312

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.PcW CFSG.KC.HSA312
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.QuasithinUnique.K1.SporadicPerm (hsB compArr applyTab ptsOf)
open CFSG.Quasithin.A312S CFSG.Quasithin.A312S.HS
open CFSG.Sporadic.HS.Native (hsData)

theorem hB : hsB = [0, 1, 2] := by
  rw [← CFSG.KD.HSDc.facts.2.2.2.1]
  decide

theorem hL1K_eq : hsL1K = CFSG.Quasithin.A312Hs.hsLettersK 1 := rfl

theorem hn' : (1100 : Nat) < 2 ^ 32 := by norm_num

theorem hw' : 0 < 11 := by norm_num

theorem hid : Rep 1100 11 I (idTab 1100) := CFSG.KD.LQT.H4089.rep_id0

theorem rL1 : ∀ l < hsL1K.length, Rep 1100 11 (CFSG.KD.LQT.H4089.L1c l) hsL1K[l]! := by
  rw [hL1K_eq, len1]
  exact hL1K

theorem rZ : Rep 1100 11 Z hsZ4K := by
  unfold hsZ4K
  rw [n_eq]
  exact rep_wordTab hn' hw' hid (rep_letters rL1 (by rw [hL1K_eq, len1]; decide)) zW

theorem rE : RepL 1100 11 Es hsEK := by
  unfold hsEK
  rw [n_eq]
  exact repL_words hn' hw' hid rL1 (by rw [hL1K_eq, len1]; decide) rfl eW

theorem rE3 : RepL 1100 11 E3s (hsEK.map fun e => powTab 1100 e 3) :=
  rE.pow hn' hw' hid 3 rfl e3P

theorem rZ2 : Rep 1100 11 Z2 (compArr hsZ4K hsZ4K) := by
  have := rep_comp hn' hw' rZ rZ
  have e : pcS 1100 11 (mask 11) Z Z = Z2 := Nat.eq_of_beq_eq_true z2P
  rwa [e] at this

theorem rZ3 : Rep 1100 11 Z3 (powTab 1100 hsZ4K 3) := by
  have := rep_pow hn' hw' hid rZ 3
  have e : powS 1100 11 (mask 11) I Z 3 = Z3 := Nat.eq_of_beq_eq_true z3P
  rwa [e] at this

theorem all_mem {α : Type} {l : List α} {f : α → Bool} (h : l.all f = true) : ∀ x ∈ l, f x = true :=
  List.all_eq_true.1 h

theorem fix_of {c : Nat} {t : Array Nat} (h : Rep 1100 11 c t) {xs : List (List Nat)}
    (hk : labsK 1100 11 2047 c xs = true) : fixLabs t xs = true := by
  unfold fixLabs
  rw [List.all_eq_true]
  intro x hx
  rw [labsK_spec h hk x hx, beq_self_eq_true]

theorem y1 : A312HS1K := by
  have hm1 := fun e (he : e ∈ hsEK) => rE.mem' he
  unfold A312HS1K
  refine ⟨by rw [hL1K_eq, len1], ?_, ?_, ?_⟩
  · have h := (inclPt_iff.1 incl_ok) 4 (by decide) 1 (by decide)
    exact h.2 (by decide)
  · rw [HSK.Om_get (j := 1) (by decide), List.all_eq_true]
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact fix_of rZ (all_mem fixL Z List.mem_cons_self)
    · obtain ⟨c, hc, hr⟩ := hm1 t ht
      exact fix_of hr (all_mem fixL c (List.mem_cons_of_mem _ hc))
  · unfold Z4StarOK ExtraOK
    rw [n_eq, hB]
    obtain ⟨hEn, hEb⟩ := baseEnum_sound rE rE3 enumE
    have hP0 : ptsOf [0, 1, 2] hsEK ∈ J.ETs.toList := by
      rw [← hEn.2.1, getElem!_pos _ 0 hEn.1]
      exact Array.getElem_mem_toList hEn.1
    have hPb : ∀ x ∈ ptsOf [0, 1, 2] hsEK, x < 1100 := hEb _ hP0
    have hB3 : ∀ b ∈ [0, 1, 2], b < 1100 := by decide
    have rZE : RepL 1100 11 (Z :: Es) (hsZ4K :: hsEK) := rE.cons rZ
    have rZE3 : RepL 1100 11 (Z3 :: E3s) ((hsZ4K :: hsEK).map fun e => powTab 1100 e 3) :=
      rE3.cons rZ3
    obtain ⟨hVn, -⟩ := baseEnum_sound rZE rZE3 enumV
    have hs := sizes
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    refine ⟨⟨hEn, hs.1, fun e he => ?_, ?_, ?_, ?_, fun e he => ?_, fun e he f hf => ?_,
      extra_sound (by norm_num) rE rZ2 hEb hP0 ext⟩, ?_, fun e he => ?_, ?_, hVn, hs.2⟩
    · obtain ⟨c, hc, hr⟩ := hm1 e he
      exact comp_eq hn' hw' hr rZ2 rZ2 hr (all_mem ez c hc)
    · exact rep_eq (rep_comp hn' hw' rZ2 rZ2) hid (eq_of_beq zz)
    · refine rep_ne hw' rZ2 hid fun e => ?_
      have := zne
      rw [e, beq_self_eq_true] at this
      exact Bool.false_ne_true this
    · rw [applyTab_rep rZ2 hPb, ptsOf_rep hB3 rE]
      exact List.contains_iff_mem.1 zin
    · obtain ⟨c, hc, hr⟩ := hm1 e he
      rcases Bool.or_eq_true_iff.1 (all_mem sq c hc) with h | h
      · exact Or.inl (rep_eq (rep_comp hn' hw' hr hr) hid (eq_of_beq h))
      · exact Or.inr (rep_eq (rep_comp hn' hw' hr hr) rZ2 (eq_of_beq h))
    · obtain ⟨c, hc, hr⟩ := hm1 e he
      obtain ⟨d, hd, hs⟩ := hm1 f hf
      rcases Bool.or_eq_true_iff.1 (all_mem (all_mem cm c hc) d hd) with h | h
      · exact Or.inl (comp_eq hn' hw' hr hs hs hr h)
      · exact Or.inr (rep_eq (rep_comp hn' hw' hr hs)
          (rep_comp hn' hw' rZ2 (rep_comp hn' hw' hs hr)) (eq_of_beq h))
    · exact rep_eq (rep_pow hn' hw' hid rZ 4) hid (eq_of_beq z4)
    · obtain ⟨c, hc, hr⟩ := hm1 e he
      exact comp_eq hn' hw' rZ hr hr rZ (all_mem zc c hc)
    · rw [applyTab_rep rZ hPb, ptsOf_rep hB3 rE]
      intro hmem
      have h2 : J.ETs.toList.contains (appC 11 2047 Z (ptsC 11 2047 [0, 1, 2] Es)) = true :=
        List.contains_iff_mem.2 hmem
      have := znot
      rw [h2] at this
      exact Bool.false_ne_true this

end CFSG.KD.HSA312

end

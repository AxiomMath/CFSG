module

public import Certificates.Kernel.J4M2.C4202Checks
public import CFSG.Certificates.Kernel.J4M2HexSound

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelJ4M2

open Equiv CFSG.KC.Enum CFSG.KC.LQT.L CFSG.KS.PK CFSG.KC.J4M2K CFSG.Quasithin.J4M2
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

theorem brec_not4202 (a : Bool) : Bool.rec (motive := fun _ => Bool) true false a = !a := by
  cases a <;> rfl

theorem bnot_true4202 {b : Bool} : (!b) = true ↔ b = false := by
  cases b <;> simp

theorem nat_beq4202 (a b : ℕ) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, nbeq_iff]

theorem ofNat_val77 {h : NeZero 77} (i : Fin 77) : @Fin.ofNat 77 h i.val = i :=
  Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt i.isLt])

theorem h77 : (77 : ℕ) ≤ 128 := by norm_num

theorem ch4202sig_all : ∀ n < 32, ch4202sig n = true := by
  intro n hn
  interval_cases n
  exacts [ch4202sig0, ch4202sig1, ch4202sig2, ch4202sig3, ch4202sig4, ch4202sig5, ch4202sig6,
    ch4202sig7, ch4202sig8, ch4202sig9, ch4202sig10, ch4202sig11, ch4202sig12, ch4202sig13,
    ch4202sig14, ch4202sig15, ch4202sig16, ch4202sig17, ch4202sig18, ch4202sig19, ch4202sig20,
    ch4202sig21, ch4202sig22, ch4202sig23, ch4202sig24, ch4202sig25, ch4202sig26, ch4202sig27,
    ch4202sig28, ch4202sig29, ch4202sig30, ch4202sig31]

theorem chkSig_k : chkSig = true := by
  rw [chkSig, List.all_eq_true]
  intro n hn
  have h := ch4202sig_all n (List.mem_range.1 hn)
  rw [ch4202sig] at h
  refine Eq.trans ?_ h
  congr 1

theorem sigPerm_val4202 {n : ℕ} (hn : n < 32) (i : Fin 77) :
    ((sigPerm n i : Fin 77) : ℕ) = (sigData.getD n []).getD i 0 := by
  have h0 := ch4202sig_all n hn
  rw [ch4202sig] at h0
  have h := List.all_eq_true.1 h0 i.val (List.mem_range.2 i.isLt)
  rw [beq_iff_eq, ofNat_val77] at h
  exact h

theorem code_sig4202 {n : ℕ} (hn : n < 32) : rnc7 (RN.enc (sigPerm n)) = sigC n :=
  rnc7_sig _ n (sigPerm_val4202 hn)

theorem code7_sig4202 {n : ℕ} (hn : n < 32) : code7 (sigPerm n) = sigC n :=
  (rnc7_enc _).symm.trans (code_sig4202 hn)

theorem hexLt4202 : HexLt := by
  apply hexLt_of
  have h := ch4202hexLab
  rw [Bool.and_eq_true, List.all_eq_true] at h
  rw [List.all_eq_true]
  intro l hl
  have h2 := h.2 l hl
  rw [Bool.and_eq_true] at h2
  exact h2.2

theorem dist_pt4202 (i j : Fin 77) :
    (i == j || hexB i != hexB j) = bIf(Nat.beq i.val j.val, true,
      bIf(Nat.beq (fd (nat_lit 22) hexP i.val) (fd (nat_lit 22) hexP j.val), false, true)) := by
  have e : (i == j) = Nat.beq i.val j.val := by
    rw [Bool.eq_iff_iff, beq_iff_eq, nbeq_iff, Fin.ext_iff]
  rw [bne, hexB_beq hexLt4202, e]
  generalize Nat.beq i.val j.val = a
  generalize Nat.beq (fd 22 hexP i.val) (fd 22 hexP j.val) = b
  cases a <;> cases b <;> rfl

theorem dist4202 : ((List.finRange 77).all fun i =>
    (List.finRange 77).all fun j => i == j || hexB i != hexB j) = true := by
  have e : ((List.finRange 77).all fun i =>
      (List.finRange 77).all fun j => i == j || hexB i != hexB j) = distK hexP := by
    rw [distK, allR_eq, ← map_val_finRange, List.all_map]
    refine congrArg _ (funext fun i => ?_)
    rw [Function.comp_apply, allR_eq, ← map_val_finRange, List.all_map]
    refine congrArg _ (funext fun j => ?_)
    rw [Function.comp_apply]
    exact dist_pt4202 i j
  rw [e, ← strictB_eq' hexP distK]
  exact ch4202dist

theorem blockGens_length4202 : blockGens.length = 25 := rfl

theorem ch4202gen_all : ∀ k < 25, hexGenK k = true := by
  intro k hk
  interval_cases k
  exacts [ch4202gen0, ch4202gen1, ch4202gen2, ch4202gen3, ch4202gen4, ch4202gen5, ch4202gen6,
    ch4202gen7, ch4202gen8, ch4202gen9, ch4202gen10, ch4202gen11, ch4202gen12, ch4202gen13,
    ch4202gen14, ch4202gen15, ch4202gen16, ch4202gen17, ch4202gen18, ch4202gen19, ch4202gen20,
    ch4202gen21, ch4202gen22, ch4202gen23, ch4202gen24]

theorem chkHex_k : chkHex = true := by
  rw [chkHex, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨ch4202hexLab, dist4202⟩, ?_⟩
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have e : permutesHex blockGens[k] = hexGenK k := by
    rw [hexGenK, strictB_eq', strictB_eq', List.getD_eq_getElem _ _ hk,
      permutesHex_eq hexLt4202]
  rw [e]
  rw [blockGens_length4202] at hk
  exact ch4202gen_all k hk

theorem odd_codes4202 :
    (oddPerms.map RN.enc).map rnc7 = [sigC 12, sigC 13, sigC 14, sigC 15, sigC 16] := by
  simp only [oddPerms, List.map_cons, List.map_nil]
  rw [code_sig4202 (by norm_num : 12 < 32), code_sig4202 (by norm_num : 13 < 32),
    code_sig4202 (by norm_num : 14 < 32), code_sig4202 (by norm_num : 15 < 32),
    code_sig4202 (by norm_num : 16 < 32)]

theorem rnc7_odd4202 {k : ℕ} (hk : k < 5) :
    rnc7 (RN.enc (oddPerms.getD k 1)) = [sigC 12, sigC 13, sigC 14, sigC 15, sigC 16].getD k 0 := by
  interval_cases k <;> simp only [oddPerms, List.getD_cons_zero, List.getD_cons_succ] <;>
    exact code_sig4202 (by norm_num)

theorem chkWords_k : chkWords = true := by
  have hw := ch4202words
  rw [wordsChk] at hw
  simp only [strictB_eq'] at hw
  rw [wordsCore] at hw
  simp only [brec_and, brec_not4202, Bool.and_eq_true, bnot_true4202, nbeq_iff, allR_eq,
    List.all_eq_true, List.mem_range] at hw
  obtain ⟨h1, h2, h3, h4⟩ := hw
  simp only [chkWords, bne, beq_rnc7 h77, Bool.and_eq_true, bnot_true4202, nbeq_iff,
    List.all_eq_true, List.mem_range, rnc7_evalW, odd_codes4202, List.map_cons, List.map_nil,
    rnc7_phiRN hexLt4202, rnc7_one h77]
  exact ⟨⟨⟨h1, h2⟩, h3⟩, fun k hk => (rnc7_odd4202 hk).trans (h4 k hk)⟩

theorem t_codes4202 : tPerms.map code7 = [sigC 28, sigC 29, sigC 30, sigC 17] := by
  rw [tPerms, List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
    code7_sig4202 (by norm_num : 28 < 32), code7_sig4202 (by norm_num : 29 < 32),
    code7_sig4202 (by norm_num : 30 < 32), code7_sig4202 (by norm_num : 17 < 32)]

theorem chkT_k : chkT = true := by
  have hT := ch4202t
  rw [tChk] at hT
  simp only [strictB_eq'] at hT
  rw [tCore, ← t_codes4202] at hT
  simp only [brec_and, Bool.and_eq_true, nbeq_iff, allA_eq', List.all_eq_true] at hT
  obtain ⟨h1, h2, h3, h4⟩ := hT
  rw [chkT, elts, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq,
    ← closedK7_eq h77, ← size_bfsK7 h77 tPerms 64]
  refine ⟨⟨⟨h1, h2⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    rw [contains_bfsK7 h77, code_sig4202 (by have := List.mem_range.1 hj; omega)]
    exact h3 _ (List.mem_map.2 ⟨j, hj, rfl⟩)
  · rw [List.all_eq_true]
    intro g hg
    rw [contains_bfsK7 h77, rnc7_phiRN hexLt4202]
    exact h4 _ (List.mem_map.2 ⟨g, hg, rfl⟩)

theorem ch4202class_all : ∀ j < 6, classK j = true := by
  intro j hj
  interval_cases j
  exacts [ch4202class0, ch4202class1, ch4202class2, ch4202class3, ch4202class4, ch4202class5]

theorem fix_phi4202 (g : Perm (Fin 22)) :
    (strictB (gimg g) fun G => fixK (phiK hexP (fd (nat_lit 5) G))) = fix0 (phiRN g) := by
  rw [strictB_eq']
  exact (fix0_eq _ _ (phiRN_val hexLt4202 g)).symm

theorem pres_phi4202 (g : Perm (Fin 22)) :
    (strictB (gimg g) fun G => presK (phiK hexP (fd (nat_lit 5) G))) = presI5 (phiRN g) := by
  rw [strictB_eq']
  exact (presI5_eq _ _ (phiRN_val hexLt4202 g)).symm

theorem chkClass_k : chkClass = true := by
  rw [chkClass, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun j hj => ?_, fun g hg => ?_⟩
  · have h := ch4202class_all j (List.mem_range.1 hj)
    rw [classK, strictB_eq', brec_or, brec_or, allA_eq', allA_eq'] at h
    simp only [fix_phi4202, pres_phi4202] at h
    rw [nat_beq4202, ← Bool.or_assoc] at *
    exact h
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    have hj' := List.mem_range.1 hj
    have hp := ch4202p0
    rw [p0Chk, allR_eq, List.all_eq_true] at hp
    have h := hp j hj
    rw [brec_and] at h
    have hv : ∀ i : Fin 77, ((RN.enc (sigPerm (17 + j))).val[i] : ℕ) =
        (sigData.getD (17 + j) []).getD i 0 := fun i => by
      rw [RN.enc_get]
      exact sigPerm_val4202 (by omega) i
    rw [fix0_eq _ (fun i => (sigData.getD (17 + j) []).getD i 0) hv,
      presI5_eq _ (fun i => (sigData.getD (17 + j) []).getD i 0) hv]
    exact h

theorem chk4202 :
    chkSig = true ∧ chkHex = true ∧ chkWords = true ∧ chkT = true ∧ chkClass = true :=
  ⟨chkSig_k, chkHex_k, chkWords_k, chkT_k, chkClass_k⟩

end CertificateChecks.KernelJ4M2

end

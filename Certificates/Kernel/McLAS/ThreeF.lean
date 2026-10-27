module

public import Certificates.Kernel.McLAS.F6108
public import Certificates.Kernel.McLAS.F6109
public import Certificates.Kernel.McLAS.ThreeChk
public import Certificates.Kernel.Sporadic.OddCore.McLTG
public import CFSG.Sporadic.Recognition.McLASThreeCount
public import CFSG.Sporadic.Recognition.LyonsLocalMcLPair
public import CFSG.Sporadic.SmallOddCore.McL
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.Sporadic.Recognition.McLASEnum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLAS

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KS.McLAS Subgroup
open CFSG.KS.Prim (canonK invEqK)

local notation "⟪" p "⟫" => tabT (unpack 275 9 p)

theorem rep_eq {T : Table} {g h : Equiv.Perm (Fin 275)} (hg : Rep 275 T g) (hh : Rep 275 T h) :
    g = h :=
  (tblEq_iff_eq hg hh).1 (CFSG.Sporadic.Schreier.tblEq_iff.2 fun _ _ => rfl)

theorem rep_pk {X XI : Nat} (hX : Cn X) (hinv : invEqK 275 9 (mask 9) (275 * 9) X XI = true) :
    Rep 275 ⟪X⟫ (tp 275 ⟪X⟫) :=
  rep_tp (permOK_unpack hX hinv)

theorem rep_pc {X Y : Nat} (hX : Cn X) (hY : Cn Y) {g h : Equiv.Perm (Fin 275)}
    (hg : Rep 275 ⟪X⟫ g) (hh : Rep 275 ⟪Y⟫ h) : Rep 275 ⟪pcK X Y⟫ (g * h) := by
  have := Rep.compT hg hh
  rwa [compT_unpack hX hY] at this

theorem eq_of_beq {X Y : Nat} {g h : Equiv.Perm (Fin 275)} (hg : Rep 275 ⟪X⟫ g)
    (hh : Rep 275 ⟪Y⟫ h) (e : Nat.beq X Y = true) : g = h := by
  rw [Nat.eq_of_beq_eq_true e] at hg
  exact rep_eq hg hh

theorem ord3K_iff {X : Nat} (hX : Cn X) {g : Equiv.Perm (Fin 275)} (hg : Rep 275 ⟪X⟫ g) :
    ord3K X = true ↔ orderOf g = 3 := by
  rw [← ordTest_iff_perm hg (by norm_num : 0 < 3), ordTest_eq hX 3]
  have hd : divParts 3 = [1] := by decide
  rw [hd]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  unfold ord3K
  cases Nat.beq (pwK 3 X) idK <;> cases Nat.beq (pwK 1 X) idK <;> rfl

theorem commK_iff {X Y : Nat} (hX : Cn X) (hY : Cn Y) {g h : Equiv.Perm (Fin 275)}
    (hg : Rep 275 ⟪X⟫ g) (hh : Rep 275 ⟪Y⟫ h) :
    CFSG.KS.McLAS.commK X Y = true ↔ g * h = h * g := by
  rw [← commTT_iff hg hh, commTT_unpack hX hY]
  rfl

theorem fix_eq {X : Nat} (hX : Cn X) {g : Equiv.Perm (Fin 275)} (hg : Rep 275 ⟪X⟫ g) :
    fixedPtNum g = fixK X := by
  rw [← CFSG.Sporadic.Recognition.McLAS.fixedPtCount_eq hg,
    CertificateChecks.KernelMcLAS.fixedPtCount_eq hX]

theorem inRowK_spec {S : Nat → Nat} {c i : Nat} (h : inRowK S c i = true) :
    ∃ j < c, r32 S j = i := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hall : allN c (fun j => bIf(Nat.beq (r32 S j) i, false, true)) = true := by
    refine CFSG.KS.Raw.Orb.allN_iff.2 fun j hj => ?_
    have e : Nat.beq (r32 S j) i = false := Bool.eq_false_iff.2 fun h => hne j hj (Nat.eq_of_beq_eq_true h)
    rw [e]
  unfold inRowK at h
  rw [hall] at h
  exact Bool.false_ne_true h

theorem slice_at {F : Nat → Bool} {cnt NS : Nat} (hc : cnt ≤ 200 * NS)
    (h : ∀ s < NS, slK cnt F (Nat.mul s 200) 200 = true) : ∀ i < cnt, F i = true := by
  intro i hi
  have hs := h (i / 200) (by omega)
  have h1 : Nat.mul (i / 200) 200 ≤ i := Nat.div_mul_le_self i 200
  have h2 : i < Nat.mul (i / 200) 200 + 200 := by
    change i < i / 200 * 200 + 200
    omega
  exact slK_spec hs i h1 h2 hi

theorem lt_of_chain {f : ℕ → ℕ} {N : ℕ} (h : ∀ j, j + 1 < N → f j < f (j + 1)) :
    ∀ a b, a < b → b < N → f a < f b := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h1 | h1
    · exact (ih h1 (by omega)).trans (h b hb)
    · subst h1
      exact h a hb

theorem hD : GroupData 275 mclP mclPGTbls mclGen mclSift := mcl_groupData

theorem pgInv_ok {l : Nat} (hl : l < mclPGTbls.size) :
    invOK 275 mclPGTbls[l]! mclPGInvTbls[l]! = true := by
  have hl2 : l < 2 := by simpa [mclPGTbls] using hl
  obtain ⟨-, hg⟩ := tabs_pg
  obtain ⟨-, hgi⟩ := tabs_pgi
  have h := invOK_unpack (hg l hl2).2 (hgi l hl2).2 (fa.2.2.2.1 l hl2).2.1
  rwa [← (hg l hl2).1, ← (hgi l hl2).1] at h

theorem hpgi : ∀ l < mclPGTbls.size, Rep 275 mclPGInvTbls[l]! (mclGen l)⁻¹ :=
  fun l hl => Rep.inv_of_invOK (hD.rep l hl) (pgInv_ok hl)

theorem hgP : ∀ l < mclPGTbls.size,
    Rep 275 mclPGTbls[l]! (mclGen l) ∧ Rep 275 mclPGInvTbls[l]! (mclGen l)⁻¹ ∧ mclGen l ∈ mclP :=
  fun l hl => ⟨hD.rep l hl, hpgi l hl, hD.mem hl⟩

theorem pk_mem {X XI : Nat} (hX : Cn X) (hinv : invEqK 275 9 (mask 9) (275 * 9) X XI = true)
    (hs : sK X = true) : tp 275 ⟪X⟫ ∈ mclP := by
  have h := (hD.sift _ _ (rep_pk hX hinv)).1
  rw [sift_eq hX] at h
  exact h hs

theorem tt_rep' {k : Nat} (hk : k < 11) : Rep 275 ⟪TT.F k⟫ (tp 275 (threeTbl k)) := by
  generalize hg : tp 275 (threeTbl k) = g
  have h := rep_tp (n := 275) (T := threeTbl k) (by
    rw [tabTT hk]
    exact permOK_unpack (TTc hk) (TTinv hk))
  rw [hg, tabTT hk] at h
  exact h

theorem tt_rep {k : Nat} (hk : k < 11) : Rep 275 (threeTbl k) (tp 275 (threeTbl k)) :=
  rep_tp (by rw [tabTT hk]; exact permOK_unpack (TTc hk) (TTinv hk))

theorem tt_eq {k : Nat} (hk : k < 11) : tp 275 (threeTbl k) = tp 275 ⟪TT.F k⟫ :=
  rep_eq (tt_rep' hk) (rep_pk (TTc hk) (TTinv hk))

theorem tt_mem {k : Nat} (hk : k < 11) (hs : sK (TT.F k) = true) : tp 275 (threeTbl k) ∈ mclP := by
  rw [tt_eq hk]
  exact pk_mem (TTc hk) (TTinv hk) hs

theorem tt_ord {k : Nat} (hk : k < 11) (h : ord3K (TT.F k) = true) :
    orderOf (tp 275 (threeTbl k)) = 3 :=
  (ord3K_iff (TTc hk) (tt_rep' hk)).1 h

theorem tt_cent {k l : Nat} (hk : k < 11) (hl : l < 11) (hs : sK (TT.F l) = true)
    (hc : CFSG.KS.McLAS.commK (TT.F l) (TT.F k) = true) :
    tp 275 ⟪TT.F l⟫ ∈ mclP ⊓ centralizer ({tp 275 (threeTbl k)} : Set (Equiv.Perm (Fin 275))) :=
  mem_inf.2 ⟨pk_mem (TTc hl) (TTinv hl) hs, mem_centralizer_singleton_iff.2
    ((commK_iff (TTc hl) (TTc hk) (rep_pk (TTc hl) (TTinv hl)) (tt_rep' hk)).1 hc)⟩

theorem cg₁_get {l : Nat} (hl : l < 3) : threeRow₁.centGens.toArray[l]! = ⟪TT.F l⟫ := by
  rw [cg_eq]
  interval_cases l <;> rfl

theorem cg₂_eq : threeRow₂.centGens.toArray = #[⟪TT.F 3⟫, ⟪TT.F 4⟫, ⟪TT.F 5⟫] := by
  have h3 := tabTT (k := 3) (by norm_num)
  have h4 := tabTT (k := 4) (by norm_num)
  have h5 := tabTT (k := 5) (by norm_num)
  change #[threeTbl 3, threeTbl 4, threeTbl 5] = _
  rw [h3, h4, h5]

theorem cg₂_get {l : Nat} (hl : l < 3) : threeRow₂.centGens.toArray[l]! = ⟪TT.F (l + 3)⟫ := by
  rw [cg₂_eq]
  interval_cases l <;> rfl

theorem cg_mem_of {A : Array Table} {c : Table} (hc : c ∈ A) : ∃ l < A.size, A[l]! = c := by
  obtain ⟨l, hl, e⟩ := Array.getElem_of_mem hc
  exact ⟨l, hl, by rw [getElem!_pos A l hl, e]⟩

theorem cg₁_props : ∀ c ∈ threeRow₁.centGens.toArray, Rep 275 c (tp 275 c) ∧
    tp 275 c ∈ mclP ⊓ centralizer ({tp 275 (threeTbl 0)} : Set (Equiv.Perm (Fin 275))) := by
  have hk : ∀ k < 3, sK (TT.F k) = true ∧ CFSG.KS.McLAS.commK (TT.F k) (TT.F 0) = true := by
    decide +kernel
  intro c hc
  obtain ⟨l, hl, rfl⟩ := cg_mem_of hc
  have hl3 : l < 3 := hl
  rw [cg₁_get hl3]
  exact ⟨rep_pk (TTc (by omega)) (TTinv (by omega)),
    tt_cent (by norm_num) (by omega) (hk l hl3).1 (hk l hl3).2⟩

theorem cg₂_props : ∀ c ∈ threeRow₂.centGens.toArray, Rep 275 c (tp 275 c) ∧
    tp 275 c ∈ mclP ⊓ centralizer ({tp 275 (threeTbl 3)} : Set (Equiv.Perm (Fin 275))) := by
  have hk : ∀ k < 3, sK (TT.F (k + 3)) = true ∧
      CFSG.KS.McLAS.commK (TT.F (k + 3)) (TT.F 3) = true := by
    decide +kernel
  intro c hc
  obtain ⟨l, hl, rfl⟩ := cg_mem_of hc
  have hl3 : l < 3 := hl
  rw [cg₂_get hl3]
  exact ⟨rep_pk (TTc (by omega)) (TTinv (by omega)),
    tt_cent (by norm_num) (by omega) (hk l hl3).1 (hk l hl3).2⟩

theorem k_r3a : penumHdK (TT.F 0) R3A.cnt 924000 R3A.T R3A.PL = true := by quickRfl

theorem recR3A : conjClosureH 275 mclPGTbls mclPGInvTbls (threeTbl 0) 924000 =
      hRec 275 9 R3A.cnt R3A.T R3A.PL ∧
    conjTreeOK 275 mclPGTbls mclPGInvTbls (threeTbl 0) (hRec 275 9 R3A.cnt R3A.T R3A.PL).1
      (hRec 275 9 R3A.cnt R3A.T R3A.PL).2.1 (hRec 275 9 R3A.cnt R3A.T R3A.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 R3A.cnt R3A.T R3A.PL).1.toList = true :=
  conjH_sound (k := 2) (X := TT.F 0) hn tabs_pg tabs_pgi (tabTT (by norm_num)) k_r3a r3_spec.1
    r3_spec.2

theorem recRK : mulClosureH 275 threeRow₁.centGens.toArray 924000 =
      hRec 275 9 RK.cnt RK.T RK.PL ∧
    mulTreeOK 275 threeRow₁.centGens.toArray (hRec 275 9 RK.cnt RK.T RK.PL).1
      (hRec 275 9 RK.cnt RK.T RK.PL).2.1 (hRec 275 9 RK.cnt RK.T RK.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 RK.cnt RK.T RK.PL).1.toList = true :=
  mulH_sound (k := 3) hn (fun j hj => (f6108.1 j hj).1)
    (tabs_cg RK.GI fun j hj => (f6108.1 j hj).2.1) f6108.2.2.1 rk_spec.1 rk_spec.2

theorem k_rl : bAnd(allN 3 (fun j => bAnd(Nat.beq (RL.G j) McLAS.idK,
      Nat.beq (RL.GI j) (TT.F (Nat.add j 3)))), penumHdK McLAS.idK RL.cnt 1000 RL.T RL.PL) =
    true := by
  quickRfl

theorem recRL : mulClosureH 275 threeRow₂.centGens.toArray 1000 =
      hRec 275 9 RL.cnt RL.T RL.PL ∧
    mulTreeOK 275 threeRow₂.centGens.toArray (hRec 275 9 RL.cnt RL.T RL.PL).1
      (hRec 275 9 RL.cnt RL.T RL.PL).2.1 (hRec 275 9 RL.cnt RL.T RL.PL).2.2 = true ∧
    hkeysDistinct 275 (hRec 275 9 RL.cnt RL.T RL.PL).1.toList = true := by
  have h := k_rl
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hG : ∀ j < 3, RL.G j = McLAS.idK ∧ RL.GI j = TT.F (j + 3) := by
    intro j hj
    have := allN_spec h1 j hj
    simp only [bAnd_iff, Nat.beq_eq] at this
    exact this
  have hc : RL.cnt ≤ 200 * 5 := by
    change 972 ≤ 1000
    norm_num
  have hrl := rec_spec (cnt := RL.cnt) (NS := 5) hc CertificateChecks.KernelMcLAS.ThreeChk.rl_all
  have htabs : TabsOK 275 9 3 RL.GI threeRow₂.centGens.toArray := by
    rw [cg₂_eq]
    refine ⟨rfl, fun j hj => ?_⟩
    rw [(hG j hj).2]
    refine ⟨?_, TTc (by omega)⟩
    interval_cases j <;> rfl
  exact mulH_sound (k := 3) hn (fun j hj => (hG j hj).1) htabs h2 hrl.1 hrl.2

theorem cnts : R3A.cnt = 30800 ∧ RK.cnt = 29160 ∧ RL.cnt = 972 ∧
    CertificateChecks.KernelSpor.McLTT.cnt = 729 := ⟨rfl, rfl, rfl, rfl⟩

theorem rk_elts : ∀ k < RK.cnt, ∃ c ∈ closure (tp 275 '' {x | x ∈ threeRow₁.centGens.toArray}),
    Rep 275 ⟪RK.T k⟫ c := by
  intro k hk
  have hga : ∀ l < threeRow₁.centGens.toArray.size, Rep 275 threeRow₁.centGens.toArray[l]!
      (tp 275 threeRow₁.centGens.toArray[l]!) ∧ tp 275 threeRow₁.centGens.toArray[l]! ∈
        closure (tp 275 '' {x | x ∈ threeRow₁.centGens.toArray}) := fun l hl =>
    ⟨(cg₁_props _ (getElem!_mem_array hl)).1, subset_closure ⟨_, getElem!_mem_array hl, rfl⟩⟩
  have h := mulTreeOK_spec (by norm_num) _ (gg := fun l => tp 275 threeRow₁.centGens.toArray[l]!)
    hga recRK.2.1 k (by rw [hRec_size]; exact hk)
  rwa [hRec_get hk] at h

theorem rk_inj {k k' : Nat} (hk : k < RK.cnt) (hk' : k' < RK.cnt)
    (e : tablePerm 275 ⟪RK.T k⟫ = tablePerm 275 ⟪RK.T k'⟫) : k = k' := by
  refine hkeyK_inj rk_spec.2 k hk k' hk' ?_
  obtain ⟨c, -, hc⟩ := rk_elts k hk
  obtain ⟨c', -, hc'⟩ := rk_elts k' hk'
  rw [tablePerm_eq hc, tablePerm_eq hc'] at e
  subst e
  have h1 := hkey_tabT (rk_canon hk)
  have h2 := hkey_tabT (rk_canon hk')
  have e2 : hkey 275 ⟪RK.T k⟫ = hkey 275 ⟪RK.T k'⟫ := by
    rw [hkey_eq_hkeyOf hc, hkey_eq_hkeyOf hc']
  rw [← h1, ← h2, e2]

theorem x1_mem : tp 275 (threeTbl 0) ∈ mclP := tt_mem (by norm_num) (by quickRfl)

theorem x1_ord : orderOf (tp 275 (threeTbl 0)) = 3 := tt_ord (by norm_num) (by quickRfl)

theorem x1_fix : fixedPtNum (tp 275 (threeTbl 0)) = 5 := by
  rw [fix_eq (TTc (k := 0) (by norm_num)) (tt_rep' (by norm_num))]
  exact f6108.2.2.2.2.2.2.2.1

theorem row₁_facts : ElemFacts 275 mclP 3 threeRow₁ := by
  refine elemFacts_of_bounds (r := threeRow₁) (NP := 898128000) (tt_rep (by norm_num)) x1_ord x1_mem
    (fun c hc => (cg₁_props c hc).2) ?_ ?_ card_mclP (by change 30800 * 29160 = 898128000; norm_num)
  · have := le_card_closure_of_mulTree (by norm_num) (fun c hc => (cg₁_props c hc).1) recRK.2.1
      recRK.2.2
    rw [hRec_size] at this
    exact this
  · have := le_ncard_conjClass_of_conjTree (P := mclP) hgP (tt_rep (k := 0) (by norm_num))
      recR3A.2.1 recR3A.2.2
    rw [hRec_size] at this
    exact this

theorem r3a_cover : ∀ y ∈ conjClass mclP (tp 275 (threeTbl 0)),
    ∃ k < R3A.cnt, Rep 275 ⟪R3A.T k⟫ y := by
  intro y hy
  have hcls : (conjClass mclP (tp 275 (threeTbl 0))).ncard ≤
      (hRec 275 9 R3A.cnt R3A.T R3A.PL).1.size := by
    rw [hRec_size]
    exact le_of_eq row₁_facts.cls
  have hc := conjClosure_cover hD hpgi (tt_rep (k := 0) (by norm_num)) recR3A.2.1 recR3A.2.2 hcls
  obtain ⟨k, hk, hrep⟩ := hc.2 y hy
  rw [hRec_size] at hk
  rw [hRec_get hk] at hrep
  exact ⟨k, hk, hrep⟩

theorem r3a_elts : ∀ k < R3A.cnt,
    ∃ c ∈ mclP, Rep 275 ⟪R3A.T k⟫ (c * tp 275 (threeTbl 0) * c⁻¹) := by
  intro k hk
  have h := conjTreeOK_spec mclP hgP (tt_rep (k := 0) (by norm_num)) recR3A.2.1 k
    (by rw [hRec_size]; exact hk)
  rwa [hRec_get hk] at h

theorem fact3 : (Nat.card mclP).factorization 3 = 6 := by
  rw [card_mclP, show (898128000 : ℕ) = 3 ^ 6 * 1232000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem tw_spec {i : Nat} (hi : i < CertificateChecks.KernelSpor.McLTT.cnt)
    (h : bAnd(canonK 275 9 (mask 9) (275 * 9) (TW i), bAnd(canonK 275 9 (mask 9) (275 * 9) (TWI i),
      bAnd(invEqK 275 9 (mask 9) (275 * 9) (TW i) (TWI i),
      bAnd(siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) CertificateChecks.KernelCensus.McLC.LR
          CertificateChecks.KernelCensus.McLC.TRI CertificateChecks.KernelCensus.McLC.BP 5 0 (TW i),
        Nat.beq (pcK (TW i) (CertificateChecks.KernelSpor.McLTT.T i))
          (pcK (TT.F 3) (TW i)))))) = true)
    {u : Equiv.Perm (Fin 275)} (hu : Rep 275 ⟪CertificateChecks.KernelSpor.McLTT.T i⟫ u) :
    ∃ w ∈ mclP, u = w * tp 275 (threeTbl 3) * w⁻¹ := by
  obtain ⟨hw, h1⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h1
  obtain ⟨hinv, h3⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨hs, he⟩ := (bAnd_iff _ _).1 h3
  have hc := CertificateChecks.KernelSpor.McLTK.tT i hi
  have hwr := rep_pk hw hinv
  have hwP : tp 275 ⟪TW i⟫ ∈ mclP := pk_mem hw hinv hs
  have hwu := rep_pc hw hc hwr hu
  have hxw := rep_pc (TTc (k := 3) (by norm_num)) hw (tt_rep' (k := 3) (by norm_num)) hwr
  have e := eq_of_beq hwu hxw he
  refine ⟨(tp 275 ⟪TW i⟫)⁻¹, mclP.inv_mem hwP, ?_⟩
  calc u = (tp 275 ⟪TW i⟫)⁻¹ * (tp 275 ⟪TW i⟫ * u) := by group
    _ = (tp 275 ⟪TW i⟫)⁻¹ * (tp 275 (threeTbl 3) * tp 275 ⟪TW i⟫) := by rw [e]
    _ = (tp 275 ⟪TW i⟫)⁻¹ * tp 275 (threeTbl 3) * (tp 275 ⟪TW i⟫)⁻¹⁻¹ := by group

theorem cover_facts : ∀ y ∈ mclP, orderOf y = 3 →
    (∃ g ∈ mclP, y = g * tp 275 (threeTbl 0) * g⁻¹) ∨
      ∃ g ∈ mclP, y = g * tp 275 (threeTbl 3) * g⁻¹ := by
  intro y hy hy3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have F := subEnumOK_spec hD CertificateChecks.KernelSpor.McLTK.subT
  have hTcard : Nat.card ↥(closure (tp 275 '' {x | x ∈ sylowThreeGens.toArray})) =
      3 ^ (Nat.card mclP).factorization 3 := by
    rw [F.card, fact3]
    norm_num
  obtain ⟨x, hxP, hu⟩ := exists_conj_mem_of_card_sylow F.le hTcard hy hy3
  have hu3 : orderOf (x⁻¹ * y * x) = 3 := by
    rw [← hy3]
    have := (MulAut.conj x⁻¹).orderOf_eq y
    simpa using this
  obtain ⟨i, hi, hrep⟩ := F.enum.cover _ hu
  have eE : (mulClosureH 275 sylowThreeGens.toArray 800).1 =
      (hRec 275 9 CertificateChecks.KernelSpor.McLTT.cnt CertificateChecks.KernelSpor.McLTT.T
        CertificateChecks.KernelSpor.McLTT.PL).1 := by
    have := CertificateChecks.KernelSpor.McLTK.eT.1
    unfold enumT at this
    rw [this]
  rw [eE, hRec_size] at hi
  rw [eE, hRec_get hi] at hrep
  have hc := CertificateChecks.KernelSpor.McLTK.tT i hi
  have htc := slice_at (cnt := CertificateChecks.KernelSpor.McLTT.cnt) (NS := 4)
    (by rw [cnts.2.2.2]; norm_num) CertificateChecks.KernelMcLAS.ThreeChk.tc_all i hi
  unfold tcK at htc
  rw [CFSG.KS.PEnum.strictB_app', (ord3K_iff hc hrep).2 hu3] at htc
  have back : ∀ c : Equiv.Perm (Fin 275), x⁻¹ * y * x = c → y = x * c * x⁻¹ := fun c h => by
    rw [← h]
    group
  cases ha : atK R3A.cnt R3A.T TinA i (CertificateChecks.KernelSpor.McLTT.T i) with
  | true =>
    left
    unfold atK at ha
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 ha
    have hq : r32 TinA i < R3A.cnt := Nat.le_of_ble_eq_true h1
    obtain ⟨c, hc, hcr⟩ := r3a_elts _ hq
    rw [Nat.eq_of_beq_eq_true h2] at hcr
    have e := rep_eq hrep hcr
    refine ⟨x * c, mclP.mul_mem hxP hc, ?_⟩
    rw [back _ e]
    group
  | false =>
    right
    rw [ha] at htc
    obtain ⟨w, hwP, hw⟩ := tw_spec hi htc hrep
    refine ⟨x * w, mclP.mul_mem hxP hwP, ?_⟩
    rw [back _ hw]
    group

theorem card_A_comm : (conjClass mclP (tp 275 (threeTbl 0)) ∩
    {y | tp 275 (threeTbl 3) * y = y * tp 275 (threeTbl 3)}).ncard ≤ 20 := by
  classical
  set f : ℕ → Equiv.Perm (Fin 275) := fun j => tablePerm 275 ⟪R3A.T (r32 S20 j)⟫
  have hsub : conjClass mclP (tp 275 (threeTbl 0)) ∩
      {y | tp 275 (threeTbl 3) * y = y * tp 275 (threeTbl 3)} ⊆
        (((Finset.range 20).image f : Finset _) : Set (Equiv.Perm (Fin 275))) := by
    rintro y ⟨hyA, hyc⟩
    obtain ⟨k, hk, hrep⟩ := r3a_cover y hyA
    have hcm := slice_at (cnt := R3A.cnt) (NS := 154) (by rw [cnts.1])
      CertificateChecks.KernelMcLAS.ThreeChk.cm_all k hk
    unfold cmK at hcm
    have hcomm : CFSG.KS.McLAS.commK (R3A.T k) (TT.F 3) = true :=
      (commK_iff (r3_canon hk) (TTc (k := 3) (by norm_num)) hrep (tt_rep' (by norm_num))).2
        (Set.mem_setOf_eq ▸ hyc).symm
    rw [hcomm] at hcm
    obtain ⟨j, hj, hjk⟩ := inRowK_spec hcm
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    refine ⟨j, hj, ?_⟩
    change tablePerm 275 ⟪R3A.T (r32 S20 j)⟫ = y
    rw [hjk, tablePerm_eq hrep]
  calc _ ≤ (((Finset.range 20).image f : Finset _) : Set (Equiv.Perm (Fin 275))).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ((Finset.range 20).image f).card := Set.ncard_coe_finset _
    _ ≤ (Finset.range 20).card := Finset.card_image_le
    _ = 20 := Finset.card_range 20

theorem b600_spec : ∀ j < 600, r32 B600 j < RK.cnt ∧ ord3K (RK.T (r32 B600 j)) = true ∧
    fixK (RK.T (r32 B600 j)) ≠ 5 ∧ (j + 1 < 600 → r32 B600 j < r32 B600 (j + 1)) := by
  have hb : ∀ j < 600, bK j = true := slice_at (cnt := 600) (NS := 3) (by norm_num)
    CertificateChecks.KernelMcLAS.ThreeChk.b_all
  intro j hj
  have h := hb j hj
  unfold bK at h
  rw [CFSG.KS.PEnum.strictB_app'] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [CFSG.KS.PEnum.strictB_app'] at h2
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h4
  refine ⟨Nat.le_of_ble_eq_true h1, h3, fun e => ?_, fun hj1 => ?_⟩
  · rw [e] at h5
    exact Bool.false_ne_true h5
  · have hlt : Nat.blt (Nat.succ j) 600 = true := Nat.blt_eq.mpr hj1
    rw [hlt] at h6
    exact Nat.le_of_ble_eq_true h6

theorem b600_mem {j : Nat} (hj : j < 600) :
    tablePerm 275 ⟪RK.T (r32 B600 j)⟫ ∈ conjClass mclP (tp 275 (threeTbl 3)) ∩
      {w | tp 275 (threeTbl 0) * w = w * tp 275 (threeTbl 0)} := by
  obtain ⟨hi, ho, hf, -⟩ := b600_spec j hj
  obtain ⟨c, hcK, hcr⟩ := rk_elts _ hi
  rw [tablePerm_eq hcr]
  rw [row₁_facts.gens] at hcK
  have hcP : c ∈ mclP := (mem_inf.1 hcK).1
  have hc3 : orderOf c = 3 := (ord3K_iff (rk_canon hi) hcr).1 ho
  have hcf : fixedPtNum c ≠ 5 := by
    rw [fix_eq (rk_canon hi) hcr]
    exact hf
  refine ⟨?_, (mem_centralizer_singleton_iff.1 (mem_inf.1 hcK).2).symm⟩
  rcases cover_facts c hcP hc3 with ⟨g, -, hg⟩ | hg
  · exfalso
    apply hcf
    rw [hg, fixedPtNum_conj, x1_fix]
  · exact hg

theorem card_B_comm : 600 ≤ (conjClass mclP (tp 275 (threeTbl 3)) ∩
    {w | tp 275 (threeTbl 0) * w = w * tp 275 (threeTbl 0)}).ncard := by
  classical
  set f : ℕ → Equiv.Perm (Fin 275) := fun j => tablePerm 275 ⟪RK.T (r32 B600 j)⟫
  have hmono := lt_of_chain (f := fun j => r32 B600 j) (N := 600)
    fun j hj => (b600_spec j (by omega)).2.2.2 hj
  have hinj : Set.InjOn f (Set.Iio 600) := by
    intro a ha b hb e
    simp only [Set.mem_Iio] at ha hb
    have h := rk_inj (b600_spec a ha).1 (b600_spec b hb).1 e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact (hmono a b hlt hb).ne h
    · exact (hmono b a hlt ha).ne h.symm
  have hsub : (((Finset.range 600).image f : Finset _) : Set (Equiv.Perm (Fin 275))) ⊆
      conjClass mclP (tp 275 (threeTbl 3)) ∩
        {w | tp 275 (threeTbl 0) * w = w * tp 275 (threeTbl 0)} := by
    intro z hz
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hz
    obtain ⟨j, hj, rfl⟩ := hz
    exact b600_mem hj
  have hcard : ((Finset.range 600).image f).card = 600 := by
    rw [Finset.card_image_of_injOn (fun a ha b hb e => hinj (by simpa using ha) (by simpa using hb) e),
      Finset.card_range]
  calc 600 = ((Finset.range 600).image f).card := hcard.symm
    _ = (((Finset.range 600).image f : Finset _) : Set (Equiv.Perm (Fin 275))).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem row₂_facts : ElemFacts 275 mclP 3 threeRow₂ := by
  refine elemFacts_of_bounds (r := threeRow₂) (NP := 898128000) (tt_rep (by norm_num))
    (tt_ord (by norm_num) (by quickRfl)) (tt_mem (by norm_num) (by quickRfl))
    (fun c hc => (cg₂_props c hc).2) ?_ ?_ card_mclP (by change 924000 * 972 = 898128000; norm_num)
  · have := le_card_closure_of_mulTree (by norm_num) (fun c hc => (cg₂_props c hc).1) recRL.2.1
      recRL.2.2
    rw [hRec_size] at this
    exact this
  · have hdc := ncard_conjClass_mul_ncard_comm mclP (tp 275 (threeTbl 0)) (tp 275 (threeTbl 3))
    have hA : (conjClass mclP (tp 275 (threeTbl 0))).ncard = 30800 := row₁_facts.cls
    rw [hA] at hdc
    have h1 := card_A_comm
    have h2 := card_B_comm
    change 924000 ≤ (conjClass mclP (tp 275 (threeTbl 3))).ncard
    nlinarith

theorem enum₁_facts : ∀ y ∈ mclP ⊓ centralizer ({tp 275 threeRow₁.rep} : Set (Equiv.Perm (Fin 275))),
    ∃ k < (mulClosureH 275 threeRow₁.centGens.toArray 924000).1.size,
      Rep 275 (mulClosureH 275 threeRow₁.centGens.toArray 924000).1[k]! y := by
  intro y hy
  rw [← row₁_facts.gens] at hy
  have hsize : Nat.card ↥(closure (tp 275 '' {x | x ∈ threeRow₁.centGens.toArray})) ≤
      (mulClosureH 275 threeRow₁.centGens.toArray 924000).1.size := by
    rw [row₁_facts.gens, row₁_facts.cent, recRK.1, hRec_size]
    exact le_refl _
  exact mulClosure_cover (n := 275) (by norm_num) (fun c hc => by
      have h := (cg₁_props c hc).1
      obtain ⟨l, hl, rfl⟩ := cg_mem_of hc
      have hl3 : l < 3 := hl
      rw [cg₁_get hl3]
      exact permOK_unpack (TTc (by omega)) (TTinv (by omega)))
    (by rw [recRK.1]; exact recRK.2.1) (by rw [recRK.1]; exact recRK.2.2) hsize y hy

theorem threeFacts : ThreeFacts :=
  ⟨row₁_facts, row₂_facts, cover_facts, enum₁_facts⟩

end CertificateChecks.KernelMcLAS

end

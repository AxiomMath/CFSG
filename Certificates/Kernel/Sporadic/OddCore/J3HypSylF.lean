module

public import Certificates.Kernel.Sporadic.OddCore.J3HypSyl
public import CFSG.Certificates.Kernel.Spor.MulHFSound
public import CFSG.Certificates.Kernel.Spor.MulHPcSound
public import CFSG.Certificates.Kernel.Spor.PEnumCSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Certificates.Kernel.Sporadic.OddCore.J3FourGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J3Check

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3HypSyl

open CFSG.EvenSporadicStandard.HypOne.J3 CFSG.EvenSporadicStandard.Fin76b.J3
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KS.Join
open CertificateChecks.KernelSpor.OddCore

theorem base : szOK 6156 13 = true ∧ cK (pidn 6156 13) = true ∧
    CFSG.KS.Prim.idK 6156 13 (mask 13) = true ∧ cK (J3CentP 9) = true ∧
    allN 3 (fun j => bAnd(cK (J3HS.GI j), bAnd(Nat.beq (J3HS.GI j) (J3HypP (Nat.add j 1)),
      Nat.beq (J3HS.G j) (pidn 6156 13)))) = true ∧
    Nat.beq J3HS.cnt 128 = true ∧ penumHdK (pidn 6156 13) J3HS.cnt 128 J3HS.T J3HS.PL = true := by
  simpa only [bAnd_iff] using base_ok

theorem hidc : canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13) = true := base.2.1

theorem hid : idT 6156 = tabT (unpack 6156 13 (pidn 6156 13)) := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem hcnt : J3HS.cnt = 128 := Nat.eq_of_beq_eq_true base.2.2.2.2.2.1

theorem gen {j : Nat} (hj : j < 3) : cK (J3HS.GI j) = true ∧ J3HS.GI j = J3HypP (j + 1) ∧
    J3HS.G j = pidn 6156 13 := by
  have h := allN_spec base.2.2.2.2.1 j hj
  simp only [bAnd_iff] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem hyp_tab {k : Nat} (hk : k < 12) : hypTbl k = tabT (unpack 6156 13 (J3HypP k)) := by
  have h := hexT_join_sound (d := 4) (n₀ := 513) (w := 13) (c := 12) (N := 12) J3HypT.all hyp_join
    (by norm_num) k hk
  rw [← J3HypT.eq] at h
  rw [← tabT_natArr (hypTbl k)]
  exact congrArg tabT h

theorem sg_eq : sgP0 = ((List.range 3).map fun j => tabT (unpack 6156 13 (J3HS.GI j))).toArray := by
  unfold sgP0
  rw [hyp_tab (by norm_num), hyp_tab (by norm_num), hyp_tab (by norm_num),
    ← (gen (j := 0) (by norm_num)).2.1, ← (gen (j := 1) (by norm_num)).2.1,
    ← (gen (j := 2) (by norm_num)).2.1]
  rfl

theorem s_tabs : TabsOK 6156 13 3 J3HS.GI sgP0 := by
  refine ⟨by rw [sg_eq]; simp, fun j hj => ⟨?_, (gen hj).1⟩⟩
  rw [sg_eq, getElem!_pos _ j (by simpa using hj)]
  simp

theorem pcF_find3 {n w k cnt p c : Nat} {T G CL P S U PP : Nat → Nat} (hn : n < 2 ^ 32)
    (hp : p < n)
    (hcl : ∀ i < cnt, ∀ i' < cnt, ∃ q < cnt,
      pcomp n w (mask w) (pcNK T P i) (pcNK T P i') = pcNK T P q)
    (hM : pcMK n w (mask w) k cnt p T G P S U PP = true)
    (hF : pcFK3 w (mask w) k cnt p T G CL c = true) (hc : c < cnt * k) :
    findPtK cnt T (prodQK n w (mask w) k T G) CL c = true := by
  obtain ⟨-, -, hI, hU⟩ := pcM_spec hM
  have hK : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [Nat.mul_zero] at hc
      exact absurd hc (Nat.not_lt_zero _)
    · exact h0
  unfold pcFK3 at hF
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hF
  obtain ⟨hq, hpt⟩ := hF
  have hq' : r32 CL c < cnt := Nat.blt_eq.mp hq
  have hj : c % k < k := Nat.mod_lt _ hK
  have hi : c / k < cnt := (Nat.div_lt_iff_lt_mul hK).2 hc
  obtain ⟨-, hs, hps, -⟩ := hI _ hi
  obtain ⟨hu, eu⟩ := hU _ hj
  have eT : T (c / k) = pcNK T P (r32 S (c / k)) := by
    unfold pcNK
    rw [hps]
  obtain ⟨q, hqc, eq⟩ := hcl _ hs _ hu
  rw [← eT, ← eu] at eq
  have hpq : r32 P q < cnt := (hI q hqc).1
  have e1 : pg w (mask w) (T (r32 CL c)) p = pg w (mask w) (T (r32 P q)) p := by
    rw [Nat.eq_of_beq_eq_true hpt]
    change pg w (mask w) (T (c / k)) (pg w (mask w) (G (c % k)) p) = _
    rw [← CFSG.KS.PF.pg_pcomp hn hp, eq]
    rfl
  have e2 : r32 CL c = r32 P q := by
    rw [← (hI _ hq').2.2.2, ← (hI _ hpq).2.2.2, e1]
  unfold findPtK
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true]
  refine ⟨hq, ?_⟩
  change Nat.beq (T (r32 CL c)) (pcomp n w (mask w) (T (c / k)) (G (c % k))) = true
  rw [e2, eq]
  exact Nat.beq_refl _

theorem ntJ3_spec : ∀ r < 7, ∀ i < 2 ^ r, pcTK 6156 13 (mask 13) J3HS.T J3PcP r i = true := by
  intro r hr i hi
  have key : ∀ k, ntJ3 r k = true → 32 * k ≤ i → i < 32 * k + 32 →
      pcTK 6156 13 (mask 13) J3HS.T J3PcP r i = true := fun k h h1 h2 =>
    slK_spec h i h1 h2 (by rw [shl_one]; exact hi)
  by_cases h5 : r < 5
  · have h16 : 2 ^ r ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact key 0 (CFSG.KS.Raw.Orb.allN_iff.1 ntJ3_lo r h5) (by omega) (by omega)
  · have hi' := hi
    interval_cases r <;> norm_num at hi'
    · exact key 0 ntJ3_5 (by omega) (by omega)
    · by_cases h32 : i < 32
      · exact key 0 ntJ3_60 (by omega) (by omega)
      · exact key 1 ntJ3_61 (by omega) (by omega)

theorem rlJ3_ok {r c : Nat} (hr : r < 7) (hc : 4 * c < max r 1) : rlJ3 r c = true := by
  have hc2 : c < 2 := by omega
  by_cases h5 : r < 5
  · have e : c = 0 := by omega
    rw [e]
    exact CFSG.KS.Raw.Orb.allN_iff.1 rlJ3_lo r h5
  · interval_cases r <;> interval_cases c
    exacts [rlJ3_50, rlJ3_51, rlJ3_60, rlJ3_61]

theorem rlJ3_spec {r : Nat} (hr : r < 7) :
    canonK 6156 13 (mask 13) (6156 * 13) (pcNK J3HS.T J3PcP (2 ^ r)) = true ∧
      (∃ a < 2 ^ r, pcomp 6156 13 (mask 13) (pcNK J3HS.T J3PcP (2 ^ r))
        (pcNK J3HS.T J3PcP (2 ^ r)) = pcNK J3HS.T J3PcP a) ∧
      ∀ s < r, ∃ b < 2 ^ r,
        pcomp 6156 13 (mask 13) (pcNK J3HS.T J3PcP (2 ^ r)) (pcNK J3HS.T J3PcP (2 ^ s)) =
          pcomp 6156 13 (mask 13) (pcNK J3HS.T J3PcP b) (pcNK J3HS.T J3PcP (2 ^ r)) :=
  pcR_spec (rlJ3_ok (c := 0) hr (by omega)) (fun s hs => rlJ3_ok (c := s / 4) hr (by omega))

theorem closJ3 : ∀ i < J3HS.cnt, ∀ i' < J3HS.cnt, ∃ q < J3HS.cnt,
    pcomp 6156 13 (mask 13) (pcNK J3HS.T J3PcP i) (pcNK J3HS.T J3PcP i') = pcNK J3HS.T J3PcP q := by
  obtain ⟨h0, hc0, -, -⟩ := pcM_spec mbJ3_ok
  have H := (pc_closed (m := 7) (N := pcNK J3HS.T J3PcP) h0 hc0
    (fun r hr => (rlJ3_spec hr).1)
    (fun r hr i hi => pcT_spec (ntJ3_spec r hr i hi))
    (fun r hr => (rlJ3_spec hr).2.1)
    (fun r hr => (rlJ3_spec hr).2.2) 7 (Nat.le_refl _)).2
  have e : (2 : Nat) ^ 7 = 128 := by norm_num
  rw [e] at H
  rw [hcnt]
  exact H

theorem s_pe : ∀ i < J3HS.cnt, penumPtK 6156 13 (mask 13) (6156 * 13) true J3HS.G J3HS.GI 3
    J3HS.cnt J3HS.T J3HS.PL J3HS.POS J3HS.SRT J3HS.SRI i = true := by
  have hd := base.2.2.2.2.2.2
  unfold penumHdK at hd
  simp only [bAnd_iff] at hd
  have h0 : canonK 6156 13 (mask 13) (6156 * 13) (J3HS.T 0) = true := by
    rw [Nat.eq_of_beq_eq_true hd.2.2.1]
    exact base.2.1
  have hcl : ∀ c < J3HS.cnt * 3, findPtK J3HS.cnt J3HS.T
      (prodQK 6156 13 (mask 13) 3 J3HS.T J3HS.GI) J3HS.POS c = true := fun c hc =>
    pcF_find3 (by norm_num) (by norm_num) closJ3 mbJ3_ok
      (slK_spec clJ3 c (Nat.zero_le _) (by rw [hcnt] at hc; omega) hc) hc
  exact CFSG.KS.PEnumC.penumPtK_of_C (K := 3) (S := J3HS.GI) (CL := J3HS.POS) (Nat.le_refl _)
    (fun j hj => (gen hj).2.2) (fun _ _ => rfl) (fun j hj => (gen hj).1) h0 hcl
    (fun i hi => slK_spec peJ3 i (Nat.zero_le _) (by rw [hcnt] at hi; omega) hi)

theorem s_hs : ∀ i < J3HS.cnt,
    hsortPtK 6156 13 (mask 13) J3HS.cnt J3HS.T J3HS.HS J3HS.HSI i = true := fun i hi => by
  rw [← hsortPtKF_eq 6156 13 J3HS.cnt J3HS.T J3HS.HS J3HS.HSI i]
  exact slK_spec sHF i (Nat.zero_le _) (by omega) hi

theorem closure_eq : (mulClosureH 6156 sgP0 128).1 = (hRec 6156 13 J3HS.cnt J3HS.T J3HS.PL).1 := by
  rw [(mulH_sound base.1 (fun j hj => (gen hj).2.2) s_tabs base.2.2.2.2.2.2 s_pe s_hs).1]

@[expose] noncomputable def fE (i : Nat) : Table := tabT (unpack 6156 13 (J3HS.T i))

theorem syl_eq : sylList = ((List.range 128).map fE).toArray := by
  rw [sylList_fst, closure_eq]
  apply Array.toList_inj.1
  simp only [hRec, Array.toList_ofFn]
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map, hcnt]
  rfl

theorem hT {i : Nat} (hi : i < 128) : canonK 6156 13 (mask 13) (6156 * 13) (J3HS.T i) = true :=
  penumPt_canon (s_pe i (by rw [hcnt]; exact hi))

theorem t0_eq : t0 = tabT (unpack 6156 13 (J3CentP 9)) := tbl_unpack (by norm_num)

theorem any_mem {l : List Nat} {p q : Nat → Bool} (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem all_mem {l : List Nat} {p q : Nat → Bool} (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem facts24591 : j3CenterCheck = true := by
  have h := center_ok
  unfold centerK at h
  unfold j3CenterCheck
  rw [syl_eq, sg_eq, t0_eq]
  simp only [List.any_toArray, List.all_toArray, List.any_map, List.all_map]
  have h9 := base.2.2.2.1
  refine (congrArg₂ (· && ·) (congrArg₂ (· && ·) ?_ ?_) ?_).trans h
  · refine any_mem fun i hi => ?_
    rw [Function.comp_apply]
    beta_reduce
    rw [fE, tblEq_unpack (hT (List.mem_range.1 hi)) h9]
  · refine all_mem fun i hi => ?_
    have hi' := List.mem_range.1 hi
    rw [Function.comp_apply]
    beta_reduce
    rw [fE, tblEq_unpack (hT hi') h9, hid, tblEq_unpack (hT hi') hidc]
    refine congrArg (fun b => !b || Nat.beq (J3HS.T i) (pidn 6156 13) || Nat.beq (J3HS.T i) (J3CentP 9))
      (all_mem fun j hj => ?_)
    rw [Function.comp_apply]
    beta_reduce
    rw [commTT_unpack (hT hi') (gen (List.mem_range.1 hj)).1, pc, pc]
  · refine any_mem fun i hi => ?_
    have hi' := List.mem_range.1 hi
    rw [Function.comp_apply]
    beta_reduce
    rw [fE, compT_unpack (hT hi') (hT hi'), tblEq_unpack (canonK_pcomp (hT hi') (hT hi')) h9, pc]

end CertificateChecks.KernelSpor.J3HypSyl

end

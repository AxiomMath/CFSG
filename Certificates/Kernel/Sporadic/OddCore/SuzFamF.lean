module

public import Certificates.Kernel.Sporadic.OddCore.SuzFamK0
public import Certificates.Kernel.Sporadic.OddCore.SuzFamK1
public import Certificates.Kernel.Sporadic.OddCore.SuzFamK2
public import Certificates.Kernel.Sporadic.OddCore.SuzFamK3
public import Certificates.Kernel.Sporadic.OddCore.Suz2289
public import Certificates.Kernel.Sporadic.OddCore.Glue
public import CFSG.Certificates.Kernel.Spor.FamBFSSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Sporadic.SmallOddCore.ClassSimple
import all CFSG.Sporadic.SuzOddCore.Arrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzFamD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Row CFSG.KS.TBfs CFSG.KS.PEnum
open CFSG.KS.Mathieu CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSpor.Suz2306 CertificateChecks.KernelSpor.OddCore

theorem seed_ok : Nat.beq (SuzSeedT.F 0) (FAM 0) = true := by quickRfl

@[expose] noncomputable def ptK (e : Nat) : Bool :=
  bIf(Nat.beq e 0, true,
    strictB (DIF e) (fun j => strictB (TP e) (fun t =>
      bAnd(Nat.blt j 2080, bAnd(bIf(Nat.beq (fe e j) (fe 0 j), false, true),
      bAnd(Nat.blt (Nat.shiftRight t 1) 1782,
      bAnd(Nat.beq (pg 11 (mask 11) (bK (Nat.land t 1)) (Nat.shiftRight t 1)) e,
        Nat.blt (RK (Nat.shiftRight t 1)) (RK e))))))))

theorem pts_ok : allN 1782 ptK = true := by quickRfl

@[expose] noncomputable def sLet (l : Nat) : Nat :=
  nIf(Nat.beq l 0, B0, nIf(Nat.beq l 1, SuzMtxI 0, nIf(Nat.beq l 2, B1, SuzMtxI 1)))

@[expose] noncomputable def sL (l x : Nat) : Nat := pg 11 (mask 11) (sLet l) x

theorem let_range : allN 4 (fun l => allN 1782 (fun x => Nat.blt (sL l x) 1782)) = true := by
  quickRfl

theorem b0_ne : Bool.not (Nat.beq (pg 11 (mask 11) B0 0) 0) = true := by quickRfl

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bA (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem st_hd : tbfsHdK 1782 0 ST.cnt ST.PTS ST.POS ST.PAR ST.LAB = true := by quickRfl

theorem st_s : tbfsSlK 1782 ST.cnt 4 sL (nget [0, 1, 2, 3]) ST.PTS ST.POS ST.PAR ST.LAB ST.TI 0
    1782 = true := by quickRfl

theorem st_cnt : ST.cnt = 1782 := rfl

theorem unpack_size' (n w P : Nat) : (unpack n w P).size = n := by simp [unpack]

theorem fe_eq {d j : Nat} (hj : j < (unpack 2080 15 (FAM d)).toList.length) :
    ((unpack 2080 15 (FAM d)).toList)[j] = fe d j := by
  have hj' : j < 2080 := by rwa [Array.length_toList, unpack_size'] at hj
  rw [Array.getElem_toList, ← getElem!_pos _ j (by rw [unpack_size']; exact hj'),
    CFSG.KC.Misc.PairCount.unpack_get hj']
  rfl

theorem inc_all {d : Nat} (hd : d < 1782) : incK d = true := by
  have hs : d / 891 < 2 := by omega
  have h := IP.all (d / 891) hs
  unfold incSl at h
  have := allBlk_spec h (d % 891) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.mul 891 (d / 891)) (d % 891) = d := Nat.div_add_mod d 891
  rwa [e] at this

theorem inc_facts {d : Nat} (hd : d < 1782) :
    fe d 2079 < 22880 ∧ ∀ j < 2079, fe d j < fe d (j + 1) := by
  have h := inc_all hd
  unfold incK at h
  rw [sB, bA, Bool.and_eq_true] at h
  refine ⟨Eq.mp Nat.blt_eq h.1, fun j hj => ?_⟩
  exact Eq.mp Nat.blt_eq (CFSG.KS.allN_spec h.2 j hj)

theorem fe_mono {d : Nat} (hd : d < 1782) : ∀ i j, i < j → j < 2080 → fe d i < fe d j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    have h := (inc_facts hd).2 j (by omega)
    rcases Nat.lt_or_ge i j with a | a
    · exact lt_trans (ih a (by omega)) h
    · have : i = j := by omega
      subst this
      exact h

theorem fe_lt {d : Nat} (hd : d < 1782) {j : Nat} (hj : j < 2080) : fe d j < 22880 := by
  rcases Nat.lt_or_ge j 2079 with a | a
  · exact lt_trans (fe_mono hd j 2079 a (by omega)) (inc_facts hd).1
  · have : j = 2079 := by omega
    subst this
    exact (inc_facts hd).1

@[expose] noncomputable def famL (d : Nat) : List Nat := (unpack 2080 15 (FAM d)).toList

theorem famL_length (d : Nat) : (famL d).length = 2080 := by
  rw [famL, Array.length_toList, unpack_size']

theorem famL_get {d j : Nat} (hj : j < (famL d).length) : (famL d)[j] = fe d j := fe_eq hj

theorem famL_pairwise {d : Nat} (hd : d < 1782) : (famL d).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [famL_get, famL_get]
  exact fe_mono hd i j hij (by rw [famL_length] at hj; exact hj)

theorem strictIncr_of {L : List Nat} (h : L.Pairwise (· < ·)) : strictIncr L = true := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      have hab : a < b := List.rel_of_pairwise_cons h List.mem_cons_self
      simp only [strictIncr, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hab, ih h.of_cons⟩

theorem famL_lt {d : Nat} (hd : d < 1782) : ∀ x ∈ famL d, x < 22880 := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  rw [famL_get]
  exact fe_lt hd (by rw [famL_length] at hj; exact hj)

theorem cert_get {k x : Nat} (hk : k < 2) (hx : x < 22880) : (certArr k)[x]! = ak k x := by
  rw [certArr_eq (by omega), rowArr_get hx]
  rfl

theorem cert_inv {k x : Nat} (hk : k < 2) (hx : x < 22880) :
    rg 15 (mask 15) SuzCertI (Nat.mul 715 k) (ak k x) = x := by
  have h0 := CFSG.KS.allN_spec cert_perms k (by omega)
  unfold rpermK at h0
  have h := CFSG.KS.allN_spec h0 x hx
  rw [sB, bA, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2

theorem cert_inj {k x y : Nat} (hk : k < 2) (hx : x < 22880) (hy : y < 22880)
    (h : ak k x = ak k y) : x = y := by
  rw [← cert_inv hk hx, ← cert_inv hk hy, h]

theorem part_of {f : Nat → Bool} {b : Nat} (h : ∀ s < 14, f (Nat.add b s) = true) {s : Nat}
    (h1 : b ≤ s) (h2 : s < b + 14) : f s = true := by
  have := h (s - b) (by omega)
  rwa [Nat.add_eq, Nat.add_sub_cancel' h1] at this

theorem img_all {k d : Nat} (hk : k < 2) (hd : d < 1782) : imgK k d = true := by
  have hs : d / 64 < 28 := by omega
  have h : imgSl k (d / 64) = true := by
    interval_cases k
    · rcases Nat.lt_or_ge (d / 64) 14 with a | a
      · exact part_of (f := imgSl 0) (b := 0) (fun s hs => FP0.all s hs) (by omega) (by omega)
      · exact part_of (f := imgSl 0) (b := 14) (fun s hs => FP1.all s hs) a (by omega)
    · rcases Nat.lt_or_ge (d / 64) 14 with a | a
      · exact part_of (f := imgSl 1) (b := 0) (fun s hs => FP2.all s hs) (by omega) (by omega)
      · exact part_of (f := imgSl 1) (b := 14) (fun s hs => FP3.all s hs) a (by omega)
  unfold imgSl at h
  have := allBlk_spec h (d % 64) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.mul 64 (d / 64)) (d % 64) = d := Nat.div_add_mod d 64
  rw [e, Eq.mpr Nat.blt_eq hd] at this
  exact this

theorem img_facts {k d : Nat} (hk : k < 2) (hd : d < 1782) :
    pg 11 (mask 11) (bK k) d < 1782 ∧ ∀ j < 2080, ∃ p < 2080,
      ak k (fe d j) = fe (pg 11 (mask 11) (bK k) d) p := by
  have h := img_all hk hd
  unfold imgK at h
  simp only [sB, bA, Bool.and_eq_true] at h
  refine ⟨Eq.mp Nat.blt_eq h.1, fun j hj => ?_⟩
  have h2 := CFSG.KS.allN_spec h.2 j hj
  simp only [sB, bA, Bool.and_eq_true] at h2
  exact ⟨_, Eq.mp Nat.blt_eq h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem imgSorted_eq {k d : Nat} (hk : k < 2) (hd : d < 1782) :
    imgSorted (certArr k) (famL d) = famL (pg 11 (mask 11) (bK k) d) := by
  obtain ⟨he, himg⟩ := img_facts hk hd
  set e := pg 11 (mask 11) (bK k) d
  have hmap : (famL d).map (fun p => (certArr k)[p]!) = (famL d).map (ak k) :=
    List.map_congr_left fun p hp => cert_get hk (famL_lt hd p hp)
  unfold imgSorted
  rw [hmap]
  have hnd : ((famL d).map (ak k)).Nodup :=
    List.Nodup.map_on (fun x hx y hy hxy => cert_inj hk (famL_lt hd x hx) (famL_lt hd y hy) hxy)
      ((famL_pairwise hd).imp (fun h => Nat.ne_of_lt h))
  have hsub : (famL d).map (ak k) ⊆ famL e := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    rw [famL_get]
    obtain ⟨p, hp, hpe⟩ := himg j (by rw [famL_length] at hj; exact hj)
    rw [hpe, ← famL_get (d := e) (by rw [famL_length]; exact hp)]
    exact List.getElem_mem _
  have hperm : List.Perm ((famL d).map (ak k)) (famL e) :=
    (List.subperm_of_subset hnd hsub).perm_of_length_le (by simp [famL_length])
  refine List.Perm.eq_of_pairwise (le := fun a b => decide (a ≤ b) = true)
    (fun a b _ _ h1 h2 => by simp at h1 h2; omega)
    (List.pairwise_mergeSort (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega)
      (fun a b => by simp; omega) _)
    ((famL_pairwise he).imp fun h => by simp; omega)
    ((List.mergeSort_perm _ _).trans hperm)

@[expose] noncomputable def famRec : Array (List Nat) := Array.ofFn (n := 1782) fun d => famL d.val

theorem famRec_get {d : Nat} (hd : d < 1782) : famRec[d]! = famL d := by
  rw [getElem!_pos famRec d (by simp [famRec, hd])]
  simp [famRec]

theorem idx_get {k d : Nat} (hk : k < 2) (hd : d < 1782) :
    (#[b0Arr, b1Arr][k]!)[d]! = pg 11 (mask 11) (bK k) d := by
  interval_cases k
  · simp only [List.getElem!_toArray, List.getElem!_cons_zero]
    rw [b0Arr_eq, CFSG.KC.Misc.PairCount.unpack_get hd]
    rfl
  · simp only [List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]
    rw [b1Arr_eq, CFSG.KC.Misc.PairCount.unpack_get hd]
    rfl

theorem set_get {k : Nat} (hk : k < 2) : #[certArr 0, certArr 1][k]! = certArr k := by
  interval_cases k
  · simp only [List.getElem!_toArray, List.getElem!_cons_zero]
  · simp only [List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem fam_rec : ∀ k < (#[b0Arr, b1Arr] : Array (Array Nat)).size, ∀ d < 1782,
    famRec[(#[b0Arr, b1Arr][k]!)[d]!]! = imgSorted #[certArr 0, certArr 1][k]! famRec[d]! := by
  intro k hk d hd
  have hk' : k < 2 := by simpa using hk
  rw [idx_get hk' hd, famRec_get (img_facts hk' hd).1, famRec_get hd, set_get hk',
    imgSorted_eq hk' hd]

theorem fam_idx : ∀ k < (#[b0Arr, b1Arr] : Array (Array Nat)).size, ∀ d < 1782,
    (#[b0Arr, b1Arr][k]!)[d]! < 1782 := by
  intro k hk d hd
  have hk' : k < 2 := by simpa using hk
  rw [idx_get hk' hd]
  exact (img_facts hk' hd).1

theorem pt_facts {e : Nat} (he : e < 1782) (h0 : e ≠ 0) :
    DIF e < 2080 ∧ fe e (DIF e) ≠ fe 0 (DIF e) ∧ Nat.shiftRight (TP e) 1 < 1782 ∧
      pg 11 (mask 11) (bK (Nat.land (TP e) 1)) (Nat.shiftRight (TP e) 1) = e ∧
      RK (Nat.shiftRight (TP e) 1) < RK e := by
  have h := CFSG.KS.allN_spec pts_ok e he
  unfold ptK at h
  have hb : Nat.beq e 0 = false := by
    cases h' : Nat.beq e 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h') h0
  rw [hb] at h
  simp only [sB, bA, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨Eq.mp Nat.blt_eq h1, fun e' => ?_, Eq.mp Nat.blt_eq h3, Nat.eq_of_beq_eq_true h4,
    Eq.mp Nat.blt_eq h5⟩
  rw [e', Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem fam_reach : ∀ e < 1782, e ≠ 0 → ∃ k < (#[b0Arr, b1Arr] : Array (Array Nat)).size,
    ∃ d < 1782, (#[b0Arr, b1Arr][k]!)[d]! = e ∧ RK d < RK e := by
  intro e he h0
  obtain ⟨-, -, h3, h4, h5⟩ := pt_facts he h0
  have hk : Nat.land (TP e) 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  exact ⟨_, hk, _, h3, by rw [idx_get hk h3]; exact h4, h5⟩

theorem seed_eq : famRec[0]! = familySeed := by
  rw [famRec_get (by norm_num), famL, ← Nat.eq_of_beq_eq_true seed_ok]
  unfold familySeed
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzSeedT.all 0 (by norm_num)
  rw [← SuzSeedT.eq] at h
  rw [Nat.mul_zero] at h
  rw [h]

theorem suzFam_eq : suzFam = famRec :=
  CFSG.KS.FamBFS.famBFS_eq (by norm_num) (by simp [famRec]) seed_eq fam_idx fam_rec RK fam_reach

theorem famL_ne {d : Nat} (hd : d < 1782) (h0 : d ≠ 0) : famL d ≠ famL 0 := by
  obtain ⟨h1, h2, -⟩ := pt_facts hd h0
  intro e
  have hl : DIF d < (famL d).length := by rw [famL_length]; exact h1
  have hl0 : DIF d < (famL 0).length := by rw [famL_length]; exact h1
  have := congrArg (fun L : List Nat => L[DIF d]?) e
  simp only [List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hl0, Option.some.injEq,
    famL_get] at this
  exact h2 this

theorem famOK_rec : famOK 1782 22880 #[b0Arr, b1Arr] #[certArr 0, certArr 1] famRec = true := by
  unfold famOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  have hs : famRec.size = 1782 := by rw [famRec, Array.size_ofFn]
  have hs2 : (#[b0Arr, b1Arr] : Array (Array Nat)).size = (#[certArr 0, certArr 1]).size := by
    simp only [List.size_toArray, List.length_cons, List.length_nil]
  refine ⟨⟨⟨⟨hs, hs2⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro d hd
    rw [famRec_get hd, Bool.and_eq_true, List.all_eq_true]
    exact ⟨fun x hx => decide_eq_true (famL_lt hd x hx), strictIncr_of (famL_pairwise hd)⟩
  · rw [allLt_iff]
    intro k hk
    rw [allLt_iff]
    intro d hd
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨fam_idx k hk d hd, fam_rec k hk d hd⟩
  · rw [allLt_iff]
    intro d hd
    rw [Bool.or_eq_true, beq_iff_eq]
    by_cases h0 : d = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      rw [famRec_get hd, famRec_get (by norm_num), bne_iff_ne]
      exact famL_ne hd h0

theorem perms01 : invEqK 1782 11 (mask 11) (1782 * 11) B0 (SuzMtxI 0) = true ∧
    invEqK 1782 11 (mask 11) (1782 * 11) B1 (SuzMtxI 1) = true := by
  have h := mtx_perms
  simp only [bAnd_iff] at h
  exact ⟨h.1, h.2.1⟩

theorem inv0_eq : invCand 1782 b0Arr = unpack 1782 11 (SuzMtxI 0) := by
  rw [b0Arr_eq]
  exact (invEqK_sound perms01.1).1

theorem inv1_eq : invCand 1782 b1Arr = unpack 1782 11 (SuzMtxI 1) := by
  rw [b1Arr_eq]
  exact (invEqK_sound perms01.2).1

theorem sLet_arr {l : Nat} (hl : l < 4) :
    (#[b0Arr, invCand 1782 b0Arr, b1Arr, invCand 1782 b1Arr][l]!) = unpack 1782 11 (sLet l) := by
  interval_cases l
  · simp only [List.getElem!_toArray, List.getElem!_cons_zero]
    exact b0Arr_eq
  · simp only [List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact inv0_eq
  · simp only [List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact b1Arr_eq
  · simp only [List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact inv1_eq

theorem sL_lt {l x : Nat} (hl : l < 4) (hx : x < 1782) : sL l x < 1782 :=
  Eq.mp Nat.blt_eq (CFSG.KS.allN_spec (CFSG.KS.allN_spec let_range l hl) x hx)

theorem map_get4 (a b c d : Array Nat) {l : Nat} (hl : l < 4) :
    #[a.map UInt32.ofNat, b.map UInt32.ofNat, c.map UInt32.ofNat, d.map UInt32.ofNat][l]! =
      (#[a, b, c, d][l]!).map UInt32.ofNat := by
  interval_cases l <;> rfl

theorem letters_get {l : Nat} (hl : l < 4) : smallLetters[l]! =
    (#[b0Arr, invCand 1782 b0Arr, b1Arr, invCand 1782 b1Arr][l]!).map UInt32.ofNat := by
  unfold smallLetters
  exact map_get4 _ _ _ _ hl

theorem ap_letter {l x : Nat} (hl : l < 4) (hx : x < 1782) :
    CFSG.Sporadic.Th.Native.ap smallLetters[l]! x = sL l x := by
  rw [letters_get hl, sLet_arr hl, CFSG.Sporadic.Th.Native.ap,
    CFSG.Sporadic.SmallOddCore.getElem!_map_eq _ _ (by rw [unpack_size']; exact hx),
    CFSG.KC.Misc.PairCount.unpack_get hx, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by have := sL_lt hl hx; unfold sL at this; omega)

theorem tbfsSl_spec' {n cnt r lo len : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} (h : tbfsSlK n cnt r L LV PTS POS PAR LAB TI lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < cnt → tbfsPtK n cnt r L LV PTS POS PAR LAB TI k = true := by
  intro k h1 h2 h3
  have h' := CFSG.KS.allN_spec h (k - lo) (by omega)
  rw [sB] at h'
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rw [e, Eq.mpr Nat.blt_eq h3] at h'
  exact h'

theorem small_tree : smallTreeOK = true := by
  have hlv : (#[0, 1, 2, 3] : Array Nat).size = 4 ∧ ∀ t < 4,
      (#[0, 1, 2, 3] : Array Nat)[t]! = nget [0, 1, 2, 3] t ∧ nget [0, 1, 2, 3] t < smallLetters.size ∧
      ∀ x < 1782, CFSG.Sporadic.Th.Native.ap smallLetters[nget [0, 1, 2, 3] t]! x =
        sL (nget [0, 1, 2, 3] t) x := by
    refine ⟨rfl, fun t ht => ?_⟩
    have hsz : smallLetters.size = 4 := by
      simp only [smallLetters, List.size_toArray, List.length_cons, List.length_nil]
    interval_cases t <;>
      exact ⟨rfl, by rw [hsz]; decide, fun x hx => ap_letter (by decide) hx⟩
  obtain ⟨e, h⟩ := tbfsK_sound hlv st_hd fun k hk =>
    tbfsSl_spec' st_s k (Nat.zero_le _) (by rw [st_cnt] at hk; omega) hk
  unfold smallTreeOK smallTree
  rw [e, h, Bool.true_and, beq_iff_eq]
  simp [tbfsRec, st_cnt]

theorem facts2293 : famOK 1782 22880 #[b0Arr, b1Arr] #[certArr 0, certArr 1] suzFam = true ∧
    smallTreeOK = true ∧ (b0Arr.map UInt32.ofNat).size = 1782 ∧
    (∀ i < 1782, (b0Arr[i]!) < 2 ^ 32) ∧ (∀ i < 1782, (b1Arr[i]!) < 2 ^ 32) ∧
    (∀ i < 1782, (invCand 1782 b0Arr)[i]! < 2 ^ 32) ∧
    (∀ i < 1782, (invCand 1782 b1Arr)[i]! < 2 ^ 32) ∧ b0Arr[0]! ≠ 0 ∧
    (invCand 1782 b0Arr).size = 1782 ∧ (invCand 1782 b1Arr).size = 1782 := by
  have hb : ∀ l < 4, ∀ i < 1782,
      (#[b0Arr, invCand 1782 b0Arr, b1Arr, invCand 1782 b1Arr][l]!)[i]! < 2 ^ 32 := by
    intro l hl i hi
    rw [sLet_arr hl, CFSG.KC.Misc.PairCount.unpack_get hi]
    have := sL_lt hl hi
    unfold sL at this
    omega
  refine ⟨by rw [suzFam_eq]; exact famOK_rec, small_tree, by rw [b0Arr_eq]; simp [unpack_size'],
    fun i hi => hb 0 (by decide) i hi, fun i hi => hb 2 (by decide) i hi,
    fun i hi => hb 1 (by decide) i hi, fun i hi => hb 3 (by decide) i hi, ?_,
    by rw [inv0_eq, unpack_size'], by rw [inv1_eq, unpack_size']⟩
  rw [b0Arr_eq, CFSG.KC.Misc.PairCount.unpack_get (by norm_num)]
  intro e
  have h := b0_ne
  rw [e] at h
  exact absurd h (by decide)

end CertificateChecks.KernelSpor.SuzFamD

end

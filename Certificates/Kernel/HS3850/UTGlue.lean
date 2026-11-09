module

public import Certificates.Kernel.HS3850.UTChecks
public import Certificates.Kernel.HS3850.UTSearch
public import Certificates.Kernel.HS3850.UTProd
public import Certificates.Kernel.HS3850.UTWit
public import Certificates.Kernel.LocalQT.SV.C4126
public import Certificates.Kernel.HS3850.Kit
public import CFSG.Certificates.Kernel.InvTabKSound
import CFSG.Certificates.Kernel.Spor.RawOrbGrp
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.PackFld
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.RuInvHash
public import CFSG.Certificates.Kernel.Spor.ClassOneH
public import Certificates.Kernel.LocalQT.HSAut.F4146

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHS3850.UT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KD.LQT.C4126
  CFSG.KC.InvTabK CFSG.KC.LQT.SV CFSG.KC.LQT.NP CFSG.KC.BfsPin
open CFSG.Quasithin.B45Exc.HS CFSG.Quasithin.B45Exc.Tab CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Bridge.HSExcl CFSG.Monster.B.Co2.Native
open CFSG.KLie.CT (fget)

abbrev CK (p : Nat) : Prop := canonK 3850 12 (mask 12) (3850 * 12) p = true

theorem and_of {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by simpa using h

theorem allLt_iff {n : Nat} {p : Nat → Bool} : allLt n p = true ↔ ∀ i < n, p i = true :=
  CFSG.KS.MulH.allLt_iff' n p

theorem bbeq {a b : Bool} (h : Bool.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem cidn : CK idn := (PP.id (n := 3850) (w := 12) (by decide)).1

theorem hidA : idA 3850 = unpack 3850 12 idn := idA_eq (w := 12) (by decide)

theorem headSV_gen {n w N ng : Nat} {G GI : List Nat} (hh : headSV n w N ng G GI = true) :
    ∀ l < ng, canonK n w (mask w) (n * w) (CFSG.KC.LQT.TC.getTc 0 G l) = true := by
  unfold headSV at hh
  obtain ⟨-, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨hgt, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨hng, -⟩ := (bAnd_iff _ _).1 hh
  have hlen : ∀ M : List Nat, CFSG.KC.LQT.TC.lenTc M = M.length := by
    intro M
    induction M with
    | nil => rfl
    | cons _ _ ih => exact congrArg Nat.succ ih
  have hgc : ∀ (G GI : List Nat), CFSG.KC.LQT.TC.gensTc n w G GI = true → ∀ l < G.length,
      canonK n w (mask w) (n * w) (CFSG.KC.LQT.TC.getTc 0 G l) = true := by
    intro G
    induction G with
    | nil => exact fun _ _ l hl => absurd hl (by simp)
    | cons g G ih =>
      intro GI h l hl
      cases GI with
      | nil => exact absurd h (by simp [CFSG.KC.LQT.TC.gensTc])
      | cons gi GI =>
        change bAnd(canonK n w (mask w) (n * w) g, bAnd(permOK n w (mask w) (n * w) g gi,
          CFSG.KC.LQT.TC.gensTc n w G GI)) = true at h
        obtain ⟨hc, h⟩ := (bAnd_iff _ _).1 h
        obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
        cases l with
        | zero => exact hc
        | succ l => exact ih GI h l (by simpa using hl)
  intro l hl
  refine hgc G GI hgt l ?_
  rw [← hlen G, Nat.eq_of_beq_eq_true hng]
  exact hl

theorem sylE_canon {n w N ng K L : Nat} {G GI : List Nat} {E PT LT TB : Nat → Nat}
    (hh : headSV n w N ng G GI = true) (hid : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hKL : N ≤ K * L) (hc : ∀ s < K, chunkSV n w N ng G E PT LT TB (Nat.mul s L) L = true) :
    ∀ k < N, canonK n w (mask w) (n * w) (E k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hL0 : 0 < L := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · subst h0
        rw [Nat.mul_zero] at hKL
        omega
      · exact h0
    have hs' : k / L < K := by
      rw [Nat.div_lt_iff_lt_mul hL0]
      omega
    have h := hc (k / L) hs'
    unfold chunkSV at h
    have h1 := allBlk_spec h (k % L) (Nat.mod_lt _ hL0)
    beta_reduce at h1
    rw [show Nat.add (Nat.mul (k / L) L) (k % L) = k from Nat.div_add_mod' k L] at h1
    have h2 := (bIf_true h1).1 (by rw [Nat.blt_eq]; exact hk)
    unfold eltSV at h2
    obtain ⟨h3, -⟩ := (bAnd_iff _ _).1 h2
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have h3' : Nat.beq (E 0) (pidn n w) = true := h3
      have e : E 0 = pidn n w := Nat.eq_of_beq_eq_true h3'
      rw [e]
      exact hid
    · have h4 := (bIf_true h3).2 (by
        rw [Bool.eq_false_iff]
        exact fun h' => Nat.ne_of_gt hk0 (Nat.eq_of_beq_eq_true h'))
      simp only [CFSG.KC.LQT.SV.strictB_eq] at h4
      obtain ⟨h5, h4⟩ := (bAnd_iff _ _).1 h4
      obtain ⟨h6, h7⟩ := (bAnd_iff _ _).1 h4
      rw [Nat.blt_eq] at h5 h6
      rw [Nat.eq_of_beq_eq_true h7]
      exact canonK_pcomp (ih _ h5 (by omega)) (headSV_gen hh _ h6)

theorem cE {k : Nat} (hk : k < 1024) : CK (SY.E k) :=
  sylE_canon (K := 128) (L := 8) (E := SY.E) (PT := SY.PT) (LT := SY.LT) (TB := SY.TB) hSY cidn
    (by norm_num) Y.all k hk

theorem pg_lt {p q : Nat} (hp : CK p) (hq : q < 3850) : pg 12 (mask 12) p q < 3850 :=
  (CFSG.KS.PF.canon_facts hp).2.2.2 q hq

theorem syl_get : ∀ k < 1024, hsSylAl[k]! = unpack 3850 12 (SY.E k) := by
  have eP : parseNats hsSylParStr = SY.ParL := by
    rw [CP.eq]
    exact natsX_sound _ _ pP
  have eL : parseNats hsSylLabStr = SY.LabL := by
    rw [CL.eq]
    exact natsX_sound _ _ pL
  have h := (sylSV_sound (K := 128) (L := 8) (P := [0]) sylG hSY (bindSV_spec bP) (bindSV_spec bL)
    (bindSV_spec bT) (by norm_num) Y.all sSY qSY (by decide)).2
  intro k hk
  unfold hsSylAl
  rw [eP, eL]
  exact h k hk

theorem ptw_pc {p q e : Nat} (h : pc p q = e) :
    ∀ y < 3850, pg 12 (mask 12) p (pg 12 (mask 12) q y) = pg 12 (mask 12) e y := fun y hy => by
  rw [← h]
  unfold pc
  rw [CFSG.KS.PackFld.pg_pcomp (by norm_num) hy]

theorem pc_ptw {p q e : Nat} (cp : CK p) (cq : CK q) (ce : CK e)
    (h : ∀ y < 3850, pg 12 (mask 12) p (pg 12 (mask 12) q y) = pg 12 (mask 12) e y) : pc p q = e := by
  have cpq : CK (pc p q) := canonK_pcomp cp cq
  apply Nat.eq_of_beq_eq_true
  rw [← eqA_unpack cpq ce]
  unfold eqA
  rw [allLt_iff]
  intro x hx
  simp only [CFSG.KC.BfsPin.unpack_getElem!, if_pos hx, beq_iff_eq]
  unfold pc
  rw [CFSG.KS.PackFld.pg_pcomp (by norm_num) hx]
  exact h x hx

theorem sort_injSV {N : Nat} {E IS SR : Nat → Nat} (hs : sortAllSV N E IS SR = true) :
    ∀ i < N, ∀ j < N, E i = E j → i = j := by
  unfold sortAllSV at hs
  have h := allBlk_spec hs
  have hS : ∀ i < N, SR i < N ∧ IS (SR i) = i ∧ (i + 1 < N → E (IS i) < E (IS (i + 1))) := by
    intro i hi
    have := h i hi
    rw [show Nat.add 0 i = i from Nat.zero_add i] at this
    unfold sortSV at this
    rw [CFSG.KC.LQT.SV.strictB_eq] at this
    obtain ⟨h1, h23⟩ := (bAnd_iff _ _).1 this
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h23
    exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2,
      fun hi1 => Nat.blt_eq.mp ((bIf_true h3).1 (by rw [Nat.blt_eq]; exact hi1))⟩
  have mono : ∀ a b, a < b → b < N → E (IS a) < E (IS b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | rfl
      · exact lt_trans (ih h' (by omega)) ((hS b (by omega)).2.2 hb)
      · exact (hS a (by omega)).2.2 hb
  intro i hi j hj he
  obtain ⟨hri, hii, -⟩ := hS i hi
  obtain ⟨hrj, hjj, -⟩ := hS j hj
  rcases lt_trichotomy (SR i) (SR j) with h' | h' | h'
  · have := mono _ _ h' hrj
    rw [hii, hjj] at this
    omega
  · rw [← hii, ← hjj, h']
  · have := mono _ _ h' hri
    rw [hii, hjj] at this
    omega

theorem eltY {k : Nat} (hk : k < 1024) :
    eltSV 3850 12 1024 4 SY.G SY.E SY.PT SY.LT SY.TB k = true := by
  have h : chunkSV 3850 12 1024 4 SY.G SY.E SY.PT SY.LT SY.TB (Nat.mul (k / 8) 8) 8 = true :=
    Y.all (k / 8) (lt_of_lt_of_le (Nat.div_lt_of_lt_mul (show k < 8 * 128 by omega)) (le_of_eq rfl))
  unfold chunkSV at h
  have h1 := allBlk_spec h (k % 8) (Nat.mod_lt _ (by norm_num))
  beta_reduce at h1
  rw [show Nat.add (Nat.mul (k / 8) 8) (k % 8) = k from Nat.div_add_mod' k 8] at h1
  exact (bIf_true h1).1 (by rw [Nat.blt_eq]; exact hk)

theorem cGY {l : Nat} (hl : l < 4) : CK (CFSG.KC.LQT.TC.getTc 0 SY.G l) := headSV_gen hSY l hl

theorem e0Y : SY.E 0 = idn := by
  have key : ∀ k < 1024, k = 0 → SY.E k = idn := by
    intro k hk hk0
    have h := eltY hk
    unfold eltSV at h
    obtain ⟨h3, -⟩ := (bAnd_iff _ _).1 h
    have e := Nat.eq_of_beq_eq_true ((bIf_true h3).1 (by rw [hk0]; rfl))
    rw [hk0]
    exact e
  exact key 0 (by norm_num) rfl

theorem parY {k : Nat} (hk : k < 1024) (h0 : k ≠ 0) : SY.PT k < k ∧ SY.LT k < 4 ∧
    SY.E k = pc (SY.E (SY.PT k)) (CFSG.KC.LQT.TC.getTc 0 SY.G (SY.LT k)) := by
  have h := eltY hk
  unfold eltSV at h
  obtain ⟨h3, -⟩ := (bAnd_iff _ _).1 h
  have h4 := (bIf_true h3).2 (by
    rw [Bool.eq_false_iff]
    exact fun h' => h0 (Nat.eq_of_beq_eq_true h'))
  simp only [CFSG.KC.LQT.SV.strictB_eq] at h4
  obtain ⟨h5, h4⟩ := (bAnd_iff _ _).1 h4
  obtain ⟨h6, h7⟩ := (bAnd_iff _ _).1 h4
  exact ⟨Nat.blt_eq.mp h5, Nat.blt_eq.mp h6, Nat.eq_of_beq_eq_true h7⟩

theorem gstep {k l : Nat} (hk : k < 1024) (hl : l < 4) :
    ∃ t < 1024, pc (SY.E k) (CFSG.KC.LQT.TC.getTc 0 SY.G l) = SY.E t := by
  have h := eltY hk
  unfold eltSV at h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  have h1 := allBlk_spec h l hl
  beta_reduce at h1
  rw [show Nat.add 0 l = l from Nat.zero_add l, CFSG.KC.LQT.SV.strictB_eq] at h1
  generalize SY.TB (Nat.add (Nat.mul k 4) l) = t at h1
  obtain ⟨ht, h2⟩ := (bAnd_iff _ _).1 h1
  have ht := Nat.blt_eq.mp ht
  refine ⟨t, ht, ?_⟩
  rcases (bIf_true h2) with ⟨-, hf⟩
  cases hc : bAnd(bIf(Nat.beq t (nat_lit 0), false, true),
      bAnd(Nat.beq (SY.PT t) k, Nat.beq (SY.LT t) l))
  · exact Nat.eq_of_beq_eq_true (hf hc)
  · rw [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at hc
    obtain ⟨h0, hp, hl'⟩ := hc
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact absurd h0 (by decide)
    obtain ⟨-, -, e⟩ := parY ht ht0
    rw [e, Nat.eq_of_beq_eq_true hp, Nat.eq_of_beq_eq_true hl']

theorem closY : ∀ b < 1024, ∀ a < 1024, ∃ t < 1024, pc (SY.E a) (SY.E b) = SY.E t := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb a ha
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · refine ⟨a, ha, pc_ptw (cE ha) (cE hb) (cE ha) fun y hy => ?_⟩
      rw [e0Y]
      unfold idn
      rw [CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hy]
    · obtain ⟨hp, hl, he⟩ := parY hb (by omega)
      obtain ⟨s, hs, es⟩ := ih _ hp (by omega) a ha
      obtain ⟨t, ht, et⟩ := gstep hs hl
      refine ⟨t, ht, pc_ptw (cE ha) (cE hb) (cE ht) fun y hy => ?_⟩
      rw [he, ← et]
      unfold pc
      rw [CFSG.KS.PackFld.pg_pcomp (by norm_num) hy, CFSG.KS.PackFld.pg_pcomp (by norm_num) hy]
      exact ptw_pc es _ (pg_lt (cGY hl) hy)

theorem kk_pc (p q : Nat) : kk (pc p q) =
    Nat.add (Nat.mul (img p (img q 0)) 4096) (img p (img q 5)) := by
  unfold kk img pc
  rw [CFSG.KS.PackFld.pg_pcomp (by norm_num) (by norm_num : (0 : Nat) < 3850),
    CFSG.KS.PackFld.pg_pcomp (by norm_num) (by norm_num : (5 : Nat) < 3850)]

theorem img_idn {y : Nat} (hy : y < 3850) : img idn y = y := by
  unfold img idn
  exact CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hy

theorem img_pc (p q y : Nat) (hy : y < 3850) : img p (img q y) = img (pc p q) y := by
  unfold img pc
  rw [CFSG.KS.PackFld.pg_pcomp (by norm_num) hy]

theorem sq_key {k : Nat} (hk : k < 1024) : Nat.beq (pc (SY.E k) (SY.E k)) idn =
    (Nat.beq (img (SY.E k) (img (SY.E k) 0)) 0 && Nat.beq (img (SY.E k) (img (SY.E k) 5)) 5) := by
  rw [img_pc _ _ 0 (by norm_num), img_pc _ _ 5 (by norm_num)]
  obtain ⟨t, ht, et⟩ := closY k hk k hk
  rw [et]
  apply Bool.eq_iff_iff.2
  rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq]
  constructor
  · intro e
    rw [e, img_idn (by norm_num), img_idn (by norm_num)]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h5⟩
    have e : (fun k => kk (SY.E k)) t = (fun k => kk (SY.E k)) 0 := by
      change kk (SY.E t) = kk (SY.E 0)
      unfold kk
      rw [h0, h5, e0Y, img_idn (by norm_num), img_idn (by norm_num)]
    rw [sort_injSV ksort t ht 0 (by norm_num) e, e0Y]

theorem key_S {a b t : Nat} (ha : a < 1024) (hb : b < 1024) (ht : t < 1024)
    (h0 : img (SY.E a) (img (SY.E b) 0) = img (SY.E t) 0)
    (h5 : img (SY.E a) (img (SY.E b) 5) = img (SY.E t) 5) : pc (SY.E a) (SY.E b) = SY.E t := by
  rw [img_pc _ _ 0 (by norm_num)] at h0
  rw [img_pc _ _ 5 (by norm_num)] at h5
  obtain ⟨s, hs, es⟩ := closY b hb a ha
  rw [es] at h0 h5 ⊢
  have e : (fun k => kk (SY.E k)) s = (fun k => kk (SY.E k)) t := by
    change kk (SY.E s) = kk (SY.E t)
    unfold kk
    rw [h0, h5]
  rw [sort_injSV ksort s hs t ht e]

theorem key_one {a b : Nat} (ha : a < 1024) (hb : b < 1024)
    (h0 : img (SY.E a) (img (SY.E b) 0) = 0) (h5 : img (SY.E a) (img (SY.E b) 5) = 5) :
    pc (SY.E a) (SY.E b) = idn := by
  rw [← e0Y]
  refine key_S ha hb (by norm_num) ?_ ?_
  · rw [h0, e0Y, img_idn (by norm_num)]
  · rw [h5, e0Y, img_idn (by norm_num)]

theorem invs_eq : (List.range 1024).filter (fun i => !(Nat.beq (SY.E i) idn) &&
    Nat.beq (pc (SY.E i) (SY.E i)) idn) = (List.range 191).map INV := by
  rw [← beq_iff_eq.1 invs]
  apply List.filter_congr
  intro i hi
  rw [sq_key (List.mem_range.1 hi)]

theorem inv_filter : sylInv 3850 1024 hsSylAl = (List.range 191).map INV := by
  rw [← invs_eq]
  unfold sylInv
  apply List.filter_congr
  intro i hi
  have hi' := List.mem_range.1 hi
  rw [syl_get i hi', hidA, eqA_unpack (cE hi') cidn, compA_unpack (cE hi') (cE hi'),
    eqA_unpack (canonK_pcomp (cE hi') (cE hi')) cidn]
  rfl

theorem inv_mem {i : Nat} (hi : i < 191) : INV i < 1024 ∧ (!(Nat.beq (SY.E (INV i)) idn) &&
    Nat.beq (pc (SY.E (INV i)) (SY.E (INV i))) idn) = true := by
  have hm : INV i ∈ (List.range 1024).filter (fun i => !(Nat.beq (SY.E i) idn) &&
      Nat.beq (pc (SY.E i) (SY.E i)) idn) := by
    rw [invs_eq]
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  rw [List.mem_filter, List.mem_range] at hm
  exact hm

theorem cX {i : Nat} (hi : i < 191) : CK (X i) := cE (inv_mem hi).1

theorem cxE (k : Nat) : CK (xE k) := by
  unfold xE
  cases h : Nat.blt k 191
  · exact cidn
  · exact cX (Nat.blt_eq.mp h)

theorem mapMapCongr {α : Type} {f : Nat → Nat} {g h : Nat → α} {l : List Nat}
    (hp : ∀ i ∈ l, g (f i) = h i) : (l.map f).map g = l.map h := by
  rw [List.map_map]
  exact List.map_congr_left hp

theorem uinv_eq : hsUInv = ((List.range 191).map fun i => unpack 3850 12 (X i)).toArray := by
  unfold hsUInv
  exact congrArg List.toArray ((congrArg (List.map fun i => hsSylAl[i]!) inv_filter).trans
    (mapMapCongr fun i hi => syl_get _ (inv_mem (List.mem_range.1 hi)).1))

theorem uinv_size : hsUInv.size = 191 := by
  rw [uinv_eq]
  simp

theorem uinv_get {i : Nat} (hi : i < 191) : hsUInv[i]! = unpack 3850 12 (X i) := by
  rw [uinv_eq, getElem!_pos _ i (by simpa using hi)]
  simp

theorem hm : hsUTab.m = 191 := by
  unfold hsUTab
  rw [build_m, uinv_size]

theorem elt_eq (k : Nat) : hsUTab.elt k = unpack 3850 12 (xE k) := by
  unfold InvTab.elt xE
  rw [hm]
  by_cases hk : k < 191
  · rw [if_pos hk, Nat.blt_eq.mpr hk]
    unfold hsUTab
    rw [build_xs, uinv_get hk]
    rfl
  · rw [if_neg hk, show Nat.blt k 191 = false from Bool.eq_false_iff.2 fun h => hk (Nat.blt_eq.mp h),
      hidA]
    rfl

theorem keyMul_eq {p q : Nat} (hq : CK q) :
    keyMulB [0, 5] (unpack 3850 12 p) (unpack 3850 12 q) =
      [pg 12 (mask 12) p (pg 12 (mask 12) q 0), pg 12 (mask 12) p (pg 12 (mask 12) q 5)] := by
  unfold keyMulB
  simp only [List.map_cons, List.map_nil]
  rw [unpack_get' (by norm_num : 0 < 3850), unpack_get' (by norm_num : 5 < 3850),
    unpack_get' (pg_lt hq (by norm_num)), unpack_get' (pg_lt hq (by norm_num))]

theorem keyOf_eq (p : Nat) : ([0, 5].map fun i => (unpack 3850 12 p)[i]!) =
    [pg 12 (mask 12) p 0, pg 12 (mask 12) p 5] := by
  simp only [List.map_cons, List.map_nil]
  rw [unpack_get' (by norm_num : 0 < 3850), unpack_get' (by norm_num : 5 < 3850)]

theorem list2_beq (a b c d : Nat) : ([a, b] == [c, d]) = (Nat.beq a c && Nat.beq b d) := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq]
  simp

theorem commAt_eq (i j : Nat) : hsUTab.commAt i j = cK i j := by
  by_cases h : i < 191 ∧ j < 191
  · have hi : i < hsUInv.size := by rw [uinv_size]; exact h.1
    have hj : j < hsUInv.size := by rw [uinv_size]; exact h.2
    unfold hsUTab
    rw [build_commAt hsUInv [0, 5] hi hj, uinv_get h.1, uinv_get h.2, keyMul_eq (cX h.2),
      keyMul_eq (cX h.1), list2_beq]
    unfold cK
    rw [if_pos h]
    have e := bbeq (allN_spec (allN_spec comm i h.1) j h.2)
    exact e.symm
  · unfold InvTab.commAt cK
    rw [hm, if_neg h, if_neg h]

theorem kk_inj {a b c d : Nat} (ha : a < 3850) (hb : b < 3850) (hc : c < 3850) (hd : d < 3850)
    (h : Nat.add (Nat.mul a 4096) b = Nat.add (Nat.mul c 4096) d) : a = c ∧ b = d := by
  simp only [Nat.add_eq, Nat.mul_eq] at h
  omega

theorem keys' {i j : Nat} (hi : i < 192) (hj : j < 192) (hij : i ≠ j) : kk (xE i) ≠ kk (xE j) := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have := allN_spec (allN_spec keys j hj) i h
    intro e
    rw [e, Nat.beq_refl] at this
    exact Bool.noConfusion this
  · have := allN_spec (allN_spec keys i hi) j h
    intro e
    rw [e, Nat.beq_refl] at this
    exact Bool.noConfusion this

theorem keyOf_xE (k : Nat) : ([0, 5].map fun i => (unpack 3850 12 (xE k))[i]!) =
    [pg 12 (mask 12) (xE k) 0, pg 12 (mask 12) (xE k) 5] := keyOf_eq _

theorem keyOf_inj {i j : Nat} (hi : i < 192) (hj : j < 192)
    (h : ([0, 5].map fun p => (unpack 3850 12 (xE i))[p]!) =
      ([0, 5].map fun p => (unpack 3850 12 (xE j))[p]!)) : i = j := by
  by_contra hij
  apply keys' hi hj hij
  rw [keyOf_xE, keyOf_xE] at h
  simp only [List.cons.injEq, and_true] at h
  unfold kk img
  rw [h.1, h.2]

theorem prodAt_eq (i j : Nat) : hsUTab.prodAt i j = pK i j := by
  by_cases h : i < 191 ∧ j < 191
  · have hi : i < hsUInv.size := by rw [uinv_size]; exact h.1
    have hj : j < hsUInv.size := by rw [uinv_size]; exact h.2
    have hp := allN_spec (allN_spec prodk i h.1) j h.2
    unfold hsUTab
    rw [build_prodAt hsUInv [0, 5] hi hj, uinv_get h.1, uinv_get h.2, keyMul_eq (cX h.2),
      keyMul_eq (cX h.1), list2_beq, uinv_size]
    unfold pK
    rw [if_pos h.1, if_pos h.2]
    have ec := bbeq (allN_spec (allN_spec comm i h.1) j h.2)
    rw [show (Nat.beq (pg 12 (mask 12) (X i) (pg 12 (mask 12) (X j) 0))
        (pg 12 (mask 12) (X j) (pg 12 (mask 12) (X i) 0)) &&
        Nat.beq (pg 12 (mask 12) (X i) (pg 12 (mask 12) (X j) 5))
          (pg 12 (mask 12) (X j) (pg 12 (mask 12) (X i) 5))) = Nat.testBit (CM i) j from ec.symm]
    cases hb : Nat.testBit (CM i) j
    · rw [hb] at hp
      simp only [CFSG.KS.Raw.Orb.bIf_eq] at hp
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact (Nat.eq_of_beq_eq_true (by simpa using hp)).symm
    · rw [hb] at hp
      simp only [CFSG.KS.Raw.Orb.bIf_eq, ↓reduceIte, Bool.and_eq_true, Nat.ble_eq] at hp
      simp only [↓reduceIte]
      obtain ⟨hle, hkey⟩ := hp
      set q := fget (PR i) j 8 with hq
      have hk := Nat.eq_of_beq_eq_true hkey
      unfold kk img at hk
      obtain ⟨k1, k2⟩ := kk_inj (pg_lt (cX h.1) (pg_lt (cX h.2) (by norm_num)))
        (pg_lt (cX h.1) (pg_lt (cX h.2) (by norm_num))) (pg_lt (cxE q) (by norm_num))
        (pg_lt (cxE q) (by norm_num)) hk
      have hkm : [pg 12 (mask 12) (X i) (pg 12 (mask 12) (X j) 0),
          pg 12 (mask 12) (X i) (pg 12 (mask 12) (X j) 5)] =
          ([0, 5].map fun p => (unpack 3850 12 (xE q))[p]!) := by
        rw [keyOf_xE, k1, k2]
      rw [hkm]
      have hf : ∀ a ∈ List.range 191, ([0, 5].map fun p => (hsUInv[a]!)[p]!) =
          ([0, 5].map fun p => (unpack 3850 12 (xE a))[p]!) := by
        intro a ha
        have ha' := List.mem_range.1 ha
        rw [uinv_get ha']
        unfold xE
        rw [Nat.blt_eq.mpr ha']
        rfl
      rcases Nat.lt_or_ge q 191 with hq1 | hq1
      · have e1 : ([0, 5].map fun p => (unpack 3850 12 (xE q))[p]!) =
            ([0, 5].map fun p => (hsUInv[q]!)[p]!) := (hf q (List.mem_range.2 hq1)).symm
        rw [e1]
        refine getD_foldl_insert (fun a => [0, 5].map fun p => (hsUInv[a]!)[p]!) _ _ _ q
          (List.mem_range.2 hq1) fun a ha e => ?_
        have ha' := List.mem_range.1 ha
        rw [hf a ha, hf q (List.mem_range.2 hq1)] at e
        exact keyOf_inj (by omega) (by omega) e
      · have hq191 : q = 191 := by omega
        have e1 : ([0, 5].map fun p => (unpack 3850 12 (xE q))[p]!) =
            ([0, 5].map fun p => (idA 3850)[p]!) := by
          rw [hq191, hidA]
          rfl
        rw [e1, getD_foldl_insert_not _ _ _ _ _ fun a ha e => ?_, Std.HashMap.getD_insert_self,
          hq191]
        have ha' := List.mem_range.1 ha
        rw [hf a ha, hidA] at e
        have e2 : ([0, 5].map fun p => (unpack 3850 12 idn)[p]!) =
            ([0, 5].map fun p => (unpack 3850 12 (xE 191))[p]!) := rfl
        rw [e2] at e
        exact absurd (keyOf_inj (by omega) (by norm_num) e) (by omega)
  · unfold InvTab.prodAt pK
    rw [hm]
    by_cases hi : i < 191
    · have hj : ¬ j < 191 := fun hj => h ⟨hi, hj⟩
      rw [if_pos hi, if_pos hi, if_neg hj, if_neg hj]
    · rw [if_neg hi, if_neg hi]

theorem pg_swap {f g e : Nat → Nat} {n : Nat} (hg : ∀ x < n, g x < n) (he : ∀ x < n, e x < n)
    (ff : ∀ x < n, f (f x) = x) (gg : ∀ x < n, g (g x) = x) (ee : ∀ x < n, e (e x) = x)
    (fg : ∀ x < n, f (g x) = e x) : ∀ x < n, g (f x) = e x := by
  intro x hx
  have h1 : f (g (e x)) = x := by rw [fg _ (he x hx), ee x hx]
  have h2 := ff _ (hg _ (he x hx))
  rw [h1] at h2
  rw [h2, gg _ (he x hx)]

theorem uX_invol {i : Nat} (hi : i < 191) :
    ∀ y < 3850, pg 12 (mask 12) (X i) (pg 12 (mask 12) (X i) y) = y := by
  intro y hy
  have h := (and_of (inv_mem hi).2).2
  have e : pc (X i) (X i) = idn := Nat.eq_of_beq_eq_true h
  have c : pg 12 (mask 12) (pc (X i) (X i)) y = pg 12 (mask 12) idn y := by rw [e]
  unfold pc idn at c
  rwa [CFSG.KS.PackFld.pg_pcomp (by norm_num) hy, CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hy]
    at c

theorem xE_invol (k : Nat) :
    ∀ y < 3850, pg 12 (mask 12) (xE k) (pg 12 (mask 12) (xE k) y) = y := by
  intro y hy
  unfold xE
  cases h : Nat.blt k 191
  · have e : ∀ z < 3850, pg 12 (mask 12) idn z = z := fun z hz => by
      unfold idn
      exact CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hz
    simp only [cond_false]
    rw [e y hy, e y hy]
  · exact uX_invol (Nat.blt_eq.mp h) y hy

theorem xE_lt {k : Nat} (hk : k < 191) : xE k = X k := by
  unfold xE
  rw [Nat.blt_eq.mpr hk]
  rfl

theorem xE_mem {k : Nat} (hk : k ≤ 191) : ∃ m < 1024, xE k = SY.E m := by
  rcases Nat.lt_or_ge k 191 with h | h
  · exact ⟨INV k, (inv_mem h).1, xE_lt h⟩
  · refine ⟨0, by norm_num, ?_⟩
    rw [e0Y, show k = 191 by omega]
    rfl

theorem prod_kl {i j : Nat} (hij : i ≤ j) (hj : j < 191) (hc : Nat.testBit (CM i) j = true) :
    pc (X i) (X j) = xE (fget (PR i) j 8) := by
  have hi : i < 191 := by omega
  have hpk := allN_spec (allN_spec prodk i hi) j hj
  rw [hc] at hpk
  simp only [CFSG.KS.Raw.Orb.bIf_eq, ↓reduceIte, Bool.and_eq_true, Nat.ble_eq] at hpk
  obtain ⟨hle, hkey⟩ := hpk
  obtain ⟨t, ht, et⟩ := closY _ (inv_mem hj).1 _ (inv_mem hi).1
  obtain ⟨m, hm, em⟩ := xE_mem hle
  have e : (fun k => kk (SY.E k)) t = (fun k => kk (SY.E k)) m := by
    change kk (SY.E t) = kk (SY.E m)
    rw [← et, ← em, kk_pc]
    exact Nat.eq_of_beq_eq_true hkey
  have htm := sort_injSV ksort t ht m hm e
  change pc (SY.E (INV i)) (SY.E (INV j)) = _
  rw [et, em, htm]

theorem prod_spec {i j : Nat} (hij : i ≤ j) (hj : j < 191) (hc : Nat.testBit (CM i) j = true) :
    pc (X i) (X j) = xE (fget (PR i) j 8) ∧ pc (X j) (X i) = xE (fget (PR i) j 8) := by
  have hi : i < 191 := by omega
  have p1 := prod_kl hij hj hc
  exact ⟨p1, pc_ptw (cX hj) (cX hi) (cxE _) (pg_swap (fun y hy => pg_lt (cX hj) hy)
    (fun y hy => pg_lt (cxE _) hy) (uX_invol hi) (uX_invol hj) (xE_invol _) (ptw_pc p1))⟩

theorem check_true : hsUTab.check 4 = true := by
  unfold InvTab.check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩
  · rw [allLt_iff, hm]
    intro i hi
    have hx : hsUTab.xs[i]! = unpack 3850 12 (X i) := by
      unfold hsUTab
      rw [build_xs, uinv_get hi]
    rw [hx]
    have h2 : isInvA 3850 (unpack 3850 12 (X i)) (unpack 3850 12 (X i)) = true := by
      unfold isInvA
      rw [allLt_iff]
      intro p hp
      have h1 := pg_lt (cX hi) hp
      rw [unpack_get' hp, unpack_get' h1, uX_invol hi p hp]
      simp [h1]
    rw [Bool.and_eq_true]
    refine ⟨h2, ?_⟩
    have hn := and_of (inv_mem hi).2
    rw [hidA, eqA_unpack (cX hi) cidn]
    exact hn.1
  · rw [allLt_iff, hm]
    intro i hi
    rw [allLt_iff]
    intro j hj
    have hx : ∀ k < 191, hsUTab.xs[k]! = unpack 3850 12 (X k) := fun k hk => by
      unfold hsUTab
      rw [build_xs, uinv_get hk]
    rw [hx i hi, hx j (by omega), bne_iff_ne]
    intro e
    have e' : ([0, 5].map fun p => (unpack 3850 12 (xE i))[p]!) =
        ([0, 5].map fun p => (unpack 3850 12 (xE j))[p]!) := by
      unfold xE
      rw [Nat.blt_eq.mpr hi, Nat.blt_eq.mpr (by omega : j < 191)]
      exact e
    exact absurd (keyOf_inj (by omega) (by omega) e') (by omega)
  · apply CFSG.KS.Raw.Orb.parLt_of_forall
    rw [hm]
    intro i hi
    rw [allLt_iff]
    intro j hj
    have hi' : i < hsUInv.size := by rw [uinv_size]; exact hi
    have hj' : j < hsUInv.size := by rw [uinv_size]; exact hj
    by_cases hji : j < i
    · rw [if_pos hji]
      unfold hsUTab
      exact build_symOK hsUInv [0, 5] hi' hj'
    · rw [if_neg hji]
      unfold InvTab.pairOK
      cases hc : hsUTab.commAt i j
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hc' := hc
        unfold hsUTab at hc'
        have := build_ncAt (n := 3850) hsUInv [0, 5] hi' hj' hc' (by decide)
        unfold hsUTab
        exact this
      · simp only [↓reduceIte]
        rw [commAt_eq] at hc
        unfold cK at hc
        rw [if_pos ⟨hi, hj⟩] at hc
        obtain ⟨p1, p2⟩ := prod_spec (by omega) hj hc
        have hpk := allN_spec (allN_spec prodk i hi) j hj
        rw [hc] at hpk
        simp only [CFSG.KS.Raw.Orb.bIf_eq, ↓reduceIte, Bool.and_eq_true, Nat.ble_eq] at hpk
        rw [prodAt_eq, hm, Bool.and_eq_true, decide_eq_true_eq]
        unfold pK
        rw [if_pos hi, if_pos hj]
        refine ⟨hpk.1, ?_⟩
        have hx : ∀ k < 191, hsUTab.xs[k]! = unpack 3850 12 (X k) := fun k hk => by
          unfold hsUTab
          rw [build_xs, uinv_get hk]
        rw [hx i hi, hx j hj, elt_eq]
        unfold prodOK
        rw [allLt_iff]
        intro p hp
        have c1 := congrArg (fun a => a[p]!) (compA_unpack (cX hi) (cX hj))
        have c2 := congrArg (fun a => a[p]!) (compA_unpack (cX hj) (cX hi))
        rw [show pcomp 3850 12 (mask 12) (X i) (X j) = xE (fget (PR i) j 8) from p1] at c1
        rw [show pcomp 3850 12 (mask 12) (X j) (X i) = xE (fget (PR i) j 8) from p2] at c2
        rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
        unfold compA at c1 c2
        rw [getElem!_pos _ p (by simpa using hp), Array.getElem_ofFn] at c1 c2
        exact ⟨c1, c2⟩

theorem countP_conj {n : Nat} {a b g h : Nat → Nat} (hb : ∀ y < n, b y < n)
    (hg : ∀ y < n, g y < n) (hh : ∀ y < n, h y < n) (gh : ∀ y < n, g (h y) = y)
    (hg' : ∀ y < n, h (g y) = y) (c : ∀ y < n, a (g y) = g (b y)) :
    (List.range n).countP (fun y => a y == y) = (List.range n).countP (fun y => b y == y) := by
  have e : ∀ f : Nat → Nat,
      (List.range n).countP (fun y => f y == y) = Nat.count (fun m => f m = m) n := by
    intro f
    unfold Nat.count
    exact List.countP_congr fun i _ => by simp
  rw [e, e, Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  refine Finset.card_nbij' h g (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_)
  · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hy ⊢
    refine ⟨hh y hy.1, ?_⟩
    have h1 := c (h y) (hh y hy.1)
    rw [gh y hy.1, hy.2] at h1
    have h2 := congrArg h h1
    rw [hg' _ (hb _ (hh y hy.1))] at h2
    exact h2.symm
  · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hy ⊢
    refine ⟨hg y hy.1, ?_⟩
    rw [c y hy.1, hy.2]
  · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hy
    exact gh y hy.1
  · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hy
    exact hg' y hy.1

theorem nfix_X {s : Nat} (hs : s < 191) : CFSG.KC.PkPow.nfix 3850 12 (X s) = FX s := by
  have rep : ∀ r < 191, UCR r = r → CFSG.KC.PkPow.nfix 3850 12 (X r) = FX r := by
    intro r hr e
    have h := allN_spec fix r hr
    rw [e, Nat.beq_refl] at h
    simp only at h
    exact Nat.eq_of_beq_eq_true h
  by_cases e : UCR s = s
  · exact rep s hs e
  have h := allN_spec fix s hs
  have hb : Nat.beq (UCR s) s = false := Bool.eq_false_iff.2 fun h' => e (Nat.eq_of_beq_eq_true h')
  rw [hb] at h
  simp only at h
  unfold ucjK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, and_assoc] at h
  obtain ⟨hr, hrr, hfx, hj, hi, c0, c5, g0, g5, h0, h5⟩ := h
  have eGH := key_one hj hi g0 g5
  have eHG := key_one hi hj h0 h5
  obtain ⟨t, ht, et⟩ := closY _ hj _ (inv_mem hs).1
  have e2 : pc (SY.E (UCJ s)) (SY.E (INV (UCR s))) = SY.E t := by
    refine key_S hj (inv_mem hr).1 ht ?_ ?_
    · exact c0.symm.trans ((img_pc (X s) (SY.E (UCJ s)) 0 (by norm_num)).trans
        (congrArg (fun p => img p 0) et))
    · exact c5.symm.trans ((img_pc (X s) (SY.E (UCJ s)) 5 (by norm_num)).trans
        (congrArg (fun p => img p 5) et))
  have hc : pc (X s) (SY.E (UCJ s)) = pc (SY.E (UCJ s)) (X (UCR s)) := et.trans e2.symm
  have hcount := countP_conj (n := 3850) (a := img (X s)) (b := img (X (UCR s)))
    (g := img (SY.E (UCJ s))) (h := img (SY.E (UCI s)))
    (fun y hy => pg_lt (cX hr) hy) (fun y hy => pg_lt (cE hj) hy) (fun y hy => pg_lt (cE hi) hy)
    (fun y hy => by rw [img_pc _ _ y hy, eGH, img_idn hy])
    (fun y hy => by rw [img_pc _ _ y hy, eHG, img_idn hy])
    (fun y hy => by rw [img_pc _ _ y hy, img_pc _ _ y hy, hc])
  have u : ∀ p : Nat, (List.range 3850).countP (fun x => (unpack 3850 12 p)[x]! == x) =
      (List.range 3850).countP (fun x => img p x == x) := fun p =>
    List.countP_congr fun x hx => by simp only [unpack_get' (List.mem_range.1 hx), img]
  rw [← hfx, ← rep _ hr hrr, ← CFSG.KD.HS3850.countP_nfix, ← CFSG.KD.HS3850.countP_nfix, u, u]
  exact hcount

theorem fix_get {s : Nat} (hs : s < 191) : hsUFix[s]! = FX s := by
  have hsz : s < hsUInv.size := by rw [uinv_size]; exact hs
  unfold hsUFix
  rw [getElem!_pos _ s (by simpa using hsz), Array.getElem_map, ← getElem!_pos _ s hsz,
    uinv_get hs]
  unfold fixCountA
  rw [CFSG.KD.HS3850.countP_nfix]
  exact nfix_X hs

theorem search_eq (pred : List Nat → Bool) (k : Nat) :
    hsUTab.forallGreedyI pred k [] = forallGreedyF 191 cK pK pred k [] := by
  rw [forallGreedyI_eq, hm]
  have e1 : hsUTab.commAt = cK := funext fun i => funext fun j => commAt_eq i j
  have e2 : hsUTab.prodAt = pK := funext fun i => funext fun j => prodAt_eq i j
  rw [e1, e2]

theorem subprods_eq (l : List Nat) : hsUTab.subprodsI l = subprodsF 191 pK l := by
  rw [subprodsI_eq, hm]
  have e2 : hsUTab.prodAt = pK := funext fun i => funext fun j => prodAt_eq i j
  rw [e2]

theorem pred4_eq : hsPred4 = pred4K := by
  funext l
  unfold hsPred4 pred4K
  simp only []
  rw [subprods_eq, hm]
  have hf : (fun s => decide (s < 191) && (hsUFix[s]! == 30 || hsUFix[s]! == 46)) =
      (fun s => decide (s < 191) && (FX s == 30 || FX s == 46)) := by
    funext s
    by_cases hs : s < 191
    · rw [fix_get hs]
    · simp [hs]
  rw [hf]

theorem pred5_eq : hsPred5 = pred5K := by
  funext l
  unfold hsPred5 pred5K
  rw [subprods_eq]

theorem gens_get (k : Nat) : hsGens.getD k (pId 3850) =
    (unpack 3850 12 (L0.getD k idn), unpack 3850 12 (LI0.getD k idn)) := by
  have e := CFSG.KD.LQT.C4126.gens_eq
  unfold hsGens
  rw [e]
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> rfl
  · unfold CFSG.KC.LQT.TC.unpackP L0 LI0
    rw [List.getD_eq_default _ _ (by simpa using hk), List.getD_eq_default _ _ (by simpa using hk),
      List.getD_eq_default _ _ (by simpa using hk), pId, hidA]

theorem gen_canon : (∀ k, CK (L0.getD k idn)) ∧ ∀ k, CK (LI0.getD k idn) := by
  have h := gcanon
  refine ⟨fun k => ?_, fun k => ?_⟩ <;> rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · exact (and_of (allN_spec h 0 (by norm_num))).1
    · exact (and_of (allN_spec h 1 (by norm_num))).1
  · unfold L0
    rw [List.getD_eq_default _ _ (by simpa using hk)]
    exact cidn
  · interval_cases k
    · exact (and_of (allN_spec h 0 (by norm_num))).2
    · exact (and_of (allN_spec h 1 (by norm_num))).2
  · unfold LI0
    rw [List.getD_eq_default _ _ (by simpa using hk)]
    exact cidn

theorem word_eq (wd : List Int) : pWord 3850 hsGens wd =
    (unpack 3850 12 (wordP1 3850 12 L0 LI0 wd), unpack 3850 12 (wordP2 3850 12 L0 LI0 wd)) ∧
    CK (wordP1 3850 12 L0 LI0 wd) ∧ CK (wordP2 3850 12 L0 LI0 wd) :=
  pWord_unpack gens_get gen_canon.1 gen_canon.2 cidn hidA wd

theorem regs_get (B : List Nat) {G GI : Nat} (hG : CK G) (hGI : CK GI) (k : Nat) :
    ((B.map fun i => (hsUTab.elt i, hsUTab.elt i)) ++
      (B.map fun i => pConj 3850 (unpack 3850 12 G, unpack 3850 12 GI)
        (hsUTab.elt i, hsUTab.elt i))).getD k (pId 3850) =
      (unpack 3850 12 ((regL B G GI).getD k idn), unpack 3850 12 ((regLI B G GI).getD k idn)) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  unfold regL regLI
  rcases Nat.lt_or_ge k B.length with hk | hk
  · rw [List.getElem?_append_left (by simpa using hk), List.getElem?_append_left (by simpa using hk),
      List.getElem?_append_left (by simpa using hk)]
    simp only [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]
    rw [elt_eq]
  · rw [List.getElem?_append_right (by simpa using hk), List.getElem?_append_right (by simpa using hk),
      List.getElem?_append_right (by simpa using hk)]
    simp only [List.length_map, List.getElem?_map]
    rcases Nat.lt_or_ge (k - B.length) B.length with hk2 | hk2
    · rw [List.getElem?_eq_getElem hk2]
      simp only [Option.map_some, Option.getD_some]
      have cx := cxE B[k - B.length]
      rw [elt_eq, pConj, pMul, pMul, pInv]
      simp only
      rw [compA_unpack hG cx, compA_unpack (canonK_pcomp hG cx) hGI, compA_unpack cx hGI,
        compA_unpack hG (canonK_pcomp cx hGI)]
      rfl
    · rw [List.getElem?_eq_none hk2]
      simp only [Option.map_none, Option.getD_none]
      rw [pId, hidA]

theorem regs_canon (B : List Nat) {G GI : Nat} (hG : CK G) (hGI : CK GI) :
    (∀ k, CK ((regL B G GI).getD k idn)) ∧ ∀ k, CK ((regLI B G GI).getD k idn) := by
  have hmem : ∀ (L : List Nat), (∀ x ∈ L, CK x) → ∀ k, CK (L.getD k idn) := by
    intro L hL k
    rw [List.getD_eq_getElem?_getD]
    cases h : L[k]?
    · exact cidn
    · exact hL _ (List.mem_of_getElem? h)
  refine ⟨hmem _ fun x hx => ?_, hmem _ fun x hx => ?_⟩
  · unfold regL at hx
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
      exact cxE i
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
      exact canonK_pcomp (canonK_pcomp hG (cxE i)) hGI
  · unfold regLI at hx
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
      exact cxE i
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
      exact canonK_pcomp hG (canonK_pcomp (cxE i) hGI)

theorem gen_of {w : GenWit} (h : genK w = true) :
    genWitOK hsGens hsUTab [hsA0A, hsA1A] w = true := by
  obtain ⟨hG, cG, cGI⟩ := word_eq w.g
  unfold genK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hb, hl⟩, hw⟩ := h
  have hreg := regs_get w.basis cG cGI
  obtain ⟨cR, cRI⟩ := regs_canon w.basis cG cGI
  unfold genWitOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.all_eq_true] at hb ⊢
    intro i hi
    rw [hm]
    exact decide_eq_true (Nat.blt_eq.mp (hb i hi))
  · rw [beq_iff_eq]
    exact Nat.eq_of_beq_eq_true hl
  · have ht : [hsA0A, hsA1A] = L0.map (unpack 3850 12) := targ_eq
    have hr : genRegs hsGens hsUTab w = (w.basis.map fun i => (hsUTab.elt i, hsUTab.elt i)) ++
        (w.basis.map fun i => pConj 3850 (unpack 3850 12 (wordP1 3850 12 L0 LI0 w.g),
          unpack 3850 12 (wordP2 3850 12 L0 LI0 w.g)) (hsUTab.elt i, hsUTab.elt i)) := by
      unfold genRegs
      rw [hG]
    rw [ht, List.zip_map_right, List.all_map, List.all_eq_true]
    rw [List.all_eq_true] at hw
    intro q hq
    have e := hw q hq
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
    rw [hr, (pWord_unpack hreg cR cRI cidn hidA q.1).1]
    have hq2 : q.2 ∈ L0 := (List.of_mem_zip hq).2
    have cq : CK q.2 := by
      obtain ⟨k, hk, e⟩ := List.getElem_of_mem hq2
      have := gen_canon.1 k
      rw [List.getD_eq_getElem _ _ hk, e] at this
      exact this
    rw [eqA_unpack (pWord_unpack hreg cR cRI cidn hidA q.1).2.1 cq]
    exact e

theorem pcPcomp (p q : Nat) : pc p q = pcomp 3850 12 (mask 12) p q := rfl

theorem pPow_fst {x : PArr} {Y : Nat} (hx : x.1 = unpack 3850 12 Y) (cY : CK Y) :
    ∀ k, (pPow 3850 x k).1 = unpack 3850 12 (pwK k Y) ∧ CK (pwK k Y)
  | 0 => by
    refine ⟨?_, cidn⟩
    change (pId 3850).1 = unpack 3850 12 idn
    rw [pId, hidA]
  | k + 1 => by
    obtain ⟨h1, h2⟩ := pPow_fst hx cY k
    refine ⟨?_, canonK_pcomp cY h2⟩
    have e1 : pwK (k + 1) Y = pc Y (pwK k Y) := by
      unfold pwK
      rfl
    rw [pPow.eq_2, pMul, e1, hx, h1, compA_unpack cY h2, ← pcPcomp]

theorem dim_of {w : DimWit} (h : dimK w = true) : dimWitOK w = true := by
  obtain ⟨hG, cG, cGI⟩ := word_eq w.g
  unfold dimK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd, hc⟩, he⟩, he'⟩, fd⟩, fc⟩, fe⟩, fe'⟩, hcomm⟩, hpow⟩, hne⟩ := h
  set G1 := wordP1 3850 12 L0 LI0 w.g
  set G2 := wordP2 3850 12 L0 LI0 w.g
  have cc := cxE w.c
  have ce := cxE w.e
  have ce' := cxE w.e'
  have cY : CK (pc (pc (pc G1 (xE w.e)) G2) (xE w.e')) :=
    canonK_pcomp (canonK_pcomp (canonK_pcomp cG ce) cGI) ce'
  have hx : (pMul 3850 (pConj 3850 (unpack 3850 12 G1, unpack 3850 12 G2)
      (hsUTab.elt w.e, hsUTab.elt w.e)) (hsUTab.elt w.e', hsUTab.elt w.e')).1 =
      unpack 3850 12 (pc (pc (pc G1 (xE w.e)) G2) (xE w.e')) := by
    rw [elt_eq, elt_eq, pMul, pConj, pMul, pMul, pInv]
    simp only
    rw [compA_unpack cG ce, compA_unpack (canonK_pcomp cG ce) cGI,
      compA_unpack (canonK_pcomp (canonK_pcomp cG ce) cGI) ce']
    rfl
  unfold dimWitOK
  simp only
  rw [hG, hm, fix_get hd, fix_get hc, fix_get he, fix_get he']
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨hd, hc⟩, he⟩, he'⟩, fd⟩, fc⟩, fe⟩, fe'⟩, ?_⟩, ?_⟩
  · rw [pMul, pMul, elt_eq]
    simp only
    rw [compA_unpack cG cc, compA_unpack cc cG, eqA_unpack (canonK_pcomp cG cc) (canonK_pcomp cc cG)]
    exact Nat.beq_eq.mpr hcomm
  · unfold orderCheck
    rw [Bool.and_eq_true]
    obtain ⟨p1, p2⟩ := pPow_fst hx cY 5
    rw [p1, hx, hidA, eqA_unpack p2 cidn, eqA_unpack cY cidn]
    refine ⟨Nat.beq_eq.mpr hpow, ?_⟩
    rw [Bool.not_eq_true']
    exact hne

theorem all_of {α : Type} {L : List α} {f g : α → Bool} (hfg : ∀ a, f a = true → g a = true)
    (h : L.all f = true) : L.all g = true := by
  rw [List.all_eq_true] at h ⊢
  exact fun a ha => hfg a (h a ha)

theorem facts : hsUTab.check 4 = true ∧ hsUTab.forallGreedyI (fun _ => false) 6 [] = true ∧
    hsUTab.forallGreedyI hsPred4 4 [] = true ∧ hsUTab.forallGreedyI hsPred5 5 [] = true ∧
    hsGenWits.all (genWitOK hsGens hsUTab [hsA0A, hsA1A]) = true ∧
    hsDimWits.all dimWitOK = true :=
  ⟨check_true, by rw [search_eq]; exact rank6, by rw [search_eq, pred4_eq]; exact rank4,
    by rw [search_eq, pred5_eq]; exact rank5, all_of (fun _ h => gen_of h) gen,
    all_of (fun _ h => dim_of h) dim⟩

end CertificateChecks.KernelHS3850.UT

end

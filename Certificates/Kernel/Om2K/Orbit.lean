module

public import Certificates.Kernel.Om2K.Rel
public import Certificates.Kernel.Om2K.ChecksO
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import Certificates.Kernel.Om2K.OrbInv
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.SetOrb
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab keyF)

noncomputable abbrev V (i : Nat) : Array Nat := codeArr 9 48 (Orb.C i)

theorem orbOKc_all : ∀ c < 63, orbOKc c = true := by
  intro c hc
  interval_cases c
  exacts [orbOKc0, orbOKc1, orbOKc2, orbOKc3, orbOKc4, orbOKc5, orbOKc6, orbOKc7, orbOKc8,
    orbOKc9, orbOKc10, orbOKc11, orbOKc12, orbOKc13, orbOKc14, orbOKc15, orbOKc16, orbOKc17,
    orbOKc18, orbOKc19, orbOKc20, orbOKc21, orbOKc22, orbOKc23, orbOKc24, orbOKc25, orbOKc26,
    orbOKc27, orbOKc28, orbOKc29, orbOKc30, orbOKc31, orbOKc32, orbOKc33, orbOKc34, orbOKc35,
    orbOKc36, orbOKc37, orbOKc38, orbOKc39, orbOKc40, orbOKc41, orbOKc42, orbOKc43, orbOKc44,
    orbOKc45, orbOKc46, orbOKc47, orbOKc48, orbOKc49, orbOKc50, orbOKc51, orbOKc52, orbOKc53,
    orbOKc54, orbOKc55, orbOKc56, orbOKc57, orbOKc58, orbOKc59, orbOKc60, orbOKc61, orbOKc62]

theorem orb_facts {i : Nat} (hi : i < 6300) :
    codeOK 480 9 48 (Orb.C i) (Orb.M i) = true ∧
      closK 9 48 8 6300 L.G Orb.C Orb.M (fun j => j) Orb.E i = true ∧
      treeK 9 48 8 L.G Orb.C Orb.M (fun j => j) Orb.D i = true := by
  have h := allN_spec (orbOKc_all (i / 100) (by omega)) (i % 100) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 100 (i / 100)) (i % 100) = i := Nat.div_add_mod i 100
  rw [e] at h
  unfold orbOK at h
  obtain ⟨h1, h2⟩ := band h
  exact ⟨h1, band h2⟩

theorem code_ok {i : Nat} (hi : i < 6300) : codeOK 480 9 48 (Orb.C i) (Orb.M i) = true :=
  (orb_facts hi).1

theorem inj_of_ok {P : Nat} (h : okK P = true) :
    ∀ a < 480, ∀ b < 480, pg 9 (mask 9) P a = pg 9 (mask 9) P b → a = b := by
  have h2 := (invEqK_sound (okK_iff h).2.1).2
  unfold isInvA at h2
  rw [allLt_true] at h2
  intro a ha b hb e
  have ea := h2 a ha
  have eb := h2 b hb
  simp only [Bool.and_eq_true, beq_iff_eq] at ea eb
  rw [CFSG.KC.SetOrb.unpack_get ha] at ea
  rw [CFSG.KC.SetOrb.unpack_get hb] at eb
  rw [← ea.2, ← eb.2, e]

theorem act_eq {P i j : Nat} (hP : okK P = true) (hi : i < 6300) (hj : j < 6300)
    (h : imgK 9 48 P (Orb.C i) = Orb.M j) : actFY (unpack 480 9 P) (V i) = V j :=
  act_code (inj_of_ok hP) (code_ok hi) (code_ok hj) h

theorem validFY_codeArr {w len C M : Nat} (h : codeOK 480 w len C M = true) :
    validFY (codeArr w len C) = true := by
  obtain ⟨c1, c2, -⟩ := codeOK_facts h
  have hs : (codeArr w len C).size = len := codeArr_size _ _ _
  unfold validFY
  rw [Bool.and_eq_true, Array.all_eq_true, List.all_eq_true]
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have ht' : t < len := hs ▸ ht
    rw [← getElem!_pos _ t ht, codeArr_get ht']
    exact decide_eq_true (c1 t ht')
  · rw [List.mem_range, hs] at ht
    rw [codeArr_get (by omega), codeArr_get (by omega)]
    exact decide_eq_true (c2 t (by omega))

theorem valid_V {i : Nat} (hi : i < 6300) : validFY (V i) = true := validFY_codeArr (code_ok hi)

theorem key_V (i : Nat) : keyF (V i) = keyK 240 9 48 (Orb.C i) := foldl_code 240 9 _ 48

theorem key_inj {a b : Nat} (ha : a < 6300) (hb : b < 6300) (h : keyF (V a) = keyF (V b)) : a = b := by
  rw [key_V, key_V] at h
  exact distinctK_inj kDist a ha b hb h

theorem cert_of {gs : Array (Array Nat)} {ng N fuel : Nat} {G X Y E D : Nat → Nat}
    {root : Array Nat}
    (hgs : ∀ k < ng, gs[k]! = unpack 480 9 (G k)) (hok : ∀ k < ng, okK (G k) = true)
    (hX : ∀ i < N, X i < 6300) (hcl : ∀ i < N, closK 9 48 ng N G Orb.C Orb.M X E i = true)
    (htr : ∀ i < N, treeK 9 48 ng G Orb.C Orb.M X D i = true) (hinv : ∀ i < N, Y (X i) = i)
    (h0 : 0 < N) (hroot : V (X 0) = root) (hf : N ≤ fuel) :
    arrCertOK (fun k F => actFY gs[k]! F) ng validFY keyF root
        (arrBfs (fun k F => actFY gs[k]! F) ng keyF root fuel) = true ∧
      (∀ x, x ∈ (arrBfs (fun k F => actFY gs[k]! F) ng keyF root fuel).pts ↔
        ∃ i < N, V (X i) = x) ∧
      (arrBfs (fun k F => actFY gs[k]! F) ng keyF root fuel).pts.size = N := by
  refine orbit_of_pinned (V := fun i => V (X i)) (par := fun i => D i % 65536)
    (lab := fun i => D i / 65536) h0 hroot ?_ ?_ (fun i hi => valid_V (hX i hi)) ?_ ?_ hf
  · intro i hi k hk
    obtain ⟨j, hj, e⟩ := closK_spec (hcl i hi) k hk
    refine ⟨j, hj, ?_⟩
    rw [hgs k hk]
    exact act_eq (hok k hk) (hX i hi) (hX j hj) e
  · intro i hi hpos
    obtain ⟨hp, hl, e⟩ := treeK_spec (htr i hi) hpos
    refine ⟨hp, hl, ?_⟩
    rw [hgs _ hl]
    exact (act_eq (hok _ hl) (hX _ (by omega)) (hX i hi) e).symm
  · intro a ha b hb e
    rw [key_inj (hX a ha) (hX b hb) e]
  · intro a ha b hb e
    have e2 := key_inj (hX a ha) (hX b hb) (by rw [e])
    rw [← hinv a ha, ← hinv b hb, e2]

theorem genY_size : (genY (reflTab ())).size = 8 := by simp [genY]

theorem genY_L {k : Nat} (hk : k < 8) : (genY (reflTab ()))[k]! = unpack 480 9 (L.G k) := by
  rw [genY_get hk, Nat.eq_of_beq_eq_true (allN_spec kGY k hk)]

theorem F0_eq : fCodeY (wY LY wT0) = V 0 := by
  unfold fCodeY
  rw [t0_eq, cA_eq (by norm_num)]
  exact filter_code (code_ok (by norm_num)) (Nat.eq_of_beq_eq_true kF0)

theorem main_cert :
    arrCertOK (fun k F => actFY (genY (reflTab ()))[k]! F) 8 validFY keyF (V 0)
        (arrBfs (fun k F => actFY (genY (reflTab ()))[k]! F) 8 keyF (V 0) 6301) = true ∧
      (∀ x, x ∈ (arrBfs (fun k F => actFY (genY (reflTab ()))[k]! F) 8 keyF (V 0) 6301).pts ↔
        ∃ i < 6300, V i = x) ∧
      (arrBfs (fun k F => actFY (genY (reflTab ()))[k]! F) 8 keyF (V 0) 6301).pts.size = 6300 :=
  cert_of (X := fun j => j) (Y := fun j => j) (E := Orb.E) (D := Orb.D) (G := L.G)
    (fun k hk => genY_L hk) (fun k hk => L_ok (by omega)) (fun i hi => hi)
    (fun i hi => (orb_facts hi).2.1) (fun i hi => (orb_facts hi).2.2) (fun i _ => rfl)
    (by norm_num) rfl (by norm_num)

theorem orbit_k : orbitCheckY (reflTab ()) = true := by
  unfold orbitCheckY orbSizeY orbFY
  simp only [Bool.and_eq_true]
  rw [F0_eq, genY_size]
  obtain ⟨h1, -, h3⟩ := main_cert
  refine ⟨valid_V (by norm_num), h1, ?_⟩
  rw [h3]
  rfl

def omS (i : Nat) : Set Nat := {x | (Orb.M i).testBit x = true}

theorem mem_omS {i x : Nat} (hi : i < 6300) :
    x ∈ omS i ↔ ∃ t < 48, pg 9 (mask 9) (Orb.C i) t = x := by
  obtain ⟨-, -, m⟩ := codeOK_facts (code_ok hi)
  change (Orb.M i).testBit x = true ↔ _
  rw [← m, mem_maskK]

theorem omS_lt {i x : Nat} (hi : i < 6300) (hx : x ∈ omS i) : x < 480 := by
  obtain ⟨t, ht, rfl⟩ := (mem_omS hi).1 hx
  exact (codeOK_facts (code_ok hi)).1 t ht

theorem omImg_iff {P i j : Nat} (hi : i < 6300) :
    imgK 9 48 P (Orb.C i) = Orb.M j ↔ (pg 9 (mask 9) P) '' omS i = omS j := by
  have key : ∀ x, (imgK 9 48 P (Orb.C i)).testBit x = true ↔ x ∈ (pg 9 (mask 9) P) '' omS i := by
    intro x
    rw [mem_imgK, Set.mem_image]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, (mem_omS hi).2 ⟨t, ht, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨t, ht, rfl⟩ := (mem_omS hi).1 hy
      exact ⟨t, ht, rfl⟩
  constructor
  · intro h
    ext x
    rw [← key, h]
    rfl
  · intro h
    apply Nat.eq_of_testBit_eq
    intro x
    apply Bool.eq_iff_iff.2
    rw [key, h]
    rfl

theorem omS_inj : ∀ a < 6300, ∀ b < 6300, omS a = omS b → a = b := by
  intro a ha b hb e
  apply key_inj ha hb
  have h : V a = V b := by
    apply Array.ext'
    apply eq_of_pairwise_lt (pairwise_codeArr (code_ok ha)) (pairwise_codeArr (code_ok hb))
    intro x
    rw [mem_codeArr, mem_codeArr, ← mem_omS ha, ← mem_omS hb, e]
  rw [h]

theorem omS_clos8 {k : Nat} (hk : k < 8) :
    ∀ i < 6300, ∃ j < 6300, (pg 9 (mask 9) (L.G k)) '' omS i = omS j := by
  intro i hi
  obtain ⟨j, hj, e⟩ := closK_spec (orb_facts hi).2.1 k hk
  exact ⟨j, hj, (omImg_iff hi).1 e⟩

theorem omPg_inv {k y : Nat} (hk : k < 8) (hy : y < 480) :
    pg 9 (mask 9) (L.G (k + 8)) (pg 9 (mask 9) (L.G k) y) = y := by
  have hp := (okK_iff (L_ok (l := k) (by omega))).2.1
  have e : L.G (k + 8) = pinv (L.G k) := Nat.eq_of_beq_eq_true (allN_spec kInv k hk)
  rw [e]
  unfold permOK at hp
  obtain ⟨-, hp⟩ := band hp
  obtain ⟨-, hp⟩ := band hp
  have h := allN_spec hp y hy
  rw [CFSG.KC.SetOrb.strictB_eq] at h
  exact Nat.eq_of_beq_eq_true (band h).2

theorem omS_clos16 {l : Nat} (hl : l < 16) :
    ∀ i < 6300, ∃ j < 6300, (pg 9 (mask 9) (L.G l)) '' omS i = omS j := by
  by_cases h8 : l < 8
  · exact omS_clos8 h8
  · obtain ⟨k, rfl⟩ : ∃ k, l = k + 8 := ⟨l - 8, by omega⟩
    exact img_inv_closed omS_inj (fun i hi y hy => omPg_inv (by omega) (omS_lt hi hy))
      (omS_clos8 (k := k) (by omega))

theorem omPg_wYK : ∀ w : List Nat, ∀ y < 480, pg 9 (mask 9) (wYK w) y =
    (w.map fun l => pg 9 (mask 9) (L.G l)).foldr (fun f acc => f ∘ acc) id y
  | [], y, hy => CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hy
  | l :: w, y, hy => by
    change pg 9 (mask 9) (pcomp 480 9 (mask 9) (L.G l) (wYK w)) y = _
    rw [CFSG.KS.PF.pg_pcomp (by norm_num) hy, omPg_wYK w y hy]
    rfl

theorem omS_closW {w : List Nat} (hw : ∀ l ∈ w, l < 16) :
    ∀ i < 6300, ∃ j < 6300, imgK 9 48 (wYK w) (Orb.C i) = Orb.M j := by
  intro i hi
  obtain ⟨j, hj, e⟩ := img_word_closed (N := 6300) (S := omS)
    (w.map fun l => pg 9 (mask 9) (L.G l)) (fun f hf => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hf
      exact omS_clos16 (hw l hl)) i hi
  refine ⟨j, hj, (omImg_iff hi).2 ?_⟩
  rw [← e]
  exact Set.image_congr fun y hy => omPg_wYK w y (omS_lt hi hy)

theorem omWS_clos {s : Nat} (hs : s < 12) :
    ∀ i < 6300, ∃ j < 6300, imgK 9 48 (WS.G s) (Orb.C i) = Orb.M j := by
  have hm : wSub.getD s [] ∈ wSub := by
    rw [List.getD_eq_getElem _ _ (by rw [wSub_len]; exact hs)]
    exact List.getElem_mem _
  rw [Nat.eq_of_beq_eq_true (allN_spec kWS s hs)]
  exact omS_closW fun l hl => wSub_lt _ hm l hl

open Classical in
noncomputable def omGIx (R x : Nat) : Nat :=
  if h : ∃ j < 6300, imgK 9 48 R (Orb.C x) = Orb.M j then h.choose else 0

theorem omGIx_spec {s x : Nat} (hs : s < 12) (hx : x < 6300) :
    omGIx (WS.G s) x < 6300 ∧ imgK 9 48 (WS.G s) (Orb.C x) = Orb.M (omGIx (WS.G s) x) := by
  have h := omWS_clos hs x hx
  unfold omGIx
  split
  · next h' => exact h'.choose_spec
  · next h' => exact absurd h h'

noncomputable def omG8 (s : Nat) (X Y : Nat → Nat) (i : Nat) : Nat := Y (omGIx (WS.G s) (X i))

theorem omTr {s N : Nat} {X Y D : Nat → Nat} (hs : s < 12)
    (h : oTransS N X Y D (WS.G s) = true) :
    transOK N X Y (oEP X Y (omG8 s X Y)) D (WS.G s) = true := by
  refine transOK_of_S h fun i hi => ?_
  obtain ⟨-, h⟩ := band h
  obtain ⟨h1, h⟩ := band h
  obtain ⟨-, h⟩ := band h
  obtain ⟨h3, -⟩ := band h
  have hx := Nat.blt_eq.mp (band (allN_spec h1 i hi)).2
  obtain ⟨hj, e⟩ := omGIx_spec hs hx
  obtain ⟨a, b⟩ := band (allN_spec h3 _ hj)
  refine ⟨Nat.blt_eq.mp a, ?_⟩
  unfold omG8
  rw [Nat.eq_of_beq_eq_true b]
  exact e

theorem kTr0 : transOK Tr.c0.N Tr.c0.X Tr.c0.Y (oEP Tr.c0.X Tr.c0.Y (omG8 0 Tr.c0.X Tr.c0.Y))
    Tr.c0.D (WS.G 0) = true := omTr (by norm_num) kTrS0
theorem kTr1 : transOK Tr.c1.N Tr.c1.X Tr.c1.Y (oEP Tr.c1.X Tr.c1.Y (omG8 1 Tr.c1.X Tr.c1.Y))
    Tr.c1.D (WS.G 1) = true := omTr (by norm_num) kTrS1
theorem kTr2 : transOK Tr.c2.N Tr.c2.X Tr.c2.Y (oEP Tr.c2.X Tr.c2.Y (omG8 2 Tr.c2.X Tr.c2.Y))
    Tr.c2.D (WS.G 2) = true := omTr (by norm_num) kTrS2
theorem kTr3 : transOK Tr.c3.N Tr.c3.X Tr.c3.Y (oEP Tr.c3.X Tr.c3.Y (omG8 3 Tr.c3.X Tr.c3.Y))
    Tr.c3.D (WS.G 3) = true := omTr (by norm_num) kTrS3
theorem kTr4 : transOK Tr.c4.N Tr.c4.X Tr.c4.Y (oEP Tr.c4.X Tr.c4.Y (omG8 4 Tr.c4.X Tr.c4.Y))
    Tr.c4.D (WS.G 4) = true := omTr (by norm_num) kTrS4
theorem kTr5 : transOK Tr.c5.N Tr.c5.X Tr.c5.Y (oEP Tr.c5.X Tr.c5.Y (omG8 5 Tr.c5.X Tr.c5.Y))
    Tr.c5.D (WS.G 5) = true := omTr (by norm_num) kTrS5
theorem kTr6 : transOK Tr.c6.N Tr.c6.X Tr.c6.Y (oEP Tr.c6.X Tr.c6.Y (omG8 6 Tr.c6.X Tr.c6.Y))
    Tr.c6.D (WS.G 6) = true := omTr (by norm_num) kTrS6
theorem kTr7 : transOK Tr.c7.N Tr.c7.X Tr.c7.Y (oEP Tr.c7.X Tr.c7.Y (omG8 7 Tr.c7.X Tr.c7.Y))
    Tr.c7.D (WS.G 7) = true := omTr (by norm_num) kTrS7
theorem kTr8 : transOK Tr.c8.N Tr.c8.X Tr.c8.Y (oEP Tr.c8.X Tr.c8.Y (omG8 8 Tr.c8.X Tr.c8.Y))
    Tr.c8.D (WS.G 8) = true := omTr (by norm_num) kTrS8
theorem kTr9 : transOK Tr.c9.N Tr.c9.X Tr.c9.Y (oEP Tr.c9.X Tr.c9.Y (omG8 9 Tr.c9.X Tr.c9.Y))
    Tr.c9.D (WS.G 9) = true := omTr (by norm_num) kTrS9
theorem kTr10 : transOK Tr.c10.N Tr.c10.X Tr.c10.Y
    (oEP Tr.c10.X Tr.c10.Y (omG8 10 Tr.c10.X Tr.c10.Y)) Tr.c10.D (WS.G 10) = true :=
  omTr (by norm_num) kTrS10
theorem kTr11 : transOK Tr.c11.N Tr.c11.X Tr.c11.Y
    (oEP Tr.c11.X Tr.c11.Y (omG8 11 Tr.c11.X Tr.c11.Y)) Tr.c11.D (WS.G 11) = true :=
  omTr (by norm_num) kTrS11

end CertificateChecks.KernelOm2

end

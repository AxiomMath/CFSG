module

public import Certificates.Kernel.GMS78.WChk
public import Certificates.Kernel.Sporadic.OrdCommon
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.SmallF2Rels
public import CFSG.Sporadic.Bridge.VecSurj
public import Certificates.Data.CFSGNative.Ru.Data
public import CFSG.Certificates.Kernel.Orders.Ru.Checks.D
public import CFSG.Certificates.Kernel.Orders.Ru.Checks.K
public import CFSG.Certificates.Kernel.Orders.Ru.Data.Pay
import all CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelGMS78.RuSeedA CFSG.Sporadic.Ru.Native.seedA

#ks_chars CertificateChecks.KernelGMS78.RuSeedB CFSG.Sporadic.Ru.Native.seedB

namespace CertificateChecks.KernelGMS78.W

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.GMSW CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge CFSG.CosetTable
  CFSG.Sporadic.Bridge.VecSurj CFSG.ComponentClassification.GMS78.RuPi7
open CertificateChecks.KernelSpor.SmallF2Rels (mat mat_mul mat_one mat_injective mat_prod mat_inv)

local notation "Dt" => CFSG.Sporadic.Ru.Native.ruData

local notation "Mt" =>
  Matrix (Fin CFSG.Sporadic.Ru.Native.ruData.d) (Fin CFSG.Sporadic.Ru.Native.ruData.d) (ZMod 2)

local notation "MUL" => CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28)
  (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM

noncomputable abbrev Y (M : Nat) : Mt := ordMat 2 28 6 168 M

theorem seed1_bytes :
    CFSG.KS.Bytes.bytesEqK RuSeedA.chars CFSG.KD.OrdRu.P1 256 2349 = true := by
  quickRfl

theorem seed2_bytes :
    CFSG.KS.Bytes.bytesEqK RuSeedB.chars CFSG.KD.OrdRu.P2 256 2349 = true := by
  quickRfl

theorem mA_eq : mA Dt = Y (RG 1) := by
  have h := seed_sound (hnb := rfl) CFSG.KD.OrdRu.consts seed1_bytes (by decide)
    CFSG.KD.OrdRu.d1_0 CFSG.KD.OrdRu.d1_end
  have e : CFSG.KD.OrdRu.RW 1 = RG 1 := (Nat.eq_of_beq_eq_true bindA).symm
  change CFSG.Blueprint.NativeSporadic.decode 2 28 1 CFSG.Sporadic.Ru.Native.seedA = _
  rw [RuSeedA.eq, h]
  exact congrArg Y e

theorem mB_eq : mB Dt = Y (RG 2) := by
  have h := seed_sound (hnb := rfl) CFSG.KD.OrdRu.consts seed2_bytes (by decide)
    CFSG.KD.OrdRu.d2_0 CFSG.KD.OrdRu.d2_end
  have e : CFSG.KD.OrdRu.RW 2 = RG 2 := (Nat.eq_of_beq_eq_true bindB).symm
  change CFSG.Blueprint.NativeSporadic.decode 2 28 1 CFSG.Sporadic.Ru.Native.seedB = _
  rw [RuSeedB.eq, h]
  exact congrArg Y e

theorem hom {R : List (List (Nat × Bool))} {n : Nat} (hb : relsBounded R 9 = true)
    (hall : relsAll RG MUL R 9 CFSG.KD.OrdRu.ONE 0 n = true) (hn : Nat.beq (lenRels R) n = true) :
    (∀ g < 9, Y (RG (g + 1)) * Y (RG (9 + 1 + g)) = 1) ∧
      ∀ v ∈ R, (v.map fun x => Y (letM RG 9 x)).prod = 1 :=
  rels_sound (hnb := rfl) CFSG.KD.OrdRu.consts roots invs hb (relsAll_all hall hn)

theorem inv_reg : ∀ g < 9, Y (RG (g + 1)) * Y (RG (9 + 1 + g)) = 1 := (hom RS_bd RS_all RS_len).1

theorem mat_wordProd {x : ℕ → J Dt} {L0 : Nat} (hL : L0 ≤ 9)
    (hx : ∀ g < L0, mat Dt (x g) = Y (RG (g + 1))) :
    ∀ v : List (ℕ × Bool), (∀ l ∈ v, l.1 < L0) →
      mat Dt (wordProd x v) = (v.map fun l => Y (letM RG 9 l)).prod
  | [], _ => rfl
  | l :: v, h => by
    have ih := mat_wordProd hL hx v fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have hl : l.1 < L0 := h l List.mem_cons_self
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [mat_mul, ih]
    congr 1
    obtain ⟨g, s⟩ := l
    cases s
    · exact mat_inv Dt (hx g hl) (inv_reg g (by omega))
    · exact hx g hl

theorem mat_a : mat Dt (a Dt) = Y (RG 1) := by
  rw [CertificateChecks.KernelSpor.SmallF2Rels.mat_a Dt (N := Y (RG (9 + 1 + 0)))
    (by rw [mA_eq]; exact inv_reg 0 (by norm_num)), mA_eq]

theorem mat_b : mat Dt (b Dt) = Y (RG 2) := by
  rw [CertificateChecks.KernelSpor.SmallF2Rels.mat_b Dt (N := Y (RG (9 + 1 + 1)))
    (by rw [mB_eq]; exact inv_reg 1 (by norm_num)), mB_eq]

@[expose] noncomputable def phi (g : ℕ) : J Dt :=
  if g = 0 then a Dt else if g = 1 then b Dt else img pi7RuSpec (seedG Dt) (g - 2)

theorem phi_img (k : ℕ) : phi (k + 2) = img pi7RuSpec (seedG Dt) k := by
  simp [phi]

theorem mat_phi_lt2 : ∀ g < 2, mat Dt (phi g) = Y (RG (g + 1)) := by
  intro g hg
  interval_cases g
  · simpa [phi] using mat_a
  · simpa [phi] using mat_b

theorem seedG_eq {z : Int} (h : imgLetK z ≠ badLet) :
    seedG Dt z.toNat = if (imgLetK z).2 then phi (imgLetK z).1 else (phi (imgLetK z).1)⁻¹ := by
  obtain ⟨-, hz, e⟩ := imgLetK_of_ne h
  rw [e]
  generalize z.toNat = n at hz ⊢
  interval_cases n <;> simp [seedG, phi]

theorem wordG_seedG (w : List Int) (h : ∀ z ∈ w, imgLetK z ≠ badLet) :
    CFSG.Sporadic.Th.wordG (fun z => seedG Dt z.toNat) w = wordProd phi (w.map imgLetK) := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    simp only [CFSG.Sporadic.Th.wordG, wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih fun z' hz' => h z' (List.mem_cons_of_mem _ hz'), seedG_eq (h z List.mem_cons_self)]

theorem ne_bad {R : List (List (Nat × Bool))} (hb : relsBounded R 9 = true) {v : List (Nat × Bool)}
    (hv : v ∈ R) {l : Nat × Bool} (hl : l ∈ v) : l ≠ badLet := by
  rintro rfl
  have := CFSG.KS.Ord.relsBounded_spec hb v hv _ hl
  exact absurd this (by decide)

theorem RI_eq : RI = mkImgK pi7RuImgWords.toList 0 := relsEqK_eq RI_bind

theorem pi7RuImgWords_getElem (k : ℕ) :
    pi7RuSpec.imgWords[k]! = pi7RuImgWords.toList.getD k [] := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    ← List.getD_eq_getElem?_getD]
  rfl

theorem mat_img {k : ℕ} (hk : k < 7) : mat Dt (img pi7RuSpec (seedG Dt) k) = Y (RG (k + 3)) := by
  have hb := (hom RI_bd RI_all RI_len)
  set w := pi7RuImgWords.toList.getD k [] with hw
  have hmem : ((k + 2, false) :: w.map imgLetK) ∈ RI := by
    rw [RI_eq, mkImgK_eq]
    exact List.mem_map.2 ⟨k, List.mem_range.2 hk, by rw [Nat.zero_add]⟩
  have hbad : ∀ z ∈ w, imgLetK z ≠ badLet := fun z hz =>
    ne_bad RI_bd hmem (List.mem_cons_of_mem _ (List.mem_map_of_mem hz))
  have hlt : ∀ l ∈ w.map imgLetK, l.1 < 2 := by
    intro l hl
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hl
    obtain ⟨-, hz4, e⟩ := imgLetK_of_ne (hbad z hz)
    rw [e]
    simp only
    omega
  have h1 := hb.2 _ hmem
  rw [List.map_cons, List.prod_cons] at h1
  have e : img pi7RuSpec (seedG Dt) k = wordProd phi (w.map imgLetK) := by
    rw [img, pi7RuImgWords_getElem, ← hw, wordG_seedG w hbad]
  rw [e, mat_wordProd (by norm_num) mat_phi_lt2 _ hlt]
  have h2 : Y (letM RG 9 (k + 2, false)) = Y (RG (9 + 1 + (k + 2))) := rfl
  rw [h2] at h1
  calc (List.map (fun l => Y (letM RG 9 l)) (List.map imgLetK w)).prod
      = Y (RG (k + 2 + 1)) * (Y (RG (9 + 1 + (k + 2))) *
          (List.map (fun l => Y (letM RG 9 l)) (List.map imgLetK w)).prod) := by
        rw [← Matrix.mul_assoc, inv_reg (k + 2) (by omega), Matrix.one_mul]
    _ = Y (RG (k + 3)) := by rw [h1, Matrix.mul_one]

theorem mat_phi : ∀ g < 9, mat Dt (phi g) = Y (RG (g + 1)) := by
  intro g hg
  rcases Nat.lt_or_ge g 2 with h | h
  · exact mat_phi_lt2 g h
  · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
    rw [phi_img, mat_img (by omega)]

theorem wordProd_phi_eq_one {R : List (List (Nat × Bool))} {n : Nat} (hb : relsBounded R 9 = true)
    (hall : relsAll RG MUL R 9 CFSG.KD.OrdRu.ONE 0 n = true) (hn : Nat.beq (lenRels R) n = true)
    {v : List (Nat × Bool)} (hv : v ∈ R) : wordProd phi v = 1 := by
  apply mat_injective Dt
  rw [mat_one, mat_wordProd le_rfl mat_phi v (CFSG.KS.Ord.relsBounded_spec hb v hv)]
  exact (hom hb hall hn).2 v hv

theorem wordProd_append (x : ℕ → J Dt) (u v : List (ℕ × Bool)) :
    wordProd x (u ++ v) = wordProd x u * wordProd x v := by
  simp [wordProd, List.map_append, List.prod_append]

theorem wordOfCodes_single {c : ℕ} (hc : c < 14) :
    (wordOfCodes 7 [c]).map (fun l => (l.1.val + 2, l.2)) = [(c / 2 + 2, Nat.beq (c % 2) 0)] := by
  interval_cases c <;> rfl

theorem wordProd_pi7 (w : List (Fin 7 × Bool)) :
    wordProd (img pi7RuSpec (seedG Dt)) (w.map fun l => (l.1.val, l.2)) =
      wordProd phi (w.map fun l => (l.1.val + 2, l.2)) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, phi_img]

theorem codes_rel {R : List (List (Nat × Bool))} {n : Nat} {rs : List (List ℕ)}
    (hb : relsBounded R 9 = true) (hall : relsAll RG MUL R 9 CFSG.KD.OrdRu.ONE 0 n = true)
    (hn : Nat.beq (lenRels R) n = true) (hR : relsEqK R (mkCodesK rs) = true) :
    ∀ c ∈ rs, wordProd (img pi7RuSpec (seedG Dt))
      ((wordOfCodes 7 c).map fun l => (l.1.val, l.2)) = 1 := by
  intro c hc
  have hmem : c.map codeLetK ∈ R := by
    rw [relsEqK_eq hR, mkCodesK_eq]
    exact List.mem_map_of_mem hc
  have hcodes : (wordOfCodes 7 c).map (fun l => (l.1.val + 2, l.2)) = c.map codeLetK := by
    have hc14 : ∀ x ∈ c, codeLetK x ≠ badLet := fun x hx =>
      ne_bad hb hmem (List.mem_map_of_mem hx)
    clear hmem hc
    induction c with
    | nil => rfl
    | cons x c ih =>
      have e : wordOfCodes 7 (x :: c) = wordOfCodes 7 [x] ++ wordOfCodes 7 c := by
        simp [wordOfCodes]
      rw [e, List.map_append, ih fun y hy => hc14 y (List.mem_cons_of_mem _ hy), List.map_cons]
      obtain ⟨hx, ex⟩ := codeLetK_of_ne (hc14 x List.mem_cons_self)
      rw [wordOfCodes_single hx, ex]
      rfl
  rw [wordProd_pi7, hcodes]
  exact wordProd_phi_eq_one hb hall hn hmem

theorem pi7Rels_hold : ∀ r ∈ pi7Rels, wordProd (img pi7RuSpec (seedG Dt))
    (r.map fun l => (l.1.val, l.2)) = 1 := by
  intro r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
  rcases List.mem_append.1 hc with hc | hc
  · rcases List.mem_append.1 hc with hc | hc
    · exact codes_rel RC_bd RC_all RC_len RC_bind c hc
    · exact codes_rel RA_bd RA_all RA_len RA_bind c hc
  · exact codes_rel RE_bd RE_all RE_len RE_bind c hc

theorem imgG_eq {z : Int} (h : sgnLetK z ≠ badLet) :
    imgG pi7RuSpec (seedG Dt) z = if (sgnLetK z).2 then phi (sgnLetK z).1 else (phi (sgnLetK z).1)⁻¹ := by
  obtain ⟨-, -, e⟩ := sgnLetK_of_ne h
  rw [e]
  by_cases hz : 0 < z
  · simp only [imgG, hz, ↓reduceIte]
    rw [phi_img]
  · simp only [imgG, hz, ↓reduceIte, Bool.false_eq_true]
    rw [phi_img]

theorem wordG_imgG (w : List Int) (h : ∀ z ∈ w, sgnLetK z ≠ badLet) :
    CFSG.Sporadic.Th.wordG (imgG pi7RuSpec (seedG Dt)) w = wordProd phi (w.map sgnLetK) := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    simp only [CFSG.Sporadic.Th.wordG, wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih fun z' hz' => h z' (List.mem_cons_of_mem _ hz'), imgG_eq (h z List.mem_cons_self)]

theorem surj {i : ℕ} (hi : i < 2) :
    CFSG.Sporadic.Th.wordG (imgG pi7RuSpec (seedG Dt)) pi7RuSurjWords[i]! = phi i := by
  set w := pi7RuSurjWords.toList.getD i [] with hw
  have hmem : w.map sgnLetK ++ [(i, false)] ∈ RS := by
    rw [relsEqK_eq RS_bind, mkSurjK_eq]
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, by rw [Nat.zero_add]⟩
  have hbad : ∀ z ∈ w, sgnLetK z ≠ badLet := fun z hz =>
    ne_bad RS_bd hmem (List.mem_append_left _ (List.mem_map_of_mem hz))
  have e : pi7RuSurjWords[i]! = w := by
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
      ← List.getD_eq_getElem?_getD]
    rfl
  have h1 := wordProd_phi_eq_one RS_bd RS_all RS_len hmem
  rw [wordProd_append] at h1
  rw [e, wordG_imgG w hbad]
  have h2 : wordProd phi [(i, false)] = (phi i)⁻¹ := by simp [wordProd]
  rw [h2] at h1
  exact mul_inv_eq_one.1 h1

theorem homM {RB : Nat → Nat} {L : Nat} {R : List (List (Nat × Bool))} {n : Nat}
    (hroot : rootsOK RB (CFSG.KC.Ord.validM (nat_lit 2) (nat_lit 4704) CFSG.KD.OrdRu.L
      CFSG.KD.OrdRu.H) 1 (L + 1) = true)
    (hinv : invsOK RB MUL (CFSG.KC.Ord.validM (nat_lit 2) (nat_lit 4704) CFSG.KD.OrdRu.L
      CFSG.KD.OrdRu.H) L CFSG.KD.OrdRu.ONE = true)
    (hb : relsBounded R L = true) (hall : relsAll RB MUL R L CFSG.KD.OrdRu.ONE 0 n = true)
    (hn : Nat.beq (lenRels R) n = true) :
    (∀ g < L, Y (RB (g + 1)) * Y (RB (L + 1 + g)) = 1) ∧
      ∀ v ∈ R, (v.map fun x => Y (letM RB L x)).prod = 1 :=
  rels_sound (hnb := rfl) CFSG.KD.OrdRu.consts hroot hinv hb (relsAll_all hall hn)

theorem mat_wordProdM {RB : Nat → Nat} {L : Nat} (h9 : 9 ≤ L)
    (hsh : ∀ g < 9, RB (g + 1) = RG (g + 1))
    (hinv : ∀ g < L, Y (RB (g + 1)) * Y (RB (L + 1 + g)) = 1) :
    ∀ v : List (ℕ × Bool), (∀ l ∈ v, l.1 < 9) →
      mat Dt (wordProd phi v) = (v.map fun l => Y (letM RB L l)).prod
  | [], _ => rfl
  | l :: v, h => by
    have ih := mat_wordProdM h9 hsh hinv v fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have hl : l.1 < 9 := h l List.mem_cons_self
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [mat_mul, ih]
    congr 1
    obtain ⟨g, s⟩ := l
    have hg : mat Dt (phi g) = Y (RB (g + 1)) := by rw [hsh g hl]; exact mat_phi g hl
    cases s
    · exact mat_inv Dt hg (hinv g (by omega))
    · exact hg

theorem wordProd_ne_one_M {RB : Nat → Nat} {L : Nat} (h9 : 9 ≤ L)
    (hsh : ∀ g < 9, RB (g + 1) = RG (g + 1))
    (hinv : ∀ g < L, Y (RB (g + 1)) * Y (RB (L + 1 + g)) = 1)
    {u : List (ℕ × Bool)} (hu : ∀ l ∈ u, l.1 < 9) {j : ℕ} (hj : 9 + j < L)
    (hrel : ((u ++ [(9 + j, false)]).map fun x => Y (letM RB L x)).prod = 1)
    (hV : Y (RB (9 + j + 1)) ≠ 1) : wordProd phi u ≠ 1 := by
  intro h1
  rw [List.map_append, List.prod_append, ← mat_wordProdM h9 hsh hinv u hu, h1, mat_one,
    Matrix.one_mul] at hrel
  have h2 : Y (letM RB L (9 + j, false)) = Y (RB (L + 1 + (9 + j))) := rfl
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one, h2] at hrel
  apply hV
  calc Y (RB (9 + j + 1)) = Y (RB (9 + j + 1)) * Y (RB (L + 1 + (9 + j))) := by
        rw [hrel, Matrix.mul_one]
    _ = 1 := hinv (9 + j) hj

theorem Y_ne_one {M i j : Nat} (hi : i < 28) (hj : j < 28)
    (h : Nat.beq (Nat.mod (Nat.div M (Nat.pow 2 (168 * i + 6 * j))) 64)
      (if i = j then 0 else 1) = true) : Y M ≠ 1 := by
  intro h1
  have e := congrFun (congrFun h1 ⟨i, hi⟩) ⟨j, hj⟩
  have hv := Nat.eq_of_beq_eq_true h
  have hY : Y M ⟨i, hi⟩ ⟨j, hj⟩ = ((M / 2 ^ (168 * i + 6 * j) % 2 ^ 6 : ℕ) : ZMod 2) := rfl
  have h64 : (2 : ℕ) ^ 6 = 64 := rfl
  rw [hY, h64] at e
  change ((M / 2 ^ (168 * i + 6 * j) % 64 : ℕ) : ZMod 2) = _ at e
  have hv' : M / 2 ^ (168 * i + 6 * j) % 64 = if i = j then 0 else 1 := hv
  rw [hv', Matrix.one_apply] at e
  by_cases hij : i = j
  · subst hij
    simp at e
  · have hne : (⟨i, hi⟩ : Fin CFSG.Sporadic.Ru.Native.ruData.d) ≠ ⟨j, hj⟩ := fun e' =>
      hij (Fin.mk.inj e')
    simp [hij, hne] at e

theorem wordProd_invWord (x : ℕ → J Dt) (w : List (ℕ × Bool)) :
    wordProd x ((w.map fun l => (l.1, !l.2)).reverse) = (wordProd x w)⁻¹ := by
  induction w with
  | nil => simp [wordProd]
  | cons l w ih =>
    rw [List.map_cons, List.reverse_cons, wordProd_append, ih]
    obtain ⟨g, s⟩ := l
    cases s <;> simp [wordProd, mul_inv_rev]

theorem wordProd_finLetK (w : List (Fin 7 × Bool)) :
    wordProd phi (w.map finLetK) = wordProd (img pi7RuSpec (seedG Dt)) (w.map fun l => (l.1.val, l.2)) := by
  rw [wordProd_pi7]
  rfl

theorem pair_eq {R : List (List (Nat × Bool))} {n : Nat} (hb : relsBounded R 9 = true)
    (hall : relsAll RG MUL R 9 CFSG.KD.OrdRu.ONE 0 n = true) (hn : Nat.beq (lenRels R) n = true)
    {u v : List (Fin 7 × Bool)}
    (hv : u.map finLetK ++ ((v.map finLetK).map fun x => (x.1, !x.2)).reverse ∈ R) :
    wordProd (img pi7RuSpec (seedG Dt)) (u.map fun l => (l.1.val, l.2)) =
      wordProd (img pi7RuSpec (seedG Dt)) (v.map fun l => (l.1.val, l.2)) := by
  have h := wordProd_phi_eq_one hb hall hn hv
  rw [wordProd_append, wordProd_invWord, mul_inv_eq_one, wordProd_finLetK, wordProd_finLetK] at h
  exact h

end CertificateChecks.KernelGMS78.W

end

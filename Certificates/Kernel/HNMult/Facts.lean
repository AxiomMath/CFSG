module

public import CFSG.Sporadic.Recognition.HNMultiplierInputs
public import CFSG.Sporadic.HN.F5Chain
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.Commutant
public import Certificates.Kernel.HNMult.Data
public import Certificates.Data.Kernel.HNMultK
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import Certificates.Data.Kernel.SurjK
import Certificates.Kernel.HNMult.ChecksK
import Certificates.Kernel.HNMult.ChecksW0
import Certificates.Kernel.HNMult.ChecksW1
import Certificates.Kernel.HNMult.ChecksW2
import Certificates.Kernel.HNMult.ChecksW3
import Certificates.Kernel.HN3166.Seed
import Certificates.Kernel.VecCert.WordProg
import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.LocalComp.SurjGen
import CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K
import CFSG.Certificates.Kernel.SurjKSound
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Sporadic.Recognition.HNMultiplierInputs
import all CFSG.LieType.Multipliers.CoverWords
import all CFSG.Certificates.CosetTablePresented
import all Certificates.Data.CFSGNative.Bridge.HNGPL
import all Certificates.Data.CFSGNative.HN.Data
meta import Certificates.Data.CFSGNative.Bridge.HNGPL
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Sporadic.Recognition.CoverChainSub
public import CFSG.Sporadic.Th.F2Spec

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelHNMult.ImgT CFSG.Sporadic.Bridge.SurjD.Native.hnImgText

#lc_words CertificateChecks.KernelHNMult.ImgT CFSG.Sporadic.Bridge.SurjD.Native.hnImgText

public section

namespace CertificateChecks.KernelHNMult

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNMult CFSG.KD.HNMult CFSG.Sporadic.F5
open CFSG.Sporadic.Recognition.HNMultiplier CFSG.Sporadic.Bridge.TableSurj
open CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

local notation "OM" =>
  ordMat 5 (CFSG.Sporadic.F5.Native.F5Data.d CFSG.Sporadic.HN.Native.hnData) 13 1729

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem decL_eq (w : List ℕ) : decL w = w.map letC := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    change List.cons (letC c) (decL w) = _
    rw [ih, List.map_cons]

noncomputable def lm (c : ℕ) : Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5) :=
  OM (letM RB 13 (letC c))

noncomputable def Mr (g : ℕ) : Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5) := OM (RB (g + 1))

noncomputable def Mi (g : ℕ) : Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5) := OM (RB (14 + g))

theorem lm_eq (c : ℕ) : lm c = if c % 2 = 1 then Mr (c / 2) else Mi (c / 2) := by
  unfold lm Mr Mi
  rw [CertificateChecks.KernelWP.letC_div]
  by_cases h : c % 2 = 1
  · simp only [h, decide_true, if_true]
    rfl
  · simp only [h, decide_false, if_false]
    change OM (RB (Nat.add (Nat.succ 13) (c / 2))) = _
    rfl

theorem sound {rels : List (List (ℕ × Bool))} (hb : relsBounded rels 13 = true)
    (hr : ∀ r < lenRels rels, relOK RB mul rels 13 CFSG.KD.FamHNSeed.ONE r = true ∨
      ∃ s < r, relDupOK rels s r = true) :
    (∀ g < 13, ordMat 5 133 13 1729 (RB (g + 1)) * ordMat 5 133 13 1729 (RB (13 + 1 + g)) = 1) ∧
      ∀ v ∈ rels, (v.map fun x => ordMat 5 133 13 1729 (letM RB 13 x)).prod = 1 :=
  rels_sound (p := 5) (d := 133) (w := 13) (S := 1729) (T := 9) (L := CFSG.KD.FamHNSeed.L)
    (H := CFSG.KD.FamHNSeed.H) (CM := CFSG.KD.FamHNSeed.CM) (RM := CFSG.KD.FamHNSeed.RM)
    (ONE := CFSG.KD.FamHNSeed.ONE) (LV := CFSG.KD.FamHNSeed.LV) (HV := CFSG.KD.FamHNSeed.HV)
    (nb := 229957) (Lg := 13) (RB := RB) CFSG.KD.FamHNSeed.consts rfl hroots hinv hb hr

theorem pair (g : ℕ) (hg : g < 13) : Mr g * Mi g = 1 := by
  have h := (sound (rels := []) rfl (fun r hr => absurd hr (Nat.not_lt_zero r))).1 g hg
  have e : 13 + 1 + g = 14 + g := by omega
  rw [e] at h
  exact h

theorem relW_one {w : List ℕ} (h : relW RB mul 13 CFSG.KD.FamHNSeed.ONE w = true) :
    (w.map lm).prod = 1 := by
  obtain ⟨hb, hr⟩ := andB_true h
  have hs := (sound hb (fun r hr' => by
      have h1 : r = 0 := by
        have : lenRels (List.cons (decL w) List.nil) = 1 := rfl
        omega
      subst h1
      exact Or.inl hr)).2 (decL w) List.mem_cons_self
  rw [decL_eq, List.map_map] at hs
  exact hs

theorem range_spec {lo : ℕ} :
    ∀ n, relWRange RB mul 13 CFSG.KD.FamHNSeed.ONE WD lo n = true →
      ∀ k < n, relW RB mul 13 CFSG.KD.FamHNSeed.ONE (WD (lo + k)) = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact range_spec n h1 k hk
    · exact h2

theorem range_join {lo n m : ℕ} (h1 : relWRange RB mul 13 CFSG.KD.FamHNSeed.ONE WD lo n = true)
    (h2 : relWRange RB mul 13 CFSG.KD.FamHNSeed.ONE WD (lo + n) m = true) :
    relWRange RB mul 13 CFSG.KD.FamHNSeed.ONE WD lo (n + m) = true := by
  induction m with
  | zero => exact h1
  | succ m ih =>
    obtain ⟨h3, h4⟩ := andB_true h2
    change andB (relWRange RB mul 13 CFSG.KD.FamHNSeed.ONE WD lo (n + m))
      (relW RB mul 13 CFSG.KD.FamHNSeed.ONE (WD (Nat.add lo (n + m)))) = true
    have e : Nat.add lo (n + m) = Nat.add (lo + n) m := by
      change lo + (n + m) = lo + n + m
      omega
    rw [e, ih h3, h4]
    rfl

theorem rj (s n t : ℕ) (ht : s + n = t)
    (h1 : relWRange RB mul 13 CFSG.KD.FamHNSeed.ONE WD 0 s = true)
    (h2 : relWRange RB mul 13 CFSG.KD.FamHNSeed.ONE WD s n = true) :
    relWRange RB mul 13 CFSG.KD.FamHNSeed.ONE WD 0 t = true := by
  have h2' : relWRange RB mul 13 CFSG.KD.FamHNSeed.ONE WD (0 + s) n = true := by
    rwa [Nat.zero_add]
  rw [← ht]
  exact range_join h1 h2'

theorem all_words : relWRange RB mul 13 CFSG.KD.FamHNSeed.ONE WD 0 86 = true := by
  have j4 := rj 2 2 4 rfl w0 w2
  have j5 := rj 4 1 5 rfl j4 w4
  have j6 := rj 5 1 6 rfl j5 w5
  have j7 := rj 6 1 7 rfl j6 w6
  have j8 := rj 7 1 8 rfl j7 w7
  have j10 := rj 8 2 10 rfl j8 w8
  have j24 := rj 10 14 24 rfl j10 w10
  have j47 := rj 24 23 47 rfl j24 w24
  have j53 := rj 47 6 53 rfl j47 w47
  have j57 := rj 53 4 57 rfl j53 w53
  have j60 := rj 57 3 60 rfl j57 w57
  have j62 := rj 60 2 62 rfl j60 w60
  have j64 := rj 62 2 64 rfl j62 w62
  have j65 := rj 64 1 65 rfl j64 w64
  have j74 := rj 65 9 74 rfl j65 w65
  have j82 := rj 74 8 82 rfl j74 w74
  have j84 := rj 82 2 84 rfl j82 w82
  have j85 := rj 84 1 85 rfl j84 w84
  exact rj 85 1 86 rfl j85 w85

theorem word_one {k : ℕ} (hk : k < 86) : ((WD k).map lm).prod = 1 := by
  have h := range_spec 86 all_words k hk
  rw [Nat.zero_add] at h
  exact relW_one h

theorem mul_comm_of_one {d : ℕ} {A B : Matrix (Fin d) (Fin d) (ZMod 5)} (h : A * B = 1) :
    B * A = 1 :=
  mul_eq_one_comm.mp h

theorem word_root {k g : ℕ} (hk : k < 86) (hg : g < 13) {u : List ℕ} (hu : WD k = u ++ [2 * g]) :
    (u.map lm).prod = Mr g := by
  have h := word_one hk
  rw [hu, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
    lm_eq, if_neg (by omega : ¬ 2 * g % 2 = 1), Nat.mul_div_cancel_left g (by norm_num)] at h
  have h2 : Mi g * Mr g = 1 := mul_comm_of_one (pair g hg)
  calc (u.map lm).prod = (u.map lm).prod * (Mi g * Mr g) := by rw [h2, mul_one]
    _ = Mr g := by rw [← mul_assoc, h, one_mul]

@[expose] def slpCode (z : ℤ) : ℕ :=
  2 * (if z.natAbs ≤ 2 then z.natAbs - 1 else z.natAbs - 3) + (if 0 < z then 1 else 0)

@[expose] def cc (l : ℕ) : ℕ := if l % 2 = 0 then 2 * (l / 2) + 1 else 2 * (l / 2)

@[expose] def chainCode (z : ℤ) : ℕ := cc z.toNat

@[expose] def genCode (l : ℕ × Bool) : ℕ := 2 * (6 + l.1) + (if l.2 then 1 else 0)

theorem tie_gs : ∀ g < 6, 2 ≤ g → WD (g - 2) = (Dt).words[g]!.map slpCode ++ [2 * g] := by
  decide +kernel

theorem bnd_gs : ∀ g < 6, ∀ z ∈ (Dt).words[g]!,
    (z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) ∨ (3 ≤ z.natAbs ∧ z.natAbs - 3 < g) := by
  decide +kernel

theorem words01 : (Dt).words[0]! = [1] ∧ (Dt).words[1]! = [2] := by
  decide +kernel

theorem wordsK_img : CFSG.KC.SurjK.wordsK ImgT.chars ImgT.W = true := by quickRfl

theorem imgWords_eq : hnSpec.imgWords = ImgT.W.toArray := by
  have h := CFSG.KC.SurjK.wordsK_sound wordsK_img
  rw [← ImgT.eq] at h
  exact h

@[expose] def tabImgOf (I : Array (List ℤ)) : Array (List ℤ) :=
  #[I[1]!, I[2]! ++ I[1]! ++ invChainWord I[2]!, I[2]!, I[3]! ++ I[2]! ++ I[3]!, I[0]!, I[3]!,
    I[4]!]

theorem tabImg_eq : hnTabImg = tabImgOf ImgT.W.toArray := by
  unfold hnTabImg
  rw [imgWords_eq]
  rfl

theorem tie_img : ∀ i < 7,
    WD (4 + i) = (tabImgOf ImgT.W.toArray)[i]!.map chainCode ++ [2 * (6 + i)] := by
  decide +kernel

theorem bnd_img : ∀ i < 7, ∀ z ∈ (tabImgOf ImgT.W.toArray)[i]!, 0 ≤ z ∧ z < 12 := by
  decide +kernel

theorem tie_rels : hnTabRels.map (fun r => r.map genCode) =
    (List.range 73).map fun k => WD (11 + k) := by
  decide +kernel

theorem tie_surj : (∃ u, WD 84 = u ++ [0] ∧ ∀ c ∈ u, 12 ≤ c ∧ c < 26) ∧
    (∃ u, WD 85 = u ++ [2] ∧ ∀ c ∈ u, 12 ≤ c ∧ c < 26) :=
  ⟨⟨(WD 84).dropLast, by decide +kernel, by decide +kernel⟩,
    ⟨(WD 85).dropLast, by decide +kernel, by decide +kernel⟩⟩

noncomputable abbrev gf (i : ℕ) : J Dt := img hnTabSpec (CFSG.Perm.pairG (gs Dt)) i

noncomputable def E (g : ℕ) : J Dt := if g < 6 then gs Dt g else gf (g - 6)

noncomputable def el (c : ℕ) : J Dt := if c % 2 = 1 then E (c / 2) else (E (c / 2))⁻¹

noncomputable abbrev matHom : J Dt →* Matrix (Fin (Dt).d) (Fin (Dt).d) (ZMod 5) :=
  (Units.coeHom _).comp (J Dt).subtype

theorem mat_eq (x : J Dt) : mat Dt x = matHom x := rfl

theorem mat_prod (l : List (J Dt)) : mat Dt l.prod = (l.map (mat Dt)).prod := by
  rw [mat_eq, map_list_prod]
  rfl

theorem mat_inv_of {x : J Dt} {g : ℕ} (hg : g < 13) (hx : mat Dt x = Mr g) :
    mat Dt x⁻¹ = Mi g := by
  have h1 : mat Dt x⁻¹ * mat Dt x = 1 := by
    rw [mat_eq, mat_eq, ← map_mul, inv_mul_cancel, map_one]
  calc mat Dt x⁻¹ = mat Dt x⁻¹ * (Mr g * Mi g) := by rw [pair g hg, mul_one]
    _ = Mi g := by rw [← mul_assoc, ← hx, h1, one_mul]

theorem mat_el_of {c : ℕ} (hc : c / 2 < 13) (h : mat Dt (E (c / 2)) = Mr (c / 2)) :
    mat Dt (el c) = lm c := by
  rw [lm_eq]
  unfold el
  split_ifs
  · exact h
  · exact mat_inv_of hc h

theorem mat_a : mat Dt (a Dt) = Mr 0 := by
  rw [mat_a' CertificateChecks.KernelHN.det_mA, CertificateChecks.KernelHN.s_mA]
  exact congrArg OM (Nat.eq_of_beq_eq_true hA).symm

theorem mat_b : mat Dt (b Dt) = Mr 1 := by
  rw [mat_b' CertificateChecks.KernelHN.det_mB, CertificateChecks.KernelHN.s_mB]
  exact congrArg OM (Nat.eq_of_beq_eq_true hB).symm

theorem gs0 : gs Dt 0 = a Dt := by
  unfold gs
  rw [CFSG.Sporadic.Fi23.slpG_eq, words01.1]
  simp [wordG, genG]

theorem gs1 : gs Dt 1 = b Dt := by
  unfold gs
  rw [CFSG.Sporadic.Fi23.slpG_eq, words01.2]
  simp [wordG, genG]

theorem mat_wordG {f : ℤ → J Dt} (w : List ℤ) :
    mat Dt (wordG f w) = (w.map fun z => mat Dt (f z)).prod := by
  unfold wordG
  rw [mat_prod, List.map_map]
  rfl

theorem mat_gs : ∀ g < 6, mat Dt (gs Dt g) = Mr g := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hg
    rcases Nat.lt_or_ge g 2 with h2 | h2
    · interval_cases g
      · rw [gs0, mat_a]
      · rw [gs1, mat_b]
    · have hw := word_root (k := g - 2) (by omega) (by omega) (tie_gs g hg h2)
      rw [← hw]
      unfold gs
      rw [CFSG.Sporadic.Fi23.slpG_eq, mat_wordG, List.map_map]
      congr 1
      refine List.map_congr_left fun z hz => ?_
      beta_reduce
      change _ = lm (slpCode z)
      rw [lm_eq]
      have hai := mat_inv_of (x := a Dt) (g := 0) (by norm_num) mat_a
      have hbi := mat_inv_of (x := b Dt) (g := 1) (by norm_num) mat_b
      rcases bnd_gs g hg z hz with (rfl | rfl | rfl | rfl) | ⟨h3, h4⟩
      · simp [genG, slpCode, mat_a]
      · simp [genG, slpCode, hai]
      · simp [genG, slpCode, mat_b]
      · simp [genG, slpCode, hbi]
      · have hz2 : ¬ z.natAbs ≤ 2 := by omega
        rw [if_neg hz2, if_pos h4]
        have hk : slpCode z / 2 = z.natAbs - 3 := by
          unfold slpCode
          rw [if_neg hz2]
          split_ifs <;> omega
        rw [hk]
        have hg' := ih (z.natAbs - 3) h4 (by omega)
        by_cases hp : 0 < z
        · have hc : slpCode z % 2 = 1 := by
            unfold slpCode
            rw [if_neg hz2, if_pos hp]
            omega
          rw [if_pos hp, if_pos hc]
          exact hg'
        · have hc : ¬ slpCode z % 2 = 1 := by
            unfold slpCode
            rw [if_neg hz2, if_neg hp]
            omega
          rw [if_neg hp, if_neg hc]
          exact mat_inv_of (by omega) hg'

theorem mat_pairG {l : ℕ} (hl : l < 12) : mat Dt (CFSG.Perm.pairG (gs Dt) l) = lm (cc l) := by
  unfold CFSG.Perm.pairG cc
  by_cases h : l % 2 = 0
  · have hc : (2 * (l / 2) + 1) % 2 = 1 := by omega
    have hd : (2 * (l / 2) + 1) / 2 = l / 2 := by omega
    rw [if_pos h, if_pos h, lm_eq, if_pos hc, hd]
    exact mat_gs _ (by omega)
  · have hc : ¬ (2 * (l / 2)) % 2 = 1 := by omega
    rw [if_neg h, if_neg h, lm_eq, if_neg hc, Nat.mul_div_cancel_left _ (by norm_num)]
    exact mat_inv_of (by omega) (mat_gs _ (by omega))

theorem mat_gf : ∀ i < 7, mat Dt (gf i) = Mr (6 + i) := by
  intro i hi
  have hw := word_root (k := 4 + i) (by omega) (by omega) (tie_img i hi)
  rw [← hw]
  unfold gf img
  rw [mat_wordG, List.map_map]
  change ((hnTabImg[i]!).map _).prod = _
  rw [tabImg_eq]
  congr 1
  refine List.map_congr_left fun z hz => ?_
  obtain ⟨h0, h12⟩ := bnd_img i hi z hz
  exact mat_pairG (l := z.toNat) (by omega)

theorem mat_E : ∀ g < 13, mat Dt (E g) = Mr g := by
  intro g hg
  unfold E
  split_ifs with h
  · exact mat_gs g h
  · have h6 := mat_gf (g - 6) (by omega)
    have e : 6 + (g - 6) = g := by omega
    rw [e] at h6
    exact h6

theorem mat_el {c : ℕ} (hc : c < 26) : mat Dt (el c) = lm c :=
  mat_el_of (by omega) (mat_E _ (by omega))

theorem wordProd_gf (v : List (ℕ × Bool)) (hv : ∀ l ∈ v, l.1 < 7) :
    mat Dt (CFSG.Sporadic.Bridge.wordProd gf v) = ((v.map genCode).map lm).prod := by
  unfold CFSG.Sporadic.Bridge.wordProd
  rw [mat_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun l hl => ?_
  obtain ⟨i, s⟩ := l
  have h7 : i < 7 := hv _ hl
  have hE : mat Dt (gf i) = Mr (6 + i) := mat_gf i h7
  cases s
  · change mat Dt (gf i)⁻¹ = lm (genCode (i, false))
    have hc : genCode (i, false) = 2 * (6 + i) := by simp [genCode]
    rw [hc, lm_eq, if_neg (by omega : ¬ 2 * (6 + i) % 2 = 1),
      Nat.mul_div_cancel_left _ (by norm_num)]
    exact mat_inv_of (by omega) hE
  · change mat Dt (gf i) = lm (genCode (i, true))
    have hc : genCode (i, true) = 2 * (6 + i) + 1 := by simp [genCode]
    rw [hc, lm_eq, if_pos (by omega : (2 * (6 + i) + 1) % 2 = 1),
      (by omega : (2 * (6 + i) + 1) / 2 = 6 + i)]
    exact hE

theorem rels_one : ∀ v ∈ hnTabRels, CFSG.Sporadic.Bridge.wordProd gf v = 1 := by
  intro v hv
  have hb : ∀ l ∈ v, l.1 < 7 := by
    have hv' := hv
    unfold hnTabRels at hv'
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hv'
    intro l hl
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
    exact x.1.2
  have hm : v.map genCode ∈ (List.range 73).map fun k => WD (11 + k) := by
    rw [← tie_rels]
    exact List.mem_map_of_mem hv
  obtain ⟨k, hk, e⟩ := List.mem_map.1 hm
  apply mat_injective Dt
  rw [wordProd_gf v hb, ← e, word_one (by rw [List.mem_range] at hk; omega)]
  rfl

theorem closure_gf : Subgroup.closure (Set.range fun i : Fin 7 => gf i.val) = ⊤ := by
  have hmem : ∀ c, 12 ≤ c → c < 26 →
      el c ∈ Subgroup.closure (Set.range fun i : Fin 7 => gf i.val) := by
    intro c h1 h2
    have he : E (c / 2) = gf (c / 2 - 6) := by
      unfold E
      rw [if_neg (by omega)]
    have hin : gf (c / 2 - 6) ∈ Subgroup.closure (Set.range fun i : Fin 7 => gf i.val) :=
      Subgroup.subset_closure ⟨⟨c / 2 - 6, by omega⟩, rfl⟩
    unfold el
    rw [he]
    split_ifs
    · exact hin
    · exact Subgroup.inv_mem _ hin
  have hword : ∀ {k g : ℕ} {u : List ℕ}, k < 86 → g < 2 → WD k = u ++ [2 * g] →
      (∀ c ∈ u, 12 ≤ c ∧ c < 26) → mat Dt (u.map el).prod = Mr g := by
    intro k g u hk hg hu hc
    rw [mat_prod, List.map_map, ← word_root hk (by omega) hu]
    congr 1
    exact List.map_congr_left fun c hc' => mat_el (hc c hc').2
  have hprod : ∀ u : List ℕ, (∀ c ∈ u, 12 ≤ c ∧ c < 26) →
      (u.map el).prod ∈ Subgroup.closure (Set.range fun i : Fin 7 => gf i.val) := by
    intro u hu
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    exact hmem c (hu c hc).1 (hu c hc).2
  obtain ⟨⟨uA, hA', hcA⟩, ⟨uB, hB', hcB⟩⟩ := tie_surj
  have ha : a Dt = (uA.map el).prod :=
    mat_injective Dt
      (mat_a.trans (hword (k := 84) (g := 0) (by norm_num) (by norm_num) hA' hcA).symm)
  have hb : b Dt = (uB.map el).prod :=
    mat_injective Dt
      (mat_b.trans (hword (k := 85) (g := 1) (by norm_num) (by norm_num) hB' hcB).symm)
  rw [eq_top_iff, ← closure_ab Dt, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · rw [ha]
    exact hprod uA hcA
  · rw [hb]
    exact hprod uB hcB

theorem facts :
    (∀ r ∈ CFSG.Sporadic.Recognition.HNMultiplier.hnRels,
      FreeGroup.lift (fun i : Fin 7 => gf i.val) (FreeGroup.mk r) = 1) ∧
      (∀ i, FreeGroup.lift (fun j : Fin 7 => gf j.val) (FreeGroup.mk (hnCommWord i)) = gf i.val) ∧
      Subgroup.closure (Set.range fun i : Fin 7 => gf i.val) = ⊤ := by
  refine ⟨fun r hr => ?_, fun i => ?_, closure_gf⟩
  · rw [CFSG.LieType.Multipliers.lift_mk_eq_wordProd]
    exact rels_one _ (List.mem_map.2 ⟨r, List.mem_append_left _ hr, rfl⟩)
  · exact CFSG.LieType.Multipliers.lift_mk_eq_of_wordProd gf (rels_one _ (List.mem_map.2
      ⟨hnCommWord i ++ [(i, false)], List.mem_append_right _
        (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩), rfl⟩))

end CertificateChecks.KernelHNMult

end

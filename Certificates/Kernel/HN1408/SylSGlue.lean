module

public import Certificates.Kernel.HN1408.SylSBase
public import Certificates.Kernel.HN1408.SylSA
public import Certificates.Kernel.HN1408.SylSLink
public import Certificates.Kernel.HN1408.Glue
public import CFSG.Certificates.Kernel.Spor.RecGroup
public import CFSG.Certificates.Kernel.Spor.BaseMaskGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.WordSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.E64Family
public import CFSG.GroupTheory.ElemAbelianClosure
import Certificates.Kernel.HN1408.SylSSl0
import Certificates.Kernel.HN1408.SylSSl1
import Certificates.Kernel.HN1408.SylSSl2
import Certificates.Kernel.HN1408.SylSSl3
import Certificates.Kernel.HN1408.SylSSl4
import Certificates.Kernel.HN1408.SylSSl5
import Certificates.Kernel.HN1408.SylSSl6
import Certificates.Kernel.HN1408.SylSSl7
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Spor.BaseMaskSound

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.SylSG

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
  CFSG.KS.BaseMask CFSG.KS.RecGroup CFSG.KD.HN1408 CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
  CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem perm_gens : ∀ g ∈ h1408Gens, CFSG.Sporadic.SmallOddCore.permOK 1408 g = true := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := mem_gens hg
  exact (Bool.and_eq_true_iff.mp (gen_ok hj)).1

theorem rep_word {wd : List ℕ} (hw : lettersOK wd = true) :
    Rep 1408 (tabT (unpack 1408 11 (WK wd))) (elemW wd) ∧ Cn (WK wd) := by
  obtain ⟨e, c⟩ := tabW_eq hw
  have hw' : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ h1408Gens.length := by
    rw [h1408Gens_length]
    exact lettersOK_spec hw
  have h' := rep_wordTbl'' (n := 1408) (by norm_num) perm_gens wd hw'
  rw [h1408Gens_map_tp] at h'
  refine ⟨?_, c⟩
  rw [← e]
  exact h'

theorem pt_rep {X : ℕ} {σ : Equiv.Perm (Fin 1408)} (hX : Cn X)
    (h : Rep 1408 (tabT (unpack 1408 11 X)) σ) {p : ℕ} (hp : p < 1408) :
    pg 11 (mask 11) X p = idx 1408 σ p :=
  (ap_eq hX hp).symm.trans (h p hp)

theorem pt_pair {X Y : ℕ} {σ τ : Equiv.Perm (Fin 1408)} (hX : Cn X)
    (hσ : Rep 1408 (tabT (unpack 1408 11 X)) σ) (hY : Cn Y)
    (hτ : Rep 1408 (tabT (unpack 1408 11 Y)) τ) {p : ℕ} (hp : p < 1408) :
    pg 11 (mask 11) X (pg 11 (mask 11) Y p) = idx 1408 (σ * τ) p := by
  have hlt : pg 11 (mask 11) Y p < 1408 := by
    rw [pt_rep hY hτ hp]
    exact idx_lt _ hp
  rw [idx_mul, ← pt_rep hY hτ hp, pt_rep hX hσ hlt]

theorem sWords_length : sWords.length = 5 := by decide

theorem uWords_length : uWords.length = 6 := by decide

theorem sWords_letters : ∀ j < 5, lettersOK (sWords.getD j []) = true := by decide

theorem uWords_letters : ∀ j < 6, lettersOK (uWords.getD j []) = true := by decide

theorem image_getD (ws : List (List ℕ)) :
    (fun j => elemW (ws.getD j [])) '' {j | j < ws.length} = elemW '' {w | w ∈ ws} := by
  ext z
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨ws.getD j [], ?_, rfl⟩
    rw [Set.mem_setOf_eq, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    refine ⟨j, hj, ?_⟩
    beta_reduce
    rw [List.getD_eq_getElem _ _ hj]

theorem gen_rep : ∀ j < 5, canonK 1408 11 (mask 11) (1408 * 11) (SylS.G j) = true ∧
    Rep 1408 (tabT (unpack 1408 11 (SylS.G j))) (elemW (sWords.getD j [])) := by
  intro j hj
  have e : SylS.G j = WK (sWords.getD j []) :=
    Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 sylS_gens j hj)
  obtain ⟨r, c⟩ := rep_word (sWords_letters j hj)
  rw [e]
  exact ⟨c, r⟩

theorem slS_all : ∀ s < 8, slS s = true := by
  intro s hs
  interval_cases s
  exacts [slS_0, slS_1, slS_2, slS_3, slS_4, slS_5, slS_6, slS_7]

theorem penumPt_all : ∀ i < 2048, penumPtK 1408 11 (mask 11) (1408 * 11) false SylS.G SylS.GI 5
    2048 SylS.T SylS.PL SylS.POS SylS.SRT SylS.SRI i = true := by
  intro i hi
  have h := slS_all (i / 256) (by omega)
  unfold slS at h
  rw [sylS_cnt] at h
  exact penumSl_spec h (by change 256 * (i / 256) ≤ i; omega)
    (by change i < 256 * (i / 256) + 256; omega) hi

structure RecS (x : ℕ → Equiv.Perm (Fin 1408)) : Prop where
  one : x 0 = 1
  rep : ∀ i < 2048, Rep 1408 (tabT (unpack 1408 11 (SylS.T i))) (x i)
  canon : ∀ i < 2048, Cn (SylS.T i)
  inj : ∀ a < 2048, ∀ b < 2048, x a = x b → a = b
  mem : ∀ y, y ∈ wordSubgroup sWords ↔ ∃ i < 2048, x i = y

theorem exists_recS : ∃ x, RecS x := by
  have hp := penumPt_all
  obtain ⟨x, h0, hr, hi, hm, -⟩ := penumLeft_closure (n := 1408) (w := 11) (k := 5) (cnt := 2048)
    (cap := 4096) (G := SylS.G) (GI := SylS.GI) (T := SylS.T) (PL := SylS.PL) (POS := SylS.POS)
    (SRT := SylS.SRT) (SRI := SylS.SRI) (g := fun j => elemW (sWords.getD j [])) hn
    (by norm_num) gen_rep (by rw [← sylS_cnt]; exact sylS_hd) hp
  have hcl : closure ((fun j => elemW (sWords.getD j [])) '' {j | j < 5}) =
      wordSubgroup sWords := by
    have e := image_getD sWords
    rw [sWords_length] at e
    rw [e]
    rfl
  refine ⟨x, ⟨h0, hr, fun i hi => (penumPt_specH (hp i hi)).1, hi, fun y => ?_⟩⟩
  rw [← hcl]
  exact hm y

@[expose] noncomputable def memG (x : ℕ → Equiv.Perm (Fin 1408)) (I : ℕ → ℕ) (o k : ℕ) :
    Subgroup (Equiv.Perm (Fin 1408)) :=
  closure ((fun j => x (r32 I (o + 2 ^ j))) '' {j | j < k})

@[expose] noncomputable def memP (x : ℕ → Equiv.Perm (Fin 1408)) (I : ℕ → ℕ) (o k : ℕ) :
    Subgroup ↥P1408 :=
  (memG x I o k).subgroupOf P1408

theorem mem_memP {x : ℕ → Equiv.Perm (Fin 1408)} {I : ℕ → ℕ} {o k : ℕ} {z : ↥P1408} :
    z ∈ memP x I o k ↔ (z : Equiv.Perm (Fin 1408)) ∈ memG x I o k :=
  Iff.rfl

theorem card_memP {x : ℕ → Equiv.Perm (Fin 1408)} {I : ℕ → ℕ} {o k : ℕ}
    (h : memG x I o k ≤ P1408) : Nat.card (memP x I o k) = Nat.card (memG x I o k) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

@[expose] def fam (x : ℕ → Equiv.Perm (Fin 1408)) : Set (Subgroup ↥P1408) :=
  {B | ∃ k, 2 ≤ k ∧ k ≤ 6 ∧ ∃ h < famCnt k, B = memP x SylS.FM (famOff k + h * 2 ^ k) k}

@[expose] def topBit (e : ℕ) : ℕ :=
  if e < 2 then 0 else if e < 4 then 1 else if e < 8 then 2 else if e < 16 then 3 else
    if e < 32 then 4 else 5

theorem topBit_spec : ∀ e < 64, 0 < e → e ^^^ 2 ^ topBit e < e ∧
    ∀ k ≤ 6, e < 2 ^ k → topBit e < k := by
  decide

theorem layer_ok : ∀ k, 2 ≤ k → k ≤ 6 → famLayerOK k = true := by
  intro k h2 h6
  interval_cases k
  exacts [fam_layer2, fam_layer3, fam_layer4, fam_layer5, fam_layer6]

theorem layer_spec {k h : ℕ} (h2 : 2 ≤ k) (h6 : k ≤ 6) (hh : h < famCnt k) :
    memberK 11 (mask 11) 2 0 2048 SylS.T SylS.FM (famOff k + h * 2 ^ k) k = true ∧
      extK SylS.FM SylS.FG SylS.CM ivMask (famOff k + h * 2 ^ k) (famGOff k + h * k) k
        (famOff (k + 1)) (famCnt (k + 1)) = true := by
  have hL := layer_ok k h2 h6
  unfold famLayerOK at hL
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.allN_iff] at hL
  have hx := hL h hh
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hx
  have e : Nat.shiftLeft 1 k = 2 ^ k := Nat.one_shiftLeft k
  rw [e] at hx
  exact hx

theorem gen_link {k h j : ℕ} (h2 : 2 ≤ k) (h6 : k ≤ 6) (hh : h < famCnt k) (hj : j < k) :
    r32 SylS.FG (famGOff k + h * k + j) < nGD ∧
      r32 SylS.GD (r32 SylS.FG (famGOff k + h * k + j)) =
        r32 SylS.FM (famOff k + h * 2 ^ k + 2 ^ j) := by
  have hg := CFSG.KS.Raw.Orb.allN_iff.1 fam_gen (k - 2) (by omega)
  have ek : Nat.add (k - 2) 2 = k := by
    change k - 2 + 2 = k
    omega
  rw [ek] at hg
  unfold famGenOK at hg
  have h3 := CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 hg h hh) j hj
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h3
  have e1 : Nat.shiftLeft 1 k = 2 ^ k := Nat.one_shiftLeft k
  have e2 : Nat.shiftLeft 1 j = 2 ^ j := Nat.one_shiftLeft j
  rw [e1, e2] at h3
  exact ⟨Nat.blt_eq.mp h3.1, Nat.eq_of_beq_eq_true h3.2⟩

theorem cm_spec {t : ℕ} (ht : t < nGD) {u : ℕ} (hu : u < nIV) :
    hasBit (SylS.CM t) (r32 SylS.IV u) = true ↔
      commKeyK 11 (mask 11) 2 0 SylS.T (r32 SylS.IV u) (r32 SylS.GD t) = true := by
  have h := sylS_cm
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.allN_iff] at h
  exact (cmaskK_spec (h t ht)).2 u hu

theorem sylS_A_parts : memberK 11 (mask 11) 2 0 2048 SylS.T SylS.FA 0 6 = true ∧
    (∀ j < 6, SylS.T (r32 SylS.FA (2 ^ j)) = WK (uWords.getD j [])) ∧
      maskK SylS.FA 0 64 = maskK SylS.FM 6188 64 := by
  have h := sylS_A
  rw [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨h.1, fun j hj => ?_, Nat.eq_of_beq_eq_true h.2.2⟩
  have hj' := CFSG.KS.Raw.Orb.allN_iff.1 h.2.1 j hj
  have e2 : Nat.shiftLeft 1 j = 2 ^ j := Nat.one_shiftLeft j
  rw [e2] at hj'
  exact Nat.eq_of_beq_eq_true hj'

theorem sylS_conj_parts : conjMemK 11 (mask 11) 2 0 SylS.T SylS.FA SylS.FC (r32 SylS.Y 0) 64 =
    true ∧ maskK SylS.FC 0 64 = maskK SylS.FM 6252 64 := by
  have h := sylS_conj
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem coe_conj (y w : ↥P1408) :
    (((MulAut.conj y).toMonoidHom w : ↥P1408) : Equiv.Perm (Fin 1408)) =
      (y : Equiv.Perm (Fin 1408)) * w * (y : Equiv.Perm (Fin 1408))⁻¹ := by
  simp

theorem map_conj_one (H : Subgroup ↥P1408) : H.map (MulAut.conj 1).toMonoidHom = H := by
  ext z
  simp

theorem getD4_mem : sWords.getD 4 [] ∈ sWords := by
  rw [List.getD_eq_getElem sWords [] (n := 4) (by rw [sWords_length]; norm_num)]
  exact List.getElem_mem _

namespace RecS

variable {x : ℕ → Equiv.Perm (Fin 1408)} (R : RecS x)
include R

theorem mem_S {i : ℕ} (hi : i < 2048) : x i ∈ wordSubgroup sWords :=
  (R.mem _).2 ⟨i, hi, rfl⟩

theorem pt {i p : ℕ} (hi : i < 2048) (hp : p < 1408) :
    pg 11 (mask 11) (SylS.T i) p = idx 1408 (x i) p :=
  pt_rep (R.canon i hi) (R.rep i hi) hp

theorem pair {i j p : ℕ} (hi : i < 2048) (hj : j < 2048) (hp : p < 1408) :
    pg 11 (mask 11) (SylS.T i) (pg 11 (mask 11) (SylS.T j) p) = idx 1408 (x i * x j) p :=
  pt_pair (R.canon i hi) (R.rep i hi) (R.canon j hj) (R.rep j hj) hp

theorem eq_of_base {σ τ : Equiv.Perm (Fin 1408)} (hσ : σ ∈ wordSubgroup sWords)
    (hτ : τ ∈ wordSubgroup sWords) (h2 : idx 1408 σ 2 = idx 1408 τ 2)
    (h0 : idx 1408 σ 0 = idx 1408 τ 0) : σ = τ := by
  obtain ⟨a, ha, rfl⟩ := (R.mem σ).1 hσ
  obtain ⟨b, hb, rfl⟩ := (R.mem τ).1 hτ
  have hk : bkeyK 1408 11 (mask 11) 2 0 (SylS.T a) = bkeyK 1408 11 (mask 11) 2 0 (SylS.T b) := by
    unfold bkeyK
    rw [R.pt ha (p := 2) (by norm_num), R.pt ha (p := 0) (by norm_num),
      R.pt hb (p := 2) (by norm_num), R.pt hb (p := 0) (by norm_num), h2, h0]
  rw [bsort_inj (fun i hi => CFSG.KS.Raw.Orb.allN_iff.1 sylS_bsort i hi) a ha b hb hk]

theorem mul_of_key {i j q : ℕ} (hi : i < 2048) (hj : j < 2048) (hq : q < 2048)
    (h : mulKeyK 11 (mask 11) 2 0 SylS.T i j q = true) : x i * x j = x q := by
  obtain ⟨h1, h2⟩ := mulKeyK_spec h
  refine R.eq_of_base (mul_mem (R.mem_S hi) (R.mem_S hj)) (R.mem_S hq) ?_ ?_
  · rw [← R.pair hi hj (p := 2) (by norm_num), h1, R.pt hq (p := 2) (by norm_num)]
  · rw [← R.pair hi hj (p := 0) (by norm_num), h2, R.pt hq (p := 0) (by norm_num)]

theorem key_of_mul {i j q : ℕ} (hi : i < 2048) (hj : j < 2048) (hq : q < 2048)
    (e : x i * x j = x q) : mulKeyK 11 (mask 11) 2 0 SylS.T i j q = true :=
  mulKeyK_of (by rw [R.pair hi hj (p := 2) (by norm_num), e, R.pt hq (p := 2) (by norm_num)])
    (by rw [R.pair hi hj (p := 0) (by norm_num), e, R.pt hq (p := 0) (by norm_num)])

theorem comm_of_key {s g : ℕ} (hs : s < 2048) (hg : g < 2048)
    (h : commKeyK 11 (mask 11) 2 0 SylS.T s g = true) : x s * x g = x g * x s := by
  obtain ⟨h1, h2⟩ := commKeyK_spec h
  refine R.eq_of_base (mul_mem (R.mem_S hs) (R.mem_S hg)) (mul_mem (R.mem_S hg) (R.mem_S hs))
    ?_ ?_
  · rw [← R.pair hs hg (p := 2) (by norm_num), h1, R.pair hg hs (p := 2) (by norm_num)]
  · rw [← R.pair hs hg (p := 0) (by norm_num), h2, R.pair hg hs (p := 0) (by norm_num)]

theorem key_of_comm {s g : ℕ} (hs : s < 2048) (hg : g < 2048) (e : x s * x g = x g * x s) :
    commKeyK 11 (mask 11) 2 0 SylS.T s g = true :=
  commKeyK_of (by rw [R.pair hs hg (p := 2) (by norm_num), e, R.pair hg hs (p := 2) (by norm_num)])
    (by rw [R.pair hs hg (p := 0) (by norm_num), e, R.pair hg hs (p := 0) (by norm_num)])

theorem card_S : Nat.card ↥(wordSubgroupP sWords) = 2 ^ 11 := by
  rw [card_wordSubgroupP, card_of_mem_iff R.mem R.inj]
  norm_num

theorem step {I : ℕ → ℕ} {o k : ℕ} (h : memberK 11 (mask 11) 2 0 2048 SylS.T I o k = true)
    {e j : ℕ} (he : e < 2 ^ k) (hj : j < k) :
    x (r32 I (o + e)) * x (r32 I (o + 2 ^ j)) = x (r32 I (o + (e ^^^ 2 ^ j))) := by
  obtain ⟨-, hlt, -, hmul⟩ := memberK_spec h
  have hjk : 2 ^ j < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hj
  exact R.mul_of_key (hlt e he) (hlt _ hjk) (hlt _ (Nat.xor_lt_two_pow he hjk)) (hmul e he j hj)

theorem member {I : ℕ → ℕ} {o k : ℕ} (hk : k ≤ 6)
    (h : memberK 11 (mask 11) 2 0 2048 SylS.T I o k = true) :
    (∀ z, z ∈ memG x I o k ↔ ∃ e < 2 ^ k, x (r32 I (o + e)) = z) ∧
      Nat.card (memG x I o k) = 2 ^ k ∧ memG x I o k ≤ wordSubgroup sWords ∧
        ∀ e < 2 ^ k, r32 I (o + e) < 2048 := by
  obtain ⟨h0, hlt, hinj, -⟩ := memberK_spec h
  have hjk : ∀ j < k, 2 ^ j < 2 ^ k := fun j hj => Nat.pow_lt_pow_right (by norm_num) hj
  have hy0 : x (r32 I (o + 0)) = 1 := by rw [Nat.add_zero, h0, R.one]
  have htree : ∀ e, 0 < e → e < 2 ^ k →
      ∃ p < e, ∃ j < k, x (r32 I (o + e)) = x (r32 I (o + p)) * x (r32 I (o + 2 ^ j)) := by
    intro e he0 he
    have he64 : e < 64 :=
      lt_of_lt_of_le he (le_trans (Nat.pow_le_pow_right (by norm_num) hk) (by norm_num))
    obtain ⟨h1, h2⟩ := topBit_spec e he64 he0
    have hj := h2 k hk he
    refine ⟨_, h1, _, hj, ?_⟩
    rw [R.step h (lt_trans h1 he) hj, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have hcl : ∀ e < 2 ^ k, ∀ j < k,
      ∃ q < 2 ^ k, x (r32 I (o + q)) = x (r32 I (o + e)) * x (r32 I (o + 2 ^ j)) :=
    fun e he j hj => ⟨_, Nat.xor_lt_two_pow he (hjk j hj), (R.step h he hj).symm⟩
  have hinj' : ∀ a < 2 ^ k, ∀ b < 2 ^ k, x (r32 I (o + a)) = x (r32 I (o + b)) → a = b :=
    fun a ha b hb e => hinj a ha b hb (R.inj _ (hlt a ha) _ (hlt b hb) e)
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hmem := mem_closure_iff_of_right_record (x := fun e => x (r32 I (o + e)))
    (g := fun j => x (r32 I (o + 2 ^ j))) hpos hy0 htree hcl
  refine ⟨hmem, card_closure_of_right_record (x := fun e => x (r32 I (o + e)))
    (g := fun j => x (r32 I (o + 2 ^ j))) hpos hy0 htree hcl hinj', ?_, hlt⟩
  intro z hz
  obtain ⟨e, he, rfl⟩ := (hmem z).1 hz
  exact R.mem_S (hlt e he)

theorem member_ea {I : ℕ → ℕ} {o k : ℕ}
    (h : memberK 11 (mask 11) 2 0 2048 SylS.T I o k = true) :
    CFSG.Open.IsElemAbelian 2 (memG x I o k) := by
  obtain ⟨h0, -, -, -⟩ := memberK_spec h
  have hjk : ∀ j < k, 2 ^ j < 2 ^ k := fun j hj => Nat.pow_lt_pow_right (by norm_num) hj
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    beta_reduce
    rw [R.step h (hjk i hi) hj, R.step h (hjk j hj) hi, Nat.xor_comm]
  · rintro _ ⟨j, hj, rfl⟩
    beta_reduce
    rw [pow_two, R.step h (hjk j hj) hj, Nat.xor_self, Nat.add_zero, h0, R.one]

theorem memP_ea {I : ℕ → ℕ} {o k : ℕ}
    (h : memberK 11 (mask 11) 2 0 2048 SylS.T I o k = true) :
    CFSG.Open.IsElemAbelian 2 (memP x I o k) :=
  (R.member_ea h).comap (f := P1408.subtype) Subtype.val_injective

theorem ext_fam : ∀ B ∈ fam x, ∀ s ∈ wordSubgroupP sWords, s ^ 2 = 1 → s ∉ B →
    (∀ b ∈ B, s * b = b * s) → ∃ B' ∈ fam x, B ≤ B' ∧ s ∈ B' ∧ Nat.card B' = 2 * Nat.card B := by
  rintro B ⟨k, hk2, hk6, h, hh, rfl⟩ s hs hs2 hsB hc
  obtain ⟨hm, hx⟩ := layer_spec hk2 hk6 hh
  obtain ⟨hmem, hcard, hS, hlt⟩ := R.member hk6 hm
  obtain ⟨i, hi, hxi⟩ := (R.mem (s : Equiv.Perm (Fin 1408))).1 hs
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hsB
    have hs1 : s = 1 := Subtype.ext (hxi.symm.trans R.one)
    rw [hs1]
    exact one_mem _
  have hsq : x i * x i = x 0 := by
    have e : s * s = 1 := by
      rw [← pow_two]
      exact hs2
    have e' : (s : Equiv.Perm (Fin 1408)) * s = 1 := congrArg Subtype.val e
    rw [R.one, hxi]
    exact e'
  have hIM : hasBit ivMask i = true :=
    ((involMaskK_spec sylS_inv).2 i hi).2 ⟨hi0, R.key_of_mul hi hi (by norm_num) hsq⟩
  obtain ⟨u, hu, hui⟩ := (hasBit_maskK _ _ _ _).1 hIM
  rw [Nat.zero_add] at hui
  have hsM : hasBit (maskK SylS.FM (famOff k + h * 2 ^ k) (2 ^ k)) i = false := by
    cases hb : hasBit (maskK SylS.FM (famOff k + h * 2 ^ k) (2 ^ k)) i
    · rfl
    · exfalso
      obtain ⟨e, he, hei⟩ := (hasBit_maskK _ _ _ _).1 hb
      apply hsB
      rw [mem_memP]
      exact (hmem _).2 ⟨e, he, by rw [hei, hxi]⟩
  have hcm : ∀ j < k, hasBit (SylS.CM (r32 SylS.FG (famGOff k + h * k + j))) i = true := by
    intro j hj
    obtain ⟨ht, hgd⟩ := gen_link hk2 hk6 hh hj
    have hjk : 2 ^ j < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hj
    have hgm : x (r32 SylS.FM (famOff k + h * 2 ^ k + 2 ^ j)) ∈ memG x SylS.FM
        (famOff k + h * 2 ^ k) k := subset_closure ⟨j, hj, rfl⟩
    have hgP : x (r32 SylS.FM (famOff k + h * 2 ^ k + 2 ^ j)) ∈ P1408 :=
      wordSubgroup_le sWords (hS hgm)
    have hc' : (s : Equiv.Perm (Fin 1408)) * x (r32 SylS.FM (famOff k + h * 2 ^ k + 2 ^ j)) =
        x (r32 SylS.FM (famOff k + h * 2 ^ k + 2 ^ j)) * s :=
      congrArg Subtype.val (hc ⟨_, hgP⟩ hgm)
    rw [← hxi] at hc'
    have hk := R.key_of_comm hi (hlt _ hjk) hc'
    rw [← hgd, ← hui] at hk
    have hb := (cm_spec ht hu).2 hk
    rwa [hui] at hb
  obtain ⟨hh', hhlt, hsub, hbit⟩ := extK_spec hx hIM hsM hcm
  rcases Nat.lt_or_ge k 6 with hk | hk
  · obtain ⟨hm', -⟩ := layer_spec (k := k + 1) (by omega) (by omega) hhlt
    obtain ⟨hmem', hcard', hS', -⟩ := R.member (by omega) hm'
    refine ⟨_, ⟨k + 1, by omega, by omega, hh', hhlt, rfl⟩, ?_, ?_, ?_⟩
    · intro z hz
      rw [mem_memP] at hz ⊢
      obtain ⟨e, he, hze⟩ := (hmem _).1 hz
      obtain ⟨e', he', he'e⟩ := (hasBit_maskK _ _ _ _).1
        (hsub _ ((hasBit_maskK _ _ _ _).2 ⟨e, he, rfl⟩))
      exact (hmem' _).2 ⟨e', he', by rw [he'e, hze]⟩
    · rw [mem_memP]
      obtain ⟨e', he', he'e⟩ := (hasBit_maskK _ _ _ _).1 hbit
      exact (hmem' _).2 ⟨e', he', by rw [he'e, hxi]⟩
    · rw [card_memP (hS'.trans (wordSubgroup_le sWords)),
        card_memP (hS.trans (wordSubgroup_le sWords)), hcard, hcard', pow_succ']
  · have e6 : k = 6 := by omega
    subst e6
    have e7 : famCnt (6 + 1) = 0 := rfl
    omega

theorem mem_V : memP x SylS.FM 0 2 ∈ fam x := ⟨2, le_rfl, by norm_num, 0, by decide, rfl⟩

theorem member_V : memberK 11 (mask 11) 2 0 2048 SylS.T SylS.FM 0 2 = true :=
  (layer_spec (k := 2) (h := 0) le_rfl (by norm_num) (by decide)).1

theorem V_cent {v : Equiv.Perm (Fin 1408)} (hv : v ∈ memG x SylS.FM 0 2) {t : Equiv.Perm (Fin 1408)}
    (ht : t ∈ wordSubgroup sWords) : t * v = v * t := by
  obtain ⟨-, -, -, hlt⟩ := R.member (by norm_num) R.member_V
  have hle : memG x SylS.FM 0 2 ≤ centralizer (wordSubgroup sWords : Set (Equiv.Perm (Fin 1408))) := by
    unfold memG
    rw [closure_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro t ht
    obtain ⟨i, hi, rfl⟩ := (R.mem t).1 ht
    have hc := CFSG.KS.Raw.Orb.allN_iff.1 sylS_cent i hi
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at hc
    have hj' : j < 2 := hj
    interval_cases j
    · exact (R.comm_of_key (hlt 1 (by norm_num)) hi hc.1).symm
    · exact (R.comm_of_key (hlt 2 (by norm_num)) hi hc.2).symm
  exact mem_centralizer_iff.1 (hle hv) t ht

theorem A_eq : memG x SylS.FA 0 6 = wordSubgroup uWords := by
  obtain ⟨hA, hW, -⟩ := sylS_A_parts
  obtain ⟨-, -, -, hlt⟩ := R.member le_rfl hA
  have hfg : (fun j => x (r32 SylS.FA (0 + 2 ^ j))) '' {j | j < 6} = elemW '' {w | w ∈ uWords} := by
    rw [← image_getD uWords, uWords_length]
    refine Set.image_congr fun j hj => ?_
    beta_reduce
    have hj' : j < 6 := hj
    have hb : r32 SylS.FA (0 + 2 ^ j) < 2048 :=
      hlt _ (Nat.pow_lt_pow_right (by norm_num) hj')
    rw [Nat.zero_add] at hb ⊢
    have hr := R.rep _ hb
    rw [hW j hj'] at hr
    exact perm_eq_of_rep hr (rep_word (uWords_letters j hj')).1
  unfold memG wordSubgroup
  rw [hfg]

theorem A_mem (w : Equiv.Perm (Fin 1408)) :
    w ∈ wordSubgroup uWords ↔ ∃ e < 64, x (r32 SylS.FA e) = w := by
  obtain ⟨hA, -, -⟩ := sylS_A_parts
  rw [← R.A_eq, (R.member le_rfl hA).1]
  simp only [Nat.zero_add]
  constructor
  · rintro ⟨e, he, h⟩
    exact ⟨e, lt_of_lt_of_eq he (by norm_num), h⟩
  · rintro ⟨e, he, h⟩
    exact ⟨e, lt_of_lt_of_eq he (by norm_num), h⟩

theorem memP_6188 : memP x SylS.FM 6188 6 = wordSubgroupP uWords := by
  obtain ⟨-, -, hmask⟩ := sylS_A_parts
  have hm := (layer_spec (k := 6) (h := 0) (by norm_num) le_rfl (by decide)).1
  have e0 : famOff 6 + 0 * 2 ^ 6 = 6188 := rfl
  rw [e0] at hm
  obtain ⟨hmem, -, -, -⟩ := R.member le_rfl hm
  ext z
  rw [mem_memP, hmem, mem_wordSubgroupP, R.A_mem]
  constructor
  · rintro ⟨e, he, hze⟩
    obtain ⟨e', he', h'⟩ := (idx_iff_of_maskK_eq hmask (r32 SylS.FM (6188 + e))).2
      ⟨e, lt_of_lt_of_eq he (by norm_num), rfl⟩
    rw [Nat.zero_add] at h'
    exact ⟨e', he', by rw [h', hze]⟩
  · rintro ⟨e', he', hze⟩
    obtain ⟨e, he, h'⟩ := (idx_iff_of_maskK_eq hmask (r32 SylS.FA (0 + e'))).1 ⟨e', he', rfl⟩
    rw [Nat.zero_add] at h'
    exact ⟨e, lt_of_lt_of_eq he (by norm_num), by rw [h', hze]⟩

theorem member_6252 : memberK 11 (mask 11) 2 0 2048 SylS.T SylS.FM 6252 6 = true :=
  (layer_spec (k := 6) (h := 1) (by norm_num) le_rfl (by decide)).1

theorem fc_eq {e : ℕ} (he : e < 64) :
    r32 SylS.FC e < 2048 ∧ r32 SylS.FA e < 2048 ∧
      x (r32 SylS.FC e) =
        elemW (sWords.getD 4 []) * x (r32 SylS.FA e) * (elemW (sWords.getD 4 []))⁻¹ := by
  obtain ⟨hA, -, -⟩ := sylS_A_parts
  obtain ⟨-, -, -, hltA⟩ := R.member le_rfl hA
  have hFA : r32 SylS.FA e < 2048 := by
    have h1 := hltA e (lt_of_lt_of_eq he (by norm_num))
    rwa [Nat.zero_add] at h1
  obtain ⟨hC, hmask⟩ := sylS_conj_parts
  obtain ⟨-, -, -, hlt61⟩ := R.member le_rfl R.member_6252
  obtain ⟨e', he', he'e⟩ := (idx_iff_of_maskK_eq hmask (r32 SylS.FC (0 + e))).1 ⟨e, he, rfl⟩
  rw [Nat.zero_add] at he'e
  have hFC : r32 SylS.FC e < 2048 := by
    rw [← he'e]
    exact hlt61 e' (lt_of_lt_of_eq he' (by norm_num))
  have eY : SylS.T (r32 SylS.Y 0) = SylS.G 4 := Nat.eq_of_beq_eq_true sylS_y
  obtain ⟨cG, rG⟩ := gen_rep 4 (by norm_num)
  rw [← eY] at cG rG
  obtain ⟨h1, h2⟩ := conjMemK_spec hC e he
  have g4S : elemW (sWords.getD 4 []) ∈ wordSubgroup sWords := elemW_mem_wordSubgroup getD4_mem
  have heq : elemW (sWords.getD 4 []) * x (r32 SylS.FA e) =
      x (r32 SylS.FC e) * elemW (sWords.getD 4 []) := by
    refine R.eq_of_base (mul_mem g4S (R.mem_S hFA)) (mul_mem (R.mem_S hFC) g4S) ?_ ?_
    · rw [← pt_pair cG rG (R.canon _ hFA) (R.rep _ hFA) (p := 2) (by norm_num), h1,
        pt_pair (R.canon _ hFC) (R.rep _ hFC) cG rG (p := 2) (by norm_num)]
    · rw [← pt_pair cG rG (R.canon _ hFA) (R.rep _ hFA) (p := 0) (by norm_num), h2,
        pt_pair (R.canon _ hFC) (R.rep _ hFC) cG rG (p := 0) (by norm_num)]
  exact ⟨hFC, hFA, eq_mul_inv_iff_mul_eq.2 heq.symm⟩

theorem memP_6252 : memP x SylS.FM 6252 6 = (wordSubgroupP uWords).map
    (MulAut.conj (⟨elemW (sWords.getD 4 []), elemW_mem _⟩ : ↥P1408)).toMonoidHom := by
  obtain ⟨-, hmask⟩ := sylS_conj_parts
  obtain ⟨hmem, -, -, -⟩ := R.member le_rfl R.member_6252
  ext z
  rw [mem_memP, hmem, Subgroup.mem_map]
  constructor
  · rintro ⟨e, he, hze⟩
    obtain ⟨e', he', he'e⟩ := (idx_iff_of_maskK_eq hmask (r32 SylS.FM (6252 + e))).2
      ⟨e, lt_of_lt_of_eq he (by norm_num), rfl⟩
    rw [Nat.zero_add] at he'e
    obtain ⟨-, hFA, hconj⟩ := R.fc_eq he'
    have hwA : x (r32 SylS.FA e') ∈ wordSubgroup uWords := (R.A_mem _).2 ⟨e', he', rfl⟩
    refine ⟨⟨_, wordSubgroup_le uWords hwA⟩, hwA, Subtype.ext ?_⟩
    rw [coe_conj, ← hze, ← he'e, hconj]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨e', he', hwe⟩ := (R.A_mem _).1 hw
    obtain ⟨-, -, hconj⟩ := R.fc_eq he'
    obtain ⟨e, he, hee⟩ := (idx_iff_of_maskK_eq hmask (r32 SylS.FC (0 + e'))).1 ⟨e', he', rfl⟩
    refine ⟨e, lt_of_lt_of_eq he (by norm_num), ?_⟩
    rw [coe_conj, hee, Nat.zero_add, hconj, hwe]
    rfl

theorem conj_of_le {B : Subgroup ↥P1408} (hBS : B ≤ wordSubgroupP sWords)
    (he : CFSG.Open.IsElemAbelian 2 B) (h64 : Nat.card B = 64) :
    ∃ y : ↥P1408, B = (wordSubgroupP uWords).map (MulAut.conj y).toMonoidHom := by
  obtain ⟨hmemV, -, hVS', -⟩ := R.member (by norm_num) R.member_V
  have hVS : memP x SylS.FM 0 2 ≤ wordSubgroupP sWords := fun v hv => hVS' (mem_memP.1 hv)
  have hcomm : ∀ a ∈ B, ∀ b ∈ memP x SylS.FM 0 2, a * b = b * a := fun a ha b hb =>
    Subtype.ext (R.V_cent (mem_memP.1 hb) (hBS ha))
  have hWel := CFSG.Open.IsElemAbelian.sup_of_commute he (R.memP_ea R.member_V) hcomm
  have hWmem : (B ⊔ memP x SylS.FM 0 2) ∈ fam x :=
    mem_family_of_isElemAbelian R.mem_V R.ext_fam (sup_le hBS hVS) hWel le_sup_right
  obtain ⟨k, hk2, hk6, h, hh, hW⟩ := hWmem
  obtain ⟨hm, -⟩ := layer_spec hk2 hk6 hh
  obtain ⟨-, hcard, hS, -⟩ := R.member hk6 hm
  have hWcard : Nat.card ↥(B ⊔ memP x SylS.FM 0 2) = 2 ^ k := by
    rw [hW, card_memP (hS.trans (wordSubgroup_le sWords)), hcard]
  have hWle : Nat.card ↥(B ⊔ memP x SylS.FM 0 2) ≤ 64 := by
    rw [hWcard]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) hk6) (by norm_num)
  have hBW : B = B ⊔ memP x SylS.FM 0 2 :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h64]; exact hWle)
  have hk : k = 6 := by
    have e : 2 ^ k = 64 := by rw [← hWcard, ← hBW, h64]
    exact Nat.pow_right_injective le_rfl (e.trans (by norm_num : (64 : ℕ) = 2 ^ 6))
  subst hk
  have e2 : famCnt 6 = 2 := rfl
  rw [e2] at hh
  rw [hBW, hW]
  interval_cases h
  · exact ⟨1, by rw [map_conj_one]; exact R.memP_6188⟩
  · exact ⟨_, R.memP_6252⟩

end RecS

theorem card_S : Nat.card ↥(wordSubgroupP sWords) = 2 ^ 11 := by
  obtain ⟨x, R⟩ := exists_recS
  exact R.card_S

theorem conj_of_le_S {B : Subgroup ↥P1408} (hBS : B ≤ wordSubgroupP sWords)
    (he : CFSG.Open.IsElemAbelian 2 B) (h64 : Nat.card B = 64) :
    ∃ y : ↥P1408, B = (wordSubgroupP uWords).map (MulAut.conj y).toMonoidHom := by
  obtain ⟨x, R⟩ := exists_recS
  exact R.conj_of_le hBS he h64

end CFSG.KD.HN1408.SylSG

end

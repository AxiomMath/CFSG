module

public import Certificates.Data.T84S4
import all Certificates.Data.T84S4
public import CFSG.Certificates.Kernel.Misc.T84Sound
public import CFSG.Certificates.Kernel.T84S4.Sound
public import Certificates.Kernel.T84S4.Data
import Certificates.Kernel.T84S4.Checks
import Certificates.Kernel.T84S4.Checks2
import Certificates.Kernel.T84S4.Enum
import Certificates.Kernel.Misc.T84.Checks
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.T84

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.GL4 CFSG.KC.Misc.GLM.Pf

theorem memJ_iff_of_442349 (x : Certificates.T84P.Elt) :
    memJ (enc x) = true ↔ x ∈ Certificates.T84P.Jl := by
  have hj := CertificateChecks.KernelMisc.T84.ch442349_j
  unfold chJ at hj
  obtain ⟨_, hj⟩ := andB_iff.1 hj
  obtain ⟨_, hj⟩ := andB_iff.1 hj
  obtain ⟨_, hj⟩ := andB_iff.1 hj
  obtain ⟨h4, hj⟩ := andB_iff.1 hj
  obtain ⟨h5, _⟩ := andB_iff.1 hj
  exact memJ_iff h4 h5 x

end CFSG.KC.Misc.T84

namespace CertificateChecks.KernelT84S4

open CFSG.KC.Misc.GL4 CFSG.KD.T84S4

theorem act_eq : ∀ p < 192, Certificates.T84S4.actArr.getD p 0 = l4 ACT p := by decide +kernel

theorem tm_eq : ∀ p < 144, Certificates.T84S4.tmulArr.getD p 0 = l4 TM p := by decide +kernel

theorem inv_eq : ∀ i < 192, Certificates.T84S4.invT i = l8 INV i := by decide +kernel

theorem tc_eq : ∀ k < 12, Certificates.T84S4.tCodes.getD k 0 = l16 TC k := by decide +kernel

theorem one_eq : eC TC 0 = CFSG.KC.Misc.T84.oneT := by decide +kernel

theorem l16_lt (X p : Nat) : l16 X p < 65536 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem mulT_eq : ∀ i < 192, ∀ j < 192, Certificates.T84S4.mulT i j = mI ACT TM i j := by
  intro i hi j hj
  have hp : 192 * i + j < 192 * 192 := by omega
  unfold Certificates.T84S4.mulT Certificates.T84S4.tb Certificates.T84S4.mulFlat
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hp, Option.getD_some]
  have e1 : (192 * i + j) / 192 = i := by omega
  have e2 : (192 * i + j) % 192 = j := by omega
  simp only [e1, e2]
  rw [act_eq _ (by omega), tm_eq _ (by omega)]
  rfl

theorem mI_lt : ∀ i < 192, ∀ j < 192, mI ACT TM i j < 192 := boundB_sound ch442352_bound

theorem t84s4_mI_zero : ∀ i < 192, mI ACT TM i 0 = i := by decide +kernel

theorem elt_enc : ∀ i < 192, CFSG.KC.Misc.T84.enc (Certificates.T84S4.elt i) = eC TC i := by
  intro i hi
  unfold Certificates.T84S4.elt
  rw [tc_eq _ (Nat.mod_lt _ (by norm_num)),
    ← CFSG.KC.Misc.T84.mkT_eq (by omega : i / 12 < 16) (l16_lt TC (i % 12))]
  rfl

theorem tab16 : ∀ k < 12, tabB ACT TM TC (16 * k) 16 = true := by
  intro k hk
  interval_cases k
  exacts [ch442352_tab0, ch442352_tab1, ch442352_tab2, ch442352_tab3, ch442352_tab4,
    ch442352_tab5, ch442352_tab6, ch442352_tab7, ch442352_tab8, ch442352_tab9, ch442352_tab10,
    ch442352_tab11]

theorem tab_ok : ∀ i < 192, ∀ j < 192,
    CFSG.KC.Misc.T84.mulT (eC TC i) (eC TC j) = eC TC (mI ACT TM i j) := by
  intro i hi j hj
  have h := tabB_sound (tab16 (i / 16) (by omega)) (i % 16) (Nat.mod_lt _ (by norm_num)) j hj
  rw [Nat.div_add_mod i 16] at h
  exact h

theorem jB_eq (x : Nat) : Certificates.T84S4.jT x = jB x := by
  unfold Certificates.T84S4.jT jB
  cases hb : Nat.blt (x % 12) 4
  · exact decide_eq_false fun h => by
      rw [← Nat.blt_eq] at h
      rw [h] at hb
      exact Bool.noConfusion hb
  · exact decide_eq_true (by rw [← Nat.blt_eq]; exact hb)

theorem facts_one : Certificates.T84S4.elt 0 = Certificates.T84P.oneE := by
  apply CFSG.KC.Misc.T84.enc_inj
  rw [elt_enc 0 (by norm_num), one_eq, CFSG.KC.Misc.T84.enc_one]

theorem facts_mem : ∀ i < 192, Certificates.T84S4.elt i ∈ Certificates.T84P.M0l := by
  intro i hi
  rw [CFSG.KC.Misc.T84.mem_M0l CertificateChecks.KernelMisc.T84.ch442349_s0]
  unfold Certificates.T84S4.elt
  dsimp only
  rw [tc_eq _ (Nat.mod_lt _ (by norm_num)), code4_ofCode (l16_lt _ _)]
  exact (memN_iff' _ _).1 (tcB_sound ch442352_tc _ (Nat.mod_lt _ (by norm_num)))

theorem facts_inj : ∀ i < 192, ∀ j < 192,
    Certificates.T84S4.elt i = Certificates.T84S4.elt j → i = j := by
  intro i hi j hj h
  have h' := congrArg CFSG.KC.Misc.T84.enc h
  rw [elt_enc i hi, elt_enc j hj] at h'
  exact injB_sound ch442352_inj i hi j hj h'

theorem facts_tab : ∀ i < 192, ∀ j < 192, Certificates.T84S4.mulT i j < 192 ∧
    Certificates.T84P.mulE (Certificates.T84S4.elt i) (Certificates.T84S4.elt j) =
      Certificates.T84S4.elt (Certificates.T84S4.mulT i j) := by
  intro i hi j hj
  rw [mulT_eq i hi j hj]
  refine ⟨mI_lt i hi j hj, ?_⟩
  apply CFSG.KC.Misc.T84.enc_inj
  rw [CFSG.KC.Misc.T84.enc_mulE, elt_enc i hi, elt_enc j hj, elt_enc _ (mI_lt i hi j hj)]
  exact tab_ok i hi j hj

theorem facts_inv : ∀ i < 192, Certificates.T84S4.invT i < 192 ∧
    Certificates.T84S4.mulT i (Certificates.T84S4.invT i) = 0 := by
  intro i hi
  obtain ⟨hl, h0⟩ := invB_sound ch442352_inv i hi
  rw [inv_eq i hi, mulT_eq i hi _ hl]
  exact ⟨hl, h0⟩

theorem facts_jT : ∀ i < 192, (Certificates.T84S4.jT i = true ↔
    Certificates.T84S4.elt i ∈ Certificates.T84P.Jl) := by
  intro i hi
  rw [← CFSG.KC.Misc.T84.memJ_iff_of_442349, elt_enc i hi, jEqB_sound ch442352_jeq i hi, jB_eq]

theorem facts_jl : ∀ x ∈ Certificates.T84P.Jl, x ∈ Certificates.T84S4.Ml () := by
  intro x hx
  obtain ⟨i, hi, he⟩ := jkB_sound ch442352_jk _
    ((CFSG.KC.Misc.T84.mem_iff CFSG.KC.Misc.T84.Jl_map).1 hx)
  have hxi : Certificates.T84S4.elt i = x :=
    CFSG.KC.Misc.T84.enc_inj (by rw [elt_enc i hi]; exact Nat.eq_of_beq_eq_true he)
  rw [← hxi]
  unfold Certificates.T84S4.Ml
  exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩

theorem facts_norm : ∀ i < 192, ∀ j < 192, Certificates.T84S4.jT j = true →
    Certificates.T84S4.jT (Certificates.T84S4.mulT (Certificates.T84S4.mulT i j)
      (Certificates.T84S4.invT i)) = true := by
  intro i hi j hj hJ
  have hl := (facts_inv i hi).1
  rw [mulT_eq i hi j hj, mulT_eq _ (mI_lt i hi j hj) _ hl, inv_eq i hi, jB_eq]
  rw [jB_eq] at hJ
  exact normB_sound ch442352_norm i hi j hj hJ

theorem facts_gen3 : Certificates.T84S4.gy < 192 ∧
    Certificates.T84S4.mulT (Certificates.T84S4.mulT Certificates.T84S4.gy Certificates.T84S4.gy)
      Certificates.T84S4.gy = 0 ∧
    ∀ i < 192, Certificates.T84S4.mulT (Certificates.T84S4.mulT i i) i = 0 ∨
      Certificates.T84S4.mulT (Certificates.T84S4.mulT (Certificates.T84S4.mulT i Certificates.T84S4.gy)
        (Certificates.T84S4.mulT i Certificates.T84S4.gy))
        (Certificates.T84S4.mulT i Certificates.T84S4.gy) = 0 := by
  have hg : Certificates.T84S4.gy = 191 := rfl
  obtain ⟨h1, h2⟩ := gen3B_sound ch442352_gen3
  rw [hg]
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [mulT_eq 191 (by norm_num) 191 (by norm_num),
      mulT_eq _ (mI_lt _ (by norm_num) _ (by norm_num)) 191 (by norm_num)]
    exact h1
  · intro i hi
    have hy := mI_lt i hi 191 (by norm_num)
    rw [mulT_eq i hi i hi, mulT_eq _ (mI_lt i hi i hi) i hi, mulT_eq i hi 191 (by norm_num),
      mulT_eq _ hy _ hy, mulT_eq _ (mI_lt _ hy _ hy) _ hy]
    exact h2 i hi

theorem facts_fpf : ∀ i < 192, i ≠ 0 →
    Certificates.T84S4.mulT (Certificates.T84S4.mulT i i) i = 0 →
    ∀ j < 192, Certificates.T84S4.jT j = true →
      Certificates.T84S4.mulT i j = Certificates.T84S4.mulT j i → j = 0 := by
  intro i hi hi0 h3 j hj hJ hc
  rw [mulT_eq i hi i hi, mulT_eq _ (mI_lt i hi i hi) i hi] at h3
  rw [mulT_eq i hi j hj, mulT_eq j hj i hi] at hc
  rw [jB_eq] at hJ
  exact fpfB_sound ch442352_fpf i hi (Nat.pos_of_ne_zero hi0) h3 j hj hJ hc

theorem facts_jg : ∀ i ∈ Certificates.T84S4.jgIdx, i < 192 ∧
    Certificates.T84S4.elt i ∈ Certificates.T84P.Jl := by
  intro i hi
  simp only [Certificates.T84S4.jgIdx, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, (facts_jT 50 (by norm_num)).1 (by decide)⟩
  · exact ⟨by norm_num, (facts_jT 181 (by norm_num)).1 (by decide)⟩
  · exact ⟨by norm_num, (facts_jT 158 (by norm_num)).1 (by decide)⟩
  · exact ⟨by norm_num, (facts_jT 110 (by norm_num)).1 (by decide)⟩

theorem pow44_enc (z : Certificates.T84P.Elt) :
    CFSG.KC.Misc.T84.enc (Certificates.T84S4.pow44 z) = pow44T (CFSG.KC.Misc.T84.enc z) := by
  unfold Certificates.T84S4.pow44 pow44T
  simp only [CFSG.KC.Misc.T84.enc_mulE]

theorem odd4 : ∀ k < 4, oddB TC (4 * k) 4 = true := by
  intro k hk
  interval_cases k
  exacts [ch442352_odd0, ch442352_odd1, ch442352_odd2, ch442352_odd3]

theorem odd_ok : ∀ u < 16, ∀ m ∈ CFSG.KC.Misc.T84.S0L,
    oddOne TC (CFSG.KC.Misc.T84.mkT u m) = true := by
  intro u hu m hm
  have h := oddB_sound (odd4 (u / 4) (by omega)) (u % 4) (Nat.mod_lt _ (by norm_num)) m hm
  rw [Nat.div_add_mod u 4] at h
  exact h

theorem facts_odd : ∀ z ∈ Certificates.T84P.M0l,
    Certificates.T84P.mulE z (Certificates.T84S4.pow44 z) = Certificates.T84P.oneE →
    (∀ i ∈ Certificates.T84S4.jgIdx, Certificates.T84P.mulE (Certificates.T84P.mulE z
      (Certificates.T84S4.elt i)) (Certificates.T84S4.pow44 z) ∈ Certificates.T84P.Jl) →
    z ∈ Certificates.T84S4.Ml () := by
  intro z hz h1 h2
  rw [CFSG.KC.Misc.T84.mem_M0l CertificateChecks.KernelMisc.T84.ch442349_s0] at hz
  obtain ⟨u, hu, hv⟩ := vec_surj z.1
  have hm : code4 z.2 < 65536 := CFSG.KC.Misc.T84.S0L_lt _ hz
  have hze : CFSG.KC.Misc.T84.enc z = CFSG.KC.Misc.T84.mkT u (code4 z.2) := by
    rw [CFSG.KC.Misc.T84.mkT_eq hu hm, hv, ofCode_code4]
  have c1 : CFSG.KC.Misc.T84.mulT (CFSG.KC.Misc.T84.enc z) (pow44T (CFSG.KC.Misc.T84.enc z)) =
      CFSG.KC.Misc.T84.oneT := by
    rw [← pow44_enc, ← CFSG.KC.Misc.T84.enc_mulE, h1, CFSG.KC.Misc.T84.enc_one]
  have cj : ∀ i ∈ Certificates.T84S4.jgIdx, CFSG.KC.Misc.T84.memJ (CFSG.KC.Misc.T84.mulT
      (CFSG.KC.Misc.T84.mulT (CFSG.KC.Misc.T84.enc z) (eC TC i))
      (pow44T (CFSG.KC.Misc.T84.enc z))) = true := by
    intro i hi
    have hi' : i < 192 := (facts_jg i hi).1
    rw [← pow44_enc, ← elt_enc i hi', ← CFSG.KC.Misc.T84.enc_mulE, ← CFSG.KC.Misc.T84.enc_mulE]
    exact (CFSG.KC.Misc.T84.memJ_iff_of_442349 _).2 (h2 i hi)
  have ho := odd_ok u hu _ hz
  rw [← hze] at ho
  obtain ⟨k, hk, he⟩ := oddOne_sound ho c1 (cj 50 (by simp [Certificates.T84S4.jgIdx]))
    (cj 181 (by simp [Certificates.T84S4.jgIdx])) (cj 158 (by simp [Certificates.T84S4.jgIdx]))
    (cj 110 (by simp [Certificates.T84S4.jgIdx]))
  rw [CFSG.KC.Misc.T84.hiT_enc] at he
  have hck : code4 z.2 = l16 TC k := Nat.eq_of_beq_eq_true he
  have hlt : 12 * u + k < 192 := by omega
  have hze' : CFSG.KC.Misc.T84.enc (Certificates.T84S4.elt (12 * u + k)) =
      CFSG.KC.Misc.T84.enc z := by
    rw [elt_enc _ hlt, hze, hck]
    change CFSG.KC.Misc.T84.mkT ((12 * u + k) / 12) (l16 TC ((12 * u + k) % 12)) = _
    have e1 : (12 * u + k) / 12 = u := by omega
    have e2 : (12 * u + k) % 12 = k := by omega
    rw [e1, e2]
  rw [← CFSG.KC.Misc.T84.enc_inj hze']
  unfold Certificates.T84S4.Ml
  exact List.mem_map.2 ⟨12 * u + k, List.mem_range.2 hlt, rfl⟩

theorem enum8 : ∀ S ∈ [S0, S1, S2, S3, S4, S5, S6, S7], enumB ACT TM WP L3 L4 I2 S = true := by
  intro S hS
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ch442352_e0, ch442352_e1, ch442352_e2, ch442352_e3, ch442352_e4, ch442352_e5,
    ch442352_e6, ch442352_e7]

theorem cut8 : [S0, S1, S2, S3, S4, S5, S6, S7].flatten = L3 := by
  have h := beq_iff_eq.1 ch442352_cut
  rw [← h]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

theorem facts_autFix : ∀ f : Nat → Nat, (∀ i < 192, f i < 192) → f 0 = 0 →
    (∀ i < 192, ∀ j < 192, f (Certificates.T84S4.mulT i j) =
      Certificates.T84S4.mulT (f i) (f j)) → (∀ i < 192, f (f i) = i) →
    ((List.range 192).filter fun x => Certificates.T84S4.jT x && f x == x).length = 4 →
    (∀ i < 192, Certificates.T84S4.jT i = true → f i = i → Certificates.T84S4.mulT i i = 0) →
      ∃ y < 192, y ≠ 0 ∧ Certificates.T84S4.mulT (Certificates.T84S4.mulT y y) y = 0 ∧
        f y = y := by
  intro f hf1 hf0 hf hff hcard hel
  have hjT : (fun x => Certificates.T84S4.jT x && f x == x) = (fun x => jB x && f x == x) :=
    funext fun x => by rw [jB_eq]
  rw [hjT] at hcard
  have hom : ∀ i < 192, ∀ j < 192, f (mI ACT TM i j) = mI ACT TM (f i) (f j) := by
    intro i hi j hj
    rw [← mulT_eq i hi j hj, ← mulT_eq _ (hf1 i hi) _ (hf1 j hj)]
    exact hf i hi j hj
  have hel' : ∀ i < 192, jB i = true → f i = i → mI ACT TM i i = 0 := by
    intro i hi hj hfi
    rw [← mulT_eq i hi i hi]
    exact hel i hi (by rw [jB_eq]; exact hj) hfi
  obtain ⟨y, hy, hy0, hy3, hfy⟩ := enum_sound ch442352_list ch442352_words
    ch442352_rels ch442352_bound t84s4_mI_zero cut8 enum8 f hf1 hf0 hom hff hcard hel'
  refine ⟨y, hy, hy0, ?_, hfy⟩
  rw [mulT_eq y hy y hy, mulT_eq _ (mI_lt y hy y hy) y hy]
  exact hy3

theorem facts : Certificates.T84S4.Facts where
  one := facts_one
  mem := facts_mem
  inj := facts_inj
  tab := facts_tab
  inv := facts_inv
  jT_iff := facts_jT
  jl_sub := facts_jl
  norm := facts_norm
  gen3 := facts_gen3
  fpf := facts_fpf
  jg := facts_jg
  odd := facts_odd
  autFix := facts_autFix

end CertificateChecks.KernelT84S4

end

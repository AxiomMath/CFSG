module

public import Certificates.Kernel.FiveStd.CoverGlue
public import Certificates.Kernel.FiveStd.Diag2
public import CFSG.Certificates.Kernel.FiveStdKKKSound
public import CFSG.Certificates.Kernel.FiveStdKDiag2Sound
public import CFSG.GH74.GLS.LU.Local.FiveStdMat8

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five

section Conj

variable {Gp : Type} [Group Gp] {ι : E → Gp} (hM : Model ι)
include hM

theorem cj_mul {c a b : E} (hc : validE c = true) (ha : validE a = true) (hb : validE b = true) :
    conjE c (mulE a b) = mulE (conjE c a) (conjE c b) := by
  have h1 := hM.valid_conjE hc ha
  have h2 := hM.valid_conjE hc hb
  apply hM.inj _ _ (hM.valid_conjE hc (hM.valid_mul _ _ ha hb)) (hM.valid_mul _ _ h1 h2)
  rw [hM.map_conjE hc (hM.valid_mul _ _ ha hb), hM.map_mul _ _ ha hb, hM.map_mul _ _ h1 h2,
    hM.map_conjE hc ha, hM.map_conjE hc hb]
  group

theorem cj_cj {a b x : E} (ha : validE a = true) (hb : validE b = true) (hx : validE x = true) :
    conjE a (conjE b x) = conjE (mulE a b) x := by
  apply hM.inj _ _ (hM.valid_conjE ha (hM.valid_conjE hb hx))
    (hM.valid_conjE (hM.valid_mul _ _ ha hb) hx)
  rw [hM.map_conjE ha (hM.valid_conjE hb hx), hM.map_conjE hb hx,
    hM.map_conjE (hM.valid_mul _ _ ha hb) hx, hM.map_mul _ _ ha hb]
  group

theorem cj_back {c x : E} (hc : validE c = true) (hx : validE x = true) :
    conjE (invE c) (conjE c x) = x := by
  apply hM.inj _ _ (hM.valid_conjE (hM.valid_inv _ hc) (hM.valid_conjE hc hx)) hx
  rw [hM.map_conjE (hM.valid_inv _ hc) (hM.valid_conjE hc hx), hM.map_conjE hc hx, hM.map_inv _ hc]
  group

theorem cj_fwd {c x : E} (hc : validE c = true) (hx : validE x = true) :
    conjE c (conjE (invE c) x) = x := by
  apply hM.inj _ _ (hM.valid_conjE hc (hM.valid_conjE (hM.valid_inv _ hc) hx)) hx
  rw [hM.map_conjE hc (hM.valid_conjE (hM.valid_inv _ hc) hx),
    hM.map_conjE (hM.valid_inv _ hc) hx, hM.map_inv _ hc]
  group

theorem cj_one {c : E} (hc : validE c = true) : conjE c oneE = oneE := by
  apply hM.inj _ _ (hM.valid_conjE hc hM.valid_one) hM.valid_one
  rw [hM.map_conjE hc hM.valid_one, hM.map_one]
  group

theorem cj_pow {c x : E} (hc : validE c = true) (hx : validE x = true) (n : Nat) :
    powE (conjE c x) n = conjE c (powE x n) := by
  have h1 := hM.valid_conjE hc hx
  apply hM.inj _ _ (hM.valid_powE h1 n) (hM.valid_conjE hc (hM.valid_powE hx n))
  rw [hM.map_powE h1, hM.map_conjE hc hx, hM.map_conjE hc (hM.valid_powE hx n), hM.map_powE hx]
  exact conj_pow

theorem cj_inj {c x y : E} (hc : validE c = true) (hx : validE x = true) (hy : validE y = true)
    (h : conjE c x = conjE c y) : x = y := by
  rw [← cj_back hM hc hx, h, cj_back hM hc hy]

theorem pow5_iff {x : E} (hx : validE x = true) :
    (ordE x = 1 ∨ ordE x = 5) ↔ powE x 5 = oneE := by
  constructor
  · intro h
    have ho : orderOf (ι x) ∣ 5 := by
      rcases h with h | h
      · rw [hM.orderOf_of_ordE hx h (by norm_num)]
        norm_num
      · rw [hM.orderOf_of_ordE hx h (by norm_num)]
    apply hM.inj _ _ (hM.valid_powE hx 5) hM.valid_one
    rw [hM.map_powE hx, hM.map_one]
    exact orderOf_dvd_iff_pow_eq_one.1 ho
  · intro h
    have h5 : ι x ^ 5 = 1 := by rw [← hM.map_powE hx, h, hM.map_one]
    have ho := orderOf_dvd_of_pow_eq_one h5
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 ho with h1 | h1
    · exact Or.inl (hM.ordE_of_orderOf hx h1 le_rfl (by norm_num))
    · exact Or.inr (hM.ordE_of_orderOf hx h1 (by norm_num) (by norm_num))

theorem ord2_iff {x : E} (hx : validE x = true) :
    ordE x = 2 ↔ mulE x x = oneE ∧ x ≠ oneE := by
  constructor
  · intro h
    have ho := hM.orderOf_of_ordE hx h (by norm_num)
    refine ⟨?_, fun e => ?_⟩
    · apply hM.inj _ _ (hM.valid_mul _ _ hx hx) hM.valid_one
      rw [hM.map_mul _ _ hx hx, hM.map_one, ← sq, ← ho, pow_orderOf_eq_one]
    · rw [e, hM.map_one, orderOf_one] at ho
      exact absurd ho (by norm_num)
  · rintro ⟨h1, h2⟩
    have h2' : ι x ^ 2 = 1 := by rw [sq, ← hM.map_mul _ _ hx hx, h1, hM.map_one]
    have hne : ι x ≠ 1 := fun e => h2 (hM.inj _ _ hx hM.valid_one (by rw [e, hM.map_one]))
    exact hM.ordE_of_orderOf hx (orderOf_eq_prime h2' hne) (by norm_num) (by norm_num)

theorem ord_conj {c x : E} (hc : validE c = true) (hx : validE x = true) {n : Nat}
    (h : ordE x = n) (hn : n ≤ 300) : ordE (conjE c x) = n := by
  have ho := hM.orderOf_of_ordE hx h hn
  apply hM.ordE_of_orderOf (hM.valid_conjE hc hx) _ (h ▸ ordE_pos x) hn
  rw [hM.map_conjE hc hx, ← ho]
  exact (MulAut.conj (ι c)).orderOf_eq (ι x)

end Conj

structure RepFacts (r : E) (A B : List E) (v0 : E) : Prop where
  hr : validE r = true
  hv0 : validE v0 = true
  hinv : conjE v0 r = invE r
  hAnd : A.Nodup
  hAlen : A.length = 25
  hcen : ∀ b, validE b = true → (mulE b r = mulE r b ↔ b ∈ B)
  hBv : ∀ b ∈ B, validE b = true
  hA : ∀ a ∈ A, validE a = true ∧ mulE a r = mulE r a ∧ powE a 5 = oneE ∧ inKK a = true ∧
    ∀ a' ∈ A, mulE a a' ∈ A
  hB : ∀ b ∈ B, (powE b 5 = oneE → b ∈ A) ∧ (∀ a ∈ A, conjE b a ∈ A) ∧
    ((mulE v0 b).s = false → ∀ a ∈ A, conjE (mulE v0 b) a = invE a)
  hdv : ∀ τ ∈ B, mulE τ τ = oneE → τ ≠ oneE → τ ≠ zE → ∀ b ∈ B,
    ∃ v ∈ [oneE, zE, τ, mulE zE τ], mulE b (invE v) ∈ A

structure NoInvFacts (r : E) (B : List E) : Prop where
  hr : validE r = true
  hcen : ∀ b, validE b = true → (mulE b r = mulE r b ↔ b ∈ B)
  hB : ∀ b ∈ B, mulE b b = oneE → b = oneE ∨ b = zE

theorem fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem hF5 : Nat.card (ZMod 5) = 5 := by
  rw [Nat.card_eq_fintype_card, ZMod.card]

theorem cb_valid (k : Nat) (hk : k < 5) : ∀ j < CM.getD k 0, validK (f20 (CB.getD k 0) j) = true :=
  fun j hj => (cPt_spec ((clsOK_spec (clsF_eq k ▸ cls_ok k hk)).2.2.2.2.1 j hj)).1

theorem iv_valid (k : Nat) (hk : k < 5) : validK (IV.getD k 0) = true :=
  (clsOK_spec (clsF_eq k ▸ cls_ok k hk)).2.2.2.2.2.1

theorem cm01 : CM.getD 0 0 = 100 ∧ CM.getD 1 0 = 100 ∧ CM.getD 2 0 = 600 := by decide +kernel

theorem rep_facts (k : Nat) (hk : k < 2) :
    RepFacts (decE (RP.getD k 0)) (decL (f20 (if k = 0 then A0 else A1)) 25)
      (decL (f20 (CB.getD k 0)) 100) (decE (IV.getD k 0)) := by
  have : Fact (Nat.Prime 5) := fact5
  have hM := Mat.model_ιF (F := ZMod 5)
  obtain ⟨hr, -, -, hcen, -, hv0, hinv⟩ := cls_glue k (by omega)
  have hcm : CM.getD k 0 = 100 := by
    interval_cases k
    · exact cm01.1
    · exact cm01.2.1
  rw [hcm] at hcen
  have hcb := cb_valid k (by omega)
  rw [hcm] at hcb
  have hdg : dgOK (if k = 0 then A0 else A1) 25 (CB.getD k 0) 100 (RP.getD k 0) (IV.getD k 0) = true := by
    interval_cases k
    · exact diag0
    · exact diag1
  have hdv : dvOK (if k = 0 then A0 else A1) 25 (CB.getD k 0) 100 = true := by
    interval_cases k
    · exact diag0v
    · exact diag1v
  have hrk := (clsOK_spec (clsF_eq k ▸ cls_ok k (by omega))).2.1
  obtain ⟨hnd, hA, hB⟩ := dg_sound hdg hrk (iv_valid k (by omega)) hcb
  refine ⟨hr, hv0, hinv, hnd, by rw [decL, List.length_map, List.length_range], hcen, ?_, ?_, hB,
    dv_sound hdv hcb⟩
  · intro b hb
    obtain ⟨j, hj, rfl⟩ := mem_decL.1 hb
    exact valid_decE (hcb j hj)
  · intro a ha
    obtain ⟨h1, h2, h3, h4, h5⟩ := hA a ha
    exact ⟨h1, h2, h3, h4, h5⟩

theorem noinv_facts : NoInvFacts (decE (RP.getD 2 0)) (decL (f20 (CB.getD 2 0)) 600) := by
  obtain ⟨hr, -, -, hcen, -, -, -⟩ := cls_glue 2 (by omega)
  have hcb := cb_valid 2 (by omega)
  rw [cm01.2.2] at hcen hcb
  exact ⟨hr, hcen, noInv_sound diag2 hcb⟩

theorem z_central {x : E} (hx : validE x = true) : mulE x zE = mulE zE x := by
  have : Fact (Nat.Prime 5) := fact5
  let st := fiveStdSetting (F := ZMod 5) hF5
  have hmem := Subgroup.mem_centralizer_singleton_iff.1 (st.ι_mem_C hx)
  have hz : validE zE = true := by decide +kernel
  apply st.model.inj _ _ (st.model.valid_mul _ _ hx hz) (st.model.valid_mul _ _ hz hx)
  rw [st.model.map_mul _ _ hx hz, st.model.map_mul _ _ hz hx]
  first
  | exact hmem
  | exact hmem.symm

theorem cj_z {c : E} (hc : validE c = true) : conjE c zE = zE := by
  have : Fact (Nat.Prime 5) := fact5
  have hM := Mat.model_ιF (F := ZMod 5)
  have hz : validE zE = true := by decide +kernel
  apply hM.inj _ _ (hM.valid_conjE hc hz) hz
  have := congrArg (Mat.ιF (ZMod 5)) (z_central hc)
  rw [hM.map_mul _ _ hc hz, hM.map_mul _ _ hz hc] at this
  rw [hM.map_conjE hc hz, this]
  group

theorem k12_meet : ∀ c ∈ K1c, K2c.contains c = true → c = oneK ∨ c = zK := by decide +kernel

theorem y0_mem : K2c.contains (cjK 409405 (invK 409405) 29501) = true := by decide +kernel

theorem x0_mem : 29501 ∈ K1c := by decide +kernel

theorem t0_valid : validK 409405 = true := by decide +kernel

theorem s_of_normK1 {v : E} (hv : validE v = true) (hn : normK1 v = true) : v.s = false := by
  have : Fact (Nat.Prime 5) := fact5
  let st := fiveStdSetting (F := ZMod 5) hF5
  have hM : Model st.ι := st.model
  cases hs : v.s
  · rfl
  exfalso
  set t0 := decE 409405 with ht0d
  set x0 := decE 29501 with hx0d
  have ht0 : validE t0 = true := valid_decE t0_valid
  have hct0 : codeE t0 = 409405 := codeE_decE (by norm_num)
  have hcx0 : codeE x0 = 29501 := codeE_decE (by norm_num)
  have hx0K : x0 ∈ K1l := by
    obtain ⟨x, hx, hxc⟩ := mem_codes K1l_codes x0_mem
    rwa [← codeE_injective (hxc.trans hcx0.symm)]
  have hx0 : validE x0 = true := List.all_eq_true.1 k1_valid x0 hx0K
  have ht0s : t0.s = true := by
    have h0 := fS_codeE t0
    rw [hct0] at h0
    cases hb : t0.s
    · rw [hb] at h0
      exact absurd h0 (by decide)
    · rfl
  set w := mulE v (invE t0) with hwd
  have hw : validE w = true := hM.valid_mul _ _ hv (hM.valid_inv _ ht0)
  have hws : w.s = false := by rw [hwd, s_mulE, s_invE, hs, ht0s]; rfl
  have hvw : v = mulE w t0 := by
    apply hM.inj _ _ hv (hM.valid_mul _ _ hw ht0)
    rw [hM.map_mul _ _ hw ht0, hwd, hM.map_mul _ _ hv (hM.valid_inv _ ht0), hM.map_inv _ ht0]
    group
  set y0 := conjE t0 x0 with hy0d
  have hy0 : validE y0 = true := hM.valid_conjE ht0 hx0
  have hy0K : y0 ∈ K2l := by
    have hc : codeE y0 ∈ K2c := by
      rw [hy0d, conj_code, hct0, hcx0]
      exact List.contains_iff_mem.1 y0_mem
    obtain ⟨y, hy, hyc⟩ := mem_codes K2l_codes hc
    rwa [← codeE_injective hyc]
  have hwK2 : conjE w y0 ∈ K2l := by
    have hblk := (st.hblock w ((mem_Cs_iff w).2 hw) hws).2
    have hyK : st.ι y0 ∈ st.K₂ := by
      have : st.ι y0 ∈ ((st.K₂ : Subgroup _) : Set _) := by rw [st.hK₂]; exact mem_S.2 ⟨y0, hy0K, rfl⟩
      exact this
    have h1 : st.ι (conjE w y0) ∈ st.K₂ := by
      rw [← hblk, hM.map_conjE hw hy0]
      exact Subgroup.mem_map.2 ⟨st.ι y0, hyK, by simp [MulAut.conj_apply]⟩
    have h2 : st.ι (conjE w y0) ∈ S st.ι K2l := by rw [← st.hK₂]; exact h1
    obtain ⟨y, hy, hye⟩ := mem_S.1 h2
    rwa [← hM.inj _ _ (List.all_eq_true.1 k2_valid y hy) (hM.valid_conjE hw hy0) hye]
  have hvx : conjE v x0 = conjE w y0 := by rw [hvw, hy0d, cj_cj hM hw ht0 hx0]
  have hvK1 : conjE v x0 ∈ K1l := by
    unfold normK1 at hn
    have := List.all_eq_true.1 hn x0 hx0K
    rw [inL, List.contains_iff_mem] at this
    exact this
  have hc1 : codeE (conjE v x0) ∈ K1c := K1l_codes ▸ List.mem_map_of_mem hvK1
  have hc2 : K2c.contains (codeE (conjE v x0)) = true := by
    rw [hvx, List.contains_iff_mem, ← K2l_codes]
    exact List.mem_map_of_mem hwK2
  rcases k12_meet _ hc1 hc2 with h1 | h1
  · have hx01 : x0 = oneE := by
      rw [← cj_back hM hv hx0, codeE_eq_oneK.1 h1, cj_one hM (hM.valid_inv _ hv)]
    have := congrArg codeE hx01
    rw [hcx0, codeE_oneE] at this
    exact absurd this (by decide)
  · have hx0z : x0 = zE := by
      rw [← cj_back hM hv hx0, codeE_injective (h1.trans codeE_zE.symm), cj_z (hM.valid_inv _ hv)]
    have := congrArg codeE hx0z
    rw [hcx0, codeE_zE] at this
    exact absurd this (by decide)

end CertificateChecks.FiveStd

end

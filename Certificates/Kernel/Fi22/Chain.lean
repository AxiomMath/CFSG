module

public import Certificates.Kernel.Fi22.Fix
public import CFSG.Certificates.Kernel.BindSubSound
public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X1_Sel
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X2_Sel
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X3_Sel
import Certificates.Kernel.Co2.Intro
import Certificates.Kernel.Fi22.Facts
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.X1_H_0
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.X2_H_0
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.X3_H_0
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelFi22

open CFSG.KC CFSG.KC.LceS CFSG.KC.Bind CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

@[expose] noncomputable def gF (k : ℕ) : FreeGroup (Fin 6) := if h : k < 6 then FreeGroup.of ⟨k, h⟩ else 1

@[expose] def relsX : Set (FreeGroup (Fin 6)) :=
  Set.range fun r : Fin 27 => bval gF (wWord (CFSG.KD.Fi22KM.XRs r)) (wLen (CFSG.KD.Fi22KM.XRs r))

abbrev XT : Type := PresentedGroup relsX

noncomputable abbrev gX : ℕ → XT := pgen relsX

theorem gX_eq (k : ℕ) : gX k = PresentedGroup.mk relsX (gF k) := by
  simp only [gX, pgen, gF]
  split_ifs <;> simp [PresentedGroup.of]

theorem xrel {r : ℕ} (hr : r < 27) :
    bval gX (wWord (CFSG.KD.Fi22KM.XRs r)) (wLen (CFSG.KD.Fi22KM.XRs r)) = 1 := by
  rw [bval_congr gX_eq, ← bval_map]
  exact PresentedGroup.one_of_mem ⟨⟨r, hr⟩, rfl⟩

theorem xr_ok : ∀ r < 27, HO.entOK (CFSG.KD.Fi22KM.XRs r) (nat_lit 12) (nat_lit 1023) = true := by
  intro r hr
  interval_cases r <;> quickRfl

theorem bval_one {G : Type*} [Group G] (gen : ℕ → G) (j : ℕ) (hj : j < 127) :
    bval gen (wWord (4 + 4096 * (2 * j))) (wLen (4 + 4096 * (2 * j))) = gen j := by
  have h1 : wWord (4 + 4096 * (2 * j)) = 2 * j := by
    change (4 + 4096 * (2 * j)) >>> 12 = _
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have h2 : wLen (4 + 4096 * (2 * j)) = 1 := by
    change ((4 + 4096 * (2 * j)) >>> 2) &&& (2 ^ 10 - 1) = _
    rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have e1 : 2 * j / 2 ^ (8 * 0) % 256 = 2 * j := by
    rw [Nat.mul_zero, pow_zero, Nat.div_one]
    omega
  rw [h1, h2, bval_succ, show bval gen (2 * j / 256) 0 = 1 from rfl, mul_one, wLet_eq, e1]
  unfold letV
  have e2 : ¬ 2 * j = 255 := by omega
  have e3 : 2 * j % 2 = 0 := by omega
  have e4 : 2 * j / 2 = j := by omega
  simp only [e2, e3, e4, ↓reduceIte]

@[expose] noncomputable def MX1 : ℕ := Nat.sub allFF (Nat.sub (nat_lit 281474976710655) (nat_lit 281470732206336))

@[expose] noncomputable def MX2 : ℕ := Nat.sub allFF (Nat.sub (nat_lit 281474976710655) (nat_lit 5493313634560))

@[expose] noncomputable def MX3 : ℕ := Nat.sub allFF (Nat.sub (nat_lit 281474976710655) (nat_lit 5514788471040))

@[expose] def f5 (k : ℕ) : ℕ := if k = 4 then 5 else k

noncomputable abbrev cg2 : ℕ → XT := fun k => gX (f5 k)

theorem mget_eq {M g v : ℕ} (h : Nat.beq (mget M g) v = true) : mget M g = v := Nat.eq_of_beq_eq_true h

theorem rel1 {P C : ℕ} (h : subRel MX1 P C = true) (hP : HO.entOK P (nat_lit 12) (nat_lit 1023) = true) :
    bval gX (wWord C) (wLen C) = bval gX (wWord P) (wLen P) := by
  refine BindSub.subRel_sound gX gX h (nG := 6) (by norm_num) ?_ (fun q _ => letters_all hP (by norm_num) q) ?_
  · obtain ⟨h1, -⟩ := KB.andB_true hP
    simpa [Nat.shiftLeft_eq] using h1
  · intro g hg hm
    interval_cases g
    · rw [mget_eq (v := 0) (by quickRfl)]; exact ⟨by norm_num, rfl⟩
    · rw [mget_eq (v := 1) (by quickRfl)]; exact ⟨by norm_num, rfl⟩
    · rw [mget_eq (v := 2) (by quickRfl)]; exact ⟨by norm_num, rfl⟩
    · rw [mget_eq (v := 3) (by quickRfl)]; exact ⟨by norm_num, rfl⟩
    · rw [mget_eq (v := 255) (by quickRfl)] at hm; omega
    · rw [mget_eq (v := 255) (by quickRfl)] at hm; omega

theorem rel2 {P C : ℕ} (h : subRel MX2 P C = true) (hP : HO.entOK P (nat_lit 12) (nat_lit 1023) = true) :
    bval cg2 (wWord C) (wLen C) = bval gX (wWord P) (wLen P) := by
  refine BindSub.subRel_sound gX cg2 h (nG := 6) (by norm_num) ?_ (fun q _ => letters_all hP (by norm_num) q) ?_
  · obtain ⟨h1, -⟩ := KB.andB_true hP
    simpa [Nat.shiftLeft_eq] using h1
  · intro g hg hm
    interval_cases g
    · rw [mget_eq (v := 0) (by quickRfl)]; exact ⟨by norm_num, rfl⟩
    · rw [mget_eq (v := 1) (by quickRfl)]; exact ⟨by norm_num, rfl⟩
    · rw [mget_eq (v := 2) (by quickRfl)]; exact ⟨by norm_num, rfl⟩
    · rw [mget_eq (v := 3) (by quickRfl)]; exact ⟨by norm_num, rfl⟩
    · rw [mget_eq (v := 255) (by quickRfl)] at hm; omega
    · rw [mget_eq (v := 4) (by quickRfl)]; exact ⟨by norm_num, rfl⟩

theorem rel3 {P C : ℕ} (h : subRel MX3 P C = true) (hP : HO.entOK P (nat_lit 12) (nat_lit 1023) = true) :
    bval gX (wWord C) (wLen C) = bval gX (wWord P) (wLen P) := by
  refine BindSub.subRel_sound gX gX h (nG := 6) (by norm_num) ?_ (fun q _ => letters_all hP (by norm_num) q) ?_
  · obtain ⟨h1, -⟩ := KB.andB_true hP
    simpa [Nat.shiftLeft_eq] using h1
  · intro g hg hm
    interval_cases g
    · rw [mget_eq (v := 0) (by quickRfl)]; exact ⟨by norm_num, rfl⟩
    · rw [mget_eq (v := 1) (by quickRfl)]; exact ⟨by norm_num, rfl⟩
    · rw [mget_eq (v := 2) (by quickRfl)]; exact ⟨by norm_num, rfl⟩
    · rw [mget_eq (v := 3) (by quickRfl)]; exact ⟨by norm_num, rfl⟩
    · rw [mget_eq (v := 4) (by quickRfl)]; exact ⟨by norm_num, rfl⟩
    · rw [mget_eq (v := 5) (by quickRfl)]; exact ⟨by norm_num, rfl⟩

noncomputable abbrev B4 : Subgroup XT := Subgroup.closure (cg2 '' {j | j < 4})

noncomputable abbrev B5 : Subgroup XT := Subgroup.closure (cg2 '' {j | j < 5})

theorem two_lt (n m : ℕ) (h : 2 * n = m) : {g : ℕ | 2 * g < m} = {g | g < n} := by
  ext g
  simp only [Set.mem_setOf_eq]
  omega

theorem x1_card : Nat.card B4 ≠ 0 ∧ Nat.card B4 ≤ 6912 := by
  have h := lceOk_intro (nR := nat_lit 13) (nS := nat_lit 0) CFSG.KD.Fi22KX1.sH1 CFSG.KD.Fi22KX1.sH0
    (by quickRfl) CFSG.KD.Fi22KX1.sH2 CFSG.KD.Fi22KX1.sH3 (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) X1facts (by quickRfl) (by quickRfl) X1cover (by quickRfl)
  have s := lceOk_sound h gX (by
    intro r hr
    change r < 13 at hr
    interval_cases r
    · exact (rel1 CFSG.KD.Fi22KX1.sH4r0 (xr_ok 0 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel1 CFSG.KD.Fi22KX1.sH4r1 (xr_ok 1 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel1 CFSG.KD.Fi22KX1.sH4r2 (xr_ok 2 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel1 CFSG.KD.Fi22KX1.sH4r3 (xr_ok 3 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel1 CFSG.KD.Fi22KX1.sH4r4 (xr_ok 4 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel1 CFSG.KD.Fi22KX1.sH4r5 (xr_ok 5 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel1 CFSG.KD.Fi22KX1.sH4r6 (xr_ok 6 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel1 CFSG.KD.Fi22KX1.sH4r7 (xr_ok 7 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel1 CFSG.KD.Fi22KX1.sH4r8 (xr_ok 8 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel1 CFSG.KD.Fi22KX1.sH4r9 (xr_ok 9 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel1 CFSG.KD.Fi22KX1.sH4r10 (xr_ok 10 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel1 CFSG.KD.Fi22KX1.sH4r11 (xr_ok 11 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel1 CFSG.KD.Fi22KX1.sH4r12 (xr_ok 12 (by norm_num))).trans (xrel (by norm_num)))
  have e0 : (fun j => bval gX (wWord (CFSG.KD.Fi22KX1.selST j)) (wLen (CFSG.KD.Fi22KX1.selST j))) ''
      {j | j < nat_lit 0} = ∅ :=
    Set.image_eq_empty.mpr (Set.eq_empty_iff_forall_notMem.mpr fun j hj => Nat.not_lt_zero j hj)
  have e1 : gX '' {g | 2 * g < nat_lit 8} = cg2 '' {j | j < 4} := by
    rw [two_lt 4 8 rfl]
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, cg2, f5]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, by rw [if_neg (by omega)]⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, by rw [if_neg (by omega)]⟩
  rw [e0, Subgroup.closure_empty, Subgroup.relIndex_bot_left, e1] at s
  exact s

theorem img_f5 {n : ℕ} {ST : ℕ → ℕ} {gen : ℕ → XT} (hn : n ≤ 5)
    (h : ∀ j < n, bval gen (wWord (ST j)) (wLen (ST j)) = cg2 j) :
    (fun j => bval gen (wWord (ST j)) (wLen (ST j))) '' {j | j < n} = cg2 '' {j | j < n} :=
  Set.image_congr fun j hj => h j hj

theorem x2_index : B4.relIndex B5 ≠ 0 ∧ B4.relIndex B5 ≤ 3960 := by
  have h := lceOk_intro (nR := nat_lit 18) (nS := nat_lit 4) CFSG.KD.Fi22KX2.sH1 CFSG.KD.Fi22KX2.sH0
    (by quickRfl) CFSG.KD.Fi22KX2.sH2 CFSG.KD.Fi22KX2.sH3 (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) X2facts (by quickRfl) (by quickRfl) X2cover (by quickRfl)
  have s := lceOk_sound h cg2 (by
    intro r hr
    change r < 18 at hr
    interval_cases r
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r0 (xr_ok 0 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r1 (xr_ok 1 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r2 (xr_ok 2 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r3 (xr_ok 3 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r4 (xr_ok 13 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r5 (xr_ok 4 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r6 (xr_ok 5 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r7 (xr_ok 6 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r8 (xr_ok 14 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r9 (xr_ok 7 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r10 (xr_ok 15 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r11 (xr_ok 8 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r12 (xr_ok 16 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r13 (xr_ok 17 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r14 (xr_ok 9 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r15 (xr_ok 10 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r16 (xr_ok 18 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel2 CFSG.KD.Fi22KX2.sH4r17 (xr_ok 19 (by norm_num))).trans (xrel (by norm_num)))
  have e0 := img_f5 (n := nat_lit 4) (ST := CFSG.KD.Fi22KX2.selST) (gen := cg2) (by norm_num) (by
    intro j hj
    change j < 4 at hj
    interval_cases j
    · rw [show CFSG.KD.Fi22KX2.selST 0 = 4 + 4096 * (2 * 0) from Nat.eq_of_beq_eq_true CFSG.KD.Fi22KX2.sH5s0,
        bval_one cg2 0 (by norm_num)]
    · rw [show CFSG.KD.Fi22KX2.selST 1 = 4 + 4096 * (2 * 1) from Nat.eq_of_beq_eq_true CFSG.KD.Fi22KX2.sH5s1,
        bval_one cg2 1 (by norm_num)]
    · rw [show CFSG.KD.Fi22KX2.selST 2 = 4 + 4096 * (2 * 2) from Nat.eq_of_beq_eq_true CFSG.KD.Fi22KX2.sH5s2,
        bval_one cg2 2 (by norm_num)]
    · rw [show CFSG.KD.Fi22KX2.selST 3 = 4 + 4096 * (2 * 3) from Nat.eq_of_beq_eq_true CFSG.KD.Fi22KX2.sH5s3,
        bval_one cg2 3 (by norm_num)])
  rw [e0, two_lt 5 (nat_lit 10) rfl] at s
  exact s

theorem x3_index : B5.relIndex ⊤ ≠ 0 ∧ B5.relIndex ⊤ ≤ 8064 := by
  have h := lceOk_intro (nR := nat_lit 23) (nS := nat_lit 5) CFSG.KD.Fi22KX3.sH1 CFSG.KD.Fi22KX3.sH0
    (by quickRfl) CFSG.KD.Fi22KX3.sH2 CFSG.KD.Fi22KX3.sH3 (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) X3facts (by quickRfl) (by quickRfl) X3cover (by quickRfl)
  have s := lceOk_sound h gX (by
    intro r hr
    change r < 23 at hr
    interval_cases r
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r0 (xr_ok 0 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r1 (xr_ok 1 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r2 (xr_ok 2 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r3 (xr_ok 3 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r4 (xr_ok 20 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r5 (xr_ok 13 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r6 (xr_ok 4 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r7 (xr_ok 5 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r8 (xr_ok 6 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r9 (xr_ok 21 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r10 (xr_ok 14 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r11 (xr_ok 7 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r12 (xr_ok 22 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r13 (xr_ok 15 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r14 (xr_ok 8 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r15 (xr_ok 17 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r16 (xr_ok 10 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r17 (xr_ok 23 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r18 (xr_ok 24 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r19 (xr_ok 25 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r20 (xr_ok 26 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r21 (xr_ok 18 (by norm_num))).trans (xrel (by norm_num))
    · exact (rel3 CFSG.KD.Fi22KX3.sH4r22 (xr_ok 19 (by norm_num))).trans (xrel (by norm_num)))
  have e0 := img_f5 (n := nat_lit 5) (ST := CFSG.KD.Fi22KX3.selST) (gen := gX) (by norm_num) (by
    intro j hj
    change j < 5 at hj
    interval_cases j
    · rw [show CFSG.KD.Fi22KX3.selST 0 = 4 + 4096 * (2 * 0) from Nat.eq_of_beq_eq_true CFSG.KD.Fi22KX3.sH5s0,
        bval_one gX 0 (by norm_num)]
      rfl
    · rw [show CFSG.KD.Fi22KX3.selST 1 = 4 + 4096 * (2 * 1) from Nat.eq_of_beq_eq_true CFSG.KD.Fi22KX3.sH5s1,
        bval_one gX 1 (by norm_num)]
      rfl
    · rw [show CFSG.KD.Fi22KX3.selST 2 = 4 + 4096 * (2 * 2) from Nat.eq_of_beq_eq_true CFSG.KD.Fi22KX3.sH5s2,
        bval_one gX 2 (by norm_num)]
      rfl
    · rw [show CFSG.KD.Fi22KX3.selST 3 = 4 + 4096 * (2 * 3) from Nat.eq_of_beq_eq_true CFSG.KD.Fi22KX3.sH5s3,
        bval_one gX 3 (by norm_num)]
      rfl
    · rw [show CFSG.KD.Fi22KX3.selST 4 = 4 + 4096 * (2 * 5) from Nat.eq_of_beq_eq_true CFSG.KD.Fi22KX3.sH5s4,
        bval_one gX 5 (by norm_num)]
      rfl)
  have etop : Subgroup.closure (gX '' {g | 2 * g < nat_lit 12}) = ⊤ := by
    rw [two_lt 6 (nat_lit 12) rfl]
    exact closure_pgen relsX
  rw [e0, etop] at s
  exact s

theorem xt_card : Finite XT ∧ Nat.card XT ≤ 12 * 18393661440 := by
  have hB : B4 ≤ B5 := by
    apply Subgroup.closure_mono
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, by change g < 4 at hg; change g < 5; omega, rfl⟩
  have c5 := KB.card_le_step ⟨hB, x2_index.1, x2_index.2⟩ x1_card
  have c := KB.card_le_step ⟨le_top, x3_index.1, x3_index.2⟩ c5
  rw [Subgroup.card_top] at c
  exact ⟨Nat.finite_of_card_ne_zero c.1, c.2.trans (by norm_num)⟩

end CertificateChecks.KernelFi22

end

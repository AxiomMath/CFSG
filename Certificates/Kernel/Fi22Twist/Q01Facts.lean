module

public import Certificates.Kernel.Fi22Twist.Q01Chk
public import Certificates.Kernel.Fi22Twist.Q01Text
public import Certificates.Kernel.Fi22Twist.Sift
public import Certificates.Kernel.Fi22Twist.CjFacts
public import Certificates.Kernel.Sporadic.Fi22.C2066
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylow
public import CFSG.Certificates.Kernel.Fi22Twist.Q01Sound
public import CFSG.Certificates.Kernel.Common.ForallTree
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist CFSG.KS CFSG.KS.E27Lie
open CFSG.KS.Fi22Twist CFSG.KC.Fi22Rk CFSG.KC.BfsPin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CertificateChecks.KernelFi22Rank.Q2 CFSG.KS.Raw
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CertificateChecks.KernelSpor

set_option maxRecDepth 400000

#kc_forall_tree q431009All (fun u => ch431009q u = true) 108 CFSG.KD.Fi22Twist.ch431009q

#kc_forall_tree qp431009All (fun k => ch431009qp k = true) 2 CFSG.KD.Fi22Twist.ch431009qp

#kc_forall_tree sf431009All (fun u => ch431009sf u = true) 49 CFSG.KD.Fi22Twist.ch431009sf

theorem qGens0_eq : qGens 0 = CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative.rowsOf 3510
    (unpack (3510 * 3) 12 Q0X.F) := by
  have e : qGens 0 = CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative.rowsOf 3510
      (CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative.hexNums 3 qGensHex0) := rfl
  rw [e, rowsOf_same, hexNums_same, CFSG.KS.HexNums.hexNums_of Q0X.eq Q0X.ok]

theorem qGens1_eq : qGens 1 = CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative.rowsOf 3510
    (unpack (3510 * 3) 12 Q1X.F) := by
  have e : qGens 1 = CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative.rowsOf 3510
      (CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative.hexNums 3 qGensHex1) := rfl
  rw [e, rowsOf_same, hexNums_same, CFSG.KS.HexNums.hexNums_of Q1X.eq Q1X.ok]

theorem q01_gens {k F : ℕ} {R : ℕ → ℕ}
    (hq : qGens k = CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative.rowsOf 3510
      (unpack (3510 * 3) 12 F))
    (hr : rowsK 3510 12 3 F R = true) :
    (∀ t < 3, PP 3510 12 (R t)) ∧
      permsA 3510 (qGens k) = Set.range fun t : Fin 3 => permOfArr 3510 (unpack 3510 12 (R t)) := by
  obtain ⟨hsz, hget⟩ := CFSG.KC.Fi22RkS.rows_of (m := 3510) (K := 3) (w := 12) (by norm_num) szA
    hr
  refine ⟨fun t ht => (hget t ht).2, ?_⟩
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < 3 := by
      have h : i < (qGens k).size := hi
      rwa [hq, hsz] at h
    refine ⟨⟨i, hi'⟩, ?_⟩
    beta_reduce
    rw [hq, (hget i hi').1]
  · rintro ⟨⟨t, ht⟩, rfl⟩
    refine ⟨t, ?_, ?_⟩
    · change t < (qGens k).size
      rw [hq, hsz]
      exact ht
    · beta_reduce
      rw [hq, (hget t ht).1]

@[expose] noncomputable def q01H (k : ℕ) : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (unpack 3510 12 (KQ (108 + k)))

theorem q01H_PP {k : ℕ} (hk : k < 2) : PP 3510 12 (KQ (108 + k)) := by
  have h := qp431009All k hk
  unfold ch431009qp at h
  rw [sB_eq] at h
  exact PP_of_permOK szA h

theorem q0_facts : Nat.card (Subgroup.closure (permsA 3510 (qGens 0))) = 27 ∧
    ∀ A ≤ Subgroup.closure (permsA 3510 (qGens 0)), Nat.card A = 27 →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 3 = 1) →
      ∀ x ∈ A, q01H 0 * x * (q01H 0)⁻¹ ∈ dSub 0 := by
  obtain ⟨hPP, hset⟩ := q01_gens qGens0_eq ch431009q0x
  rw [hset]
  refine q01_sound (K := KQ) (T := TQ) (DF := DF) (Gk := KQ 108) (j := 0)
    (g := fun t => permOfArr 3510 (unpack 3510 12 (KQ (Nat.succ t)))) (by norm_num)
    (fun t ht => prep_of_PP (hPP t ht)) (prep_of_PP (q01H_PP (k := 0) (by norm_num)))
    (fun e he => df_mem (by norm_num) e he) fun i hi => ?_
  have hi' : i < 108 := by omega
  have h := q431009All i hi'
  unfold ch431009q at h
  rw [bRec_eq, if_pos (Eq.mpr Nat.blt_eq hi)] at h
  exact h

theorem q1_facts : Nat.card (Subgroup.closure (permsA 3510 (qGens 1))) = 81 ∧
    ∀ A ≤ Subgroup.closure (permsA 3510 (qGens 1)), Nat.card A = 27 →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 3 = 1) →
      ∀ x ∈ A, q01H 1 * x * (q01H 1)⁻¹ ∈ dSub 1 := by
  obtain ⟨hPP, hset⟩ := q01_gens qGens1_eq ch431009q1x
  rw [hset]
  refine q01_sound (K := KQ1) (T := TQ1) (DF := DF) (Gk := KQ 109) (j := 1)
    (g := fun t => permOfArr 3510 (unpack 3510 12 (KQ1 (Nat.succ t)))) (by norm_num)
    (fun t ht => prep_of_PP (hPP t ht)) (prep_of_PP (q01H_PP (k := 1) (by norm_num)))
    (fun e he => df_mem (by norm_num) e he) fun i hi => ?_
  have hi' : 27 + i < 108 := by omega
  have h := q431009All (27 + i) hi'
  unfold ch431009q at h
  have hb : ¬ (Nat.blt (27 + i) 27 = true) := by
    rw [Nat.blt_eq]
    omega
  have e : Nat.sub (27 + i) 27 = i := Nat.add_sub_cancel_left 27 i
  rw [bRec_eq, if_neg hb, e] at h
  exact h

theorem sfG_hq {k : ℕ} (hk : k < 2) : sfG (21 + k) = KQ (108 + k) := by
  interval_cases k <;> rfl

theorem sfG_q0 {t : ℕ} (ht : t < 3) : sfG (23 + t) = KQ (Nat.succ t) := by
  interval_cases t <;> rfl

theorem sfG_q1 {t : ℕ} (ht : t < 3) : sfG (26 + t) = KQ1 (Nat.succ t) := by
  interval_cases t <;> rfl

theorem sfG_q2 {k : ℕ} (hk : k < 5) : sfG (29 + k) = key (GI k) := by
  interval_cases k <;> rfl

theorem sfG_row {k : ℕ} (hk : k < 15) : sfG (34 + k) = rowR TX.F k := by
  interval_cases k <;> rfl


theorem mem_P_of_PP {p : ℕ} (hP : PP 3510 12 p) (hc : Fi22X.cn p = true)
    (hs : Fi22X.siftP p = true) : permOfArr 3510 (unpack 3510 12 p) ∈ fi22P :=
  (fi22InP_iff (rep_permOfArr (CFSG.KS.Raw.Orb.isInvA_unpack
    (CFSG.KS.PinvS.permOK_pinvS hP.1 hP.2))).1).1
    (Fi22C2066.fi22InP_of (PS := fun _ => p) (j := 0) (g := unpack 3510 12 p) rfl hc hs)

theorem sf_mem {u p : ℕ} (hu : u < 49) (hp : sfG u = p) (hP : PP 3510 12 p) :
    permOfArr 3510 (unpack 3510 12 p) ∈ fi22P := by
  have h := sf431009All u hu
  unfold ch431009sf at h
  rw [sB_eq, hp] at h
  obtain ⟨hc, hs⟩ := (bAnd_iff _ _).1 h
  exact mem_P_of_PP hP hc hs

theorem cj_memP {r : ℕ} (hr : r < 21) : permOfArr 3510 (unpack 3510 12 (CJ r)) ∈ fi22P := by
  refine sf_mem (u := r) (by omega) ?_ (PP_of_permOK szA (cj431009cpAll r hr))
  have hb : Nat.blt r 21 = true := Eq.mpr Nat.blt_eq hr
  unfold sfG
  rw [hb]

theorem q01H_memP {k : ℕ} (hk : k < 2) : q01H k ∈ fi22P :=
  sf_mem (u := 21 + k) (by omega) (sfG_hq hk) (q01H_PP hk)

theorem qk_le_P {k : ℕ} (hk : k < 3) : Subgroup.closure (permsA 3510 (qGens k)) ≤ fi22P := by
  interval_cases k
  · obtain ⟨hPP, hset⟩ := q01_gens qGens0_eq ch431009q0x
    rw [hset, Subgroup.closure_le]
    rintro _ ⟨⟨t, ht⟩, rfl⟩
    exact sf_mem (u := 23 + t) (by omega) (sfG_q0 ht) (hPP t ht)
  · obtain ⟨hPP, hset⟩ := q01_gens qGens1_eq ch431009q1x
    rw [hset, Subgroup.closure_le]
    rintro _ ⟨⟨t, ht⟩, rfl⟩
    exact sf_mem (u := 26 + t) (by omega) (sfG_q1 ht) (hPP t ht)
  · obtain ⟨hsz, hget⟩ := CFSG.KC.Fi22RkS.rows_of (m := 3510) (K := 5) (w := 12) (by norm_num)
      szA rowsT
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 5 := by
      have h : k < (qGens 2).size := hk
      rwa [qGens_eq, hsz] at h
    beta_reduce
    rw [qGens_eq, (hget k hk').1]
    exact sf_mem (u := 29 + k) (by omega) (sfG_q2 hk') (hget k hk').2

theorem dSub_le_P {j : ℕ} (hj : j < 5) : dSub j ≤ fi22P := by
  have hm : ∀ m < 3, permOfArr 3510 (repXYZ[3 * j + m]!) ∈ fi22P := by
    intro m hm
    have hk : 3 * j + m < 15 := by omega
    rw [(repXYZ_facts.2 _ hk).1]
    exact sf_mem (u := 34 + (3 * j + m)) (by omega) (sfG_row hk) (repXYZ_facts.2 _ hk).2
  unfold dSub
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact hm 0 (by norm_num)
  · exact hm 1 (by norm_num)
  · exact hm 2 (by norm_num)

theorem q2_e27_conjP (A : Subgroup (Equiv.Perm (Fin 3510)))
    (hA : A ≤ Subgroup.closure (permsA 3510 (qGens 2))) (hcard : Nat.card A = 27)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ 3 = 1) :
    ∃ j < 5, ∃ h ∈ fi22P, ∀ x ∈ A, h * x * h⁻¹ ∈ dSub j := by
  obtain ⟨j, hj, h, hh, hc⟩ := q2_e27_conj A hA hcard hcomm hexp
  refine ⟨j, hj, h, (Subgroup.closure_le _).2 ?_ hh, hc⟩
  rintro _ (⟨r, hr, rfl⟩ | hx)
  · exact cj_memP hr
  · exact qk_le_P (k := 2) (by norm_num) hx

theorem q01_e27_conjP {k : ℕ} (hk : k < 2) (A : Subgroup (Equiv.Perm (Fin 3510)))
    (hA : A ≤ Subgroup.closure (permsA 3510 (qGens k))) (hcard : Nat.card A = 27)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hexp : ∀ a ∈ A, a ^ 3 = 1) :
    ∃ h ∈ fi22P, ∀ x ∈ A, h * x * h⁻¹ ∈ dSub k := by
  refine ⟨q01H k, q01H_memP hk, ?_⟩
  interval_cases k
  · exact q0_facts.2 A hA hcard hcomm hexp
  · exact q1_facts.2 A hA hcard hcomm hexp

end CertificateChecks.KernelFi22Twist

end

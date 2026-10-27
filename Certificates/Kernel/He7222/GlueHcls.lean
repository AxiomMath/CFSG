module

public import Certificates.Kernel.He7222.GlueFib
public import Certificates.Kernel.He7222.GlueKs
public import Certificates.Kernel.He7222.GlueNv
public import Certificates.Kernel.He7222.GoodK
public import Certificates.Kernel.He7222.InvK
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.OrbRow.LevelSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHe7222

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KC.HeChain CFSG.KS.Raw.Orb
  CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.KD.He7222 CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.He
  CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Monster.B.Co2.Native
  CertificateChecks.KernelLC.HeFix CertificateChecks.KernelHe7223
  CertificateChecks.KernelSchreierFam.He725 CFSG.KS.PF

theorem prep_hPI {j : ℕ}
    (hj : j < 8) : PRep 8330 14 (getS scHI j) (hP j)⁻¹ := by
  have hl : scH.length = 8 := by
    rw [← lenS_eq]
    exact Nat.eq_of_beq_eq_true ch7222hlen
  have hinvj := (invLK_sound ch7222ih).2 j (by rw [hl]; exact hj)
  have hshrj : getS scH j >>> (8330 * 14) = 0 :=
    Nat.eq_of_beq_eq_true (allN_spec ch7222shrA j hj)
  rw [getS_eq] at hshrj ⊢
  refine invK_rep (by norm_num) (by norm_num) hinvj ?_ hshrj
  rw [← getS_eq]
  exact prep_hP hj

theorem xrK_spec {XR : List ℕ} {KC : List (List ℕ)} (h : xrK XR (lenLN KC) = true) :
    ∀ r < XR.length, XR.getD r 0 < KC.length := by
  intro r hr
  have := allN_spec h r (by rw [lenS_eq]; exact hr)
  rw [Nat.blt_eq, lenLN_eq, getS_eq] at this
  exact this

theorem a0_fib :
    ∀ j < 2, ∀ r < (getLs a0XR j).length, ∃ FR FT GD : List (List ℕ),
      fibK 14 (mask 14) (getLL a0KTs j) (getLL a0KLs j) (getS scH j ::
        stkK a0Ts ((getLL a0KC (getS a0SRep j)).getD ((getLs a0XR j).getD r 0) [])) FR FT = true ∧
      ftOK (getLL a0KTs j) FT = true ∧ frOK (lenLN FT) FR = true ∧
      goodLK 14 (mask 14) (getLL a0KTs j) (getS scH j ::
        stkK a0Ts ((getLL a0KC (getS a0SRep j)).getD ((getLs a0XR j).getD r 0) [])) (HG.F 0) LU
        LUI DW R5 R7 FT GD = true := by
  intro j hj r hr
  have hfi := allN_spec (allN_spec ch7222fia j hj) r (by rw [lenS_eq]; exact hr)
  simp only [strictB_eqP, bAnd_iff, Nat.blt_eq] at hfi
  obtain ⟨hi, hj0, hr1⟩ := hfi
  have e0 := Nat.eq_of_beq_eq_true hj0
  have e1 := Nat.eq_of_beq_eq_true hr1
  set i := Nat.add (offK a0XR j) r with hidef
  refine ⟨getLL a0FR i, getLL a0FT i, getLL a0GD i, ?_, ?_, ?_, ?_⟩
  · have h := ch7222fba i hi
    unfold fbA at h
    simp only [strictB_eqP] at h
    rw [e0, e1, getLs_eq (getLL a0KC (getS a0SRep j)), getS_eq (getLs a0XR j) r] at h
    exact h
  · have h := allN_spec ch7222fta i hi
    unfold ftK at h
    simp only [strictB_eqP, bAnd_iff] at h
    rw [e0] at h
    exact h.1
  · have h := allN_spec ch7222fta i hi
    unfold ftK at h
    simp only [strictB_eqP, bAnd_iff] at h
    exact h.2
  · have h := ch7222gda i hi
    unfold gdA at h
    simp only [strictB_eqP] at h
    rw [e0, e1, getLs_eq (getLL a0KC (getS a0SRep j)), getS_eq (getLs a0XR j) r] at h
    exact h

theorem a0_scan_fib :
    ∀ j < 2, ∀ z ∈ centralizerIn heP (heGenPerm 0), HConcl (heGenPerm 0) (hP j * z) := by
  intro j hj
  obtain ⟨hKent, hKfac, hKcomp⟩ := a0_kch j hj
  have hrt := ch7222rt
  simp only [Bool.and_eq_true] at hrt
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨r0, r1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hrt
  have hsr := ch7222srep
  simp only [Bool.and_eq_true] at hsr
  obtain ⟨⟨⟨⟨⟨⟨⟨s0, s1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hsr
  have hxr := ch7222xr
  simp only [Bool.and_eq_true] at hxr
  obtain ⟨⟨⟨⟨⟨⟨x0, x1⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hxr
  have key : ∀ r : ℕ, getS a0SRep j = r → tupOK a0Ts (getLs a0RT r) = true → ca r = true →
      xrK (getLs a0XR j) (lenLN (getLL a0KC r)) = true →
      cjK (getS scH j) (HG.F 0) (rep0 (getS a0SRep j)) = true →
      sa j = true → srA j = true →
      (getLL a0KTs j).length = (getLs a0QBase j).length →
      getLL a0KLs j = (getLL a0KTs j).reverse →
      ∀ z ∈ centralizerIn heP (heGenPerm 0), HConcl (heGenPerm 0) (hP j * z) := by
    intro r hr ht hca hx hcj hsa hsrA hKL hKLs
    rw [← hr] at ht hca hx
    have hτ := heGenPerm_mem (by norm_num : (0 : ℕ) < 2)
    have hhs := conj_of_cjK hcj (prep_hP (by omega)) prep_a0 (prep_rep0 ht).1
    have hfib := a0_fib j hj
    rw [hKLs] at hfib
    exact scan_fibre (τP := HG.F 0) (s := rep0P (getS a0SRep j)) prep_a0 hτ
      (prep_hP (by omega)) (prep_hPI (by omega)) (hP_mem (by omega)) hhs (prep_rep0 ht).2
      (Ts := a0Ts) (TIs := a0TIs) rfl
      (fun t ht j hj => ⟨(a0_cent_chain.1 t ht j hj).1, (a0_cent_chain.1 t ht j hj).2.1⟩)
      (fun t ht j hj => tree_shr (by norm_num) (by norm_num) (a0_tree t ht) j hj) a0_inv
      (rs := stkK a0Ts (getLs a0RT (getS a0SRep j)))
      (fun p => evK_rep (stkK_rep (n := 8330) (w := 14) rec0 ht a0_hrep) p) hca hKL hKent
      hKfac hKcomp hsa hsrA (xrK_spec hx) hfib
  match j, hj with
  | 0, _ =>
    exact key 0 (Nat.eq_of_beq_eq_true s0) r0 ch7222ca0 x0 ch7222cj0 ch7222sa0 ch7222sra0
      (chainK_sound ch7222kca0).1 rfl
  | 1, _ =>
    exact key 1 (Nat.eq_of_beq_eq_true s1) r1 ch7222ca1 x1 ch7222cj1 ch7222sa1 ch7222sra1
      (chainK_sound ch7222kca1).1 rfl

theorem a0_hcls :
    ∀ y ∈ heP, HConcl (heGenPerm 0) y :=
  hconcl_of_entry a0_scan_entry fun j hj z hz => by
    rcases Nat.lt_or_ge j 2 with h2 | h2
    · exact a0_scan_fib j h2 z hz
    · have : j = 2 := by omega
      subst this
      exact a0_scan2 z hz

theorem t1_fib :
    ∀ j < 5, ∀ r < (getLs t1XR j).length, ∃ FR FT GD : List (List ℕ),
      fibK 14 (mask 14) (getLL t1KTs j) (getLL t1KLs j) (getS scH (Nat.add 3 j) ::
        stkK t1Ts ((getLL t1KC (getS t1SRep j)).getD ((getLs t1XR j).getD r 0) [])) FR FT = true ∧
      ftOK (getLL t1KTs j) FT = true ∧ frOK (lenLN FT) FR = true ∧
      goodLK 14 (mask 14) (getLL t1KTs j) (getS scH (Nat.add 3 j) ::
        stkK t1Ts ((getLL t1KC (getS t1SRep j)).getD ((getLs t1XR j).getD r 0) [])) PT1 LU
        LUI DW R5 R7 FT GD = true := by
  intro j hj r hr
  have hfi := allN_spec (allN_spec ch7222fit j hj) r (by rw [lenS_eq]; exact hr)
  simp only [strictB_eqP, bAnd_iff, Nat.blt_eq] at hfi
  obtain ⟨hi, hj0, hr1⟩ := hfi
  have e0 := Nat.eq_of_beq_eq_true hj0
  have e1 := Nat.eq_of_beq_eq_true hr1
  set i := Nat.add (offK t1XR j) r with hidef
  refine ⟨getLL t1FR i, getLL t1FT i, getLL t1GD i, ?_, ?_, ?_, ?_⟩
  · have h := ch7222fbt i hi
    unfold fbT at h
    simp only [strictB_eqP] at h
    rw [e0, e1, getLs_eq (getLL t1KC (getS t1SRep j)), getS_eq (getLs t1XR j) r] at h
    exact h
  · have h := allN_spec ch7222ftt i hi
    unfold ftK at h
    simp only [strictB_eqP, bAnd_iff] at h
    rw [e0] at h
    exact h.1
  · have h := allN_spec ch7222ftt i hi
    unfold ftK at h
    simp only [strictB_eqP, bAnd_iff] at h
    exact h.2
  · have h := ch7222gdt i hi
    unfold gdT at h
    simp only [strictB_eqP] at h
    rw [e0, e1, getLs_eq (getLL t1KC (getS t1SRep j)), getS_eq (getLs t1XR j) r] at h
    exact h

theorem t1_scan_fib :
    ∀ j < 5, ∀ z ∈ centralizerIn heP heT1P, HConcl heT1P (hP (3 + j) * z) := by
  intro j hj
  obtain ⟨hKent, hKfac, hKcomp⟩ := t1_kch j hj
  have hrt := ch7222rt
  simp only [Bool.and_eq_true] at hrt
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, q1⟩, q2⟩, q3⟩, -⟩, q5⟩, q6⟩ := hrt
  have hsr := ch7222srep
  simp only [Bool.and_eq_true] at hsr
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, s0⟩, s1⟩, s2⟩, s3⟩, s4⟩ := hsr
  have hxr := ch7222xr
  simp only [Bool.and_eq_true] at hxr
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, x0⟩, x1⟩, x2⟩, x3⟩, x4⟩ := hxr
  have key : ∀ r : ℕ, getS t1SRep j = r → tupOK t1Ts (getLs t1RT r) = true → ct r = true →
      xrK (getLs t1XR j) (lenLN (getLL t1KC r)) = true →
      cjK (getS scH (3 + j)) PT1 (rep1 (getS t1SRep j)) = true →
      st j = true → srT j = true →
      (getLL t1KTs j).length = (getLs t1QBase j).length →
      getLL t1KLs j = (getLL t1KTs j).reverse →
      ∀ z ∈ centralizerIn heP heT1P, HConcl heT1P (hP (3 + j) * z) := by
    intro r hr ht hct hx hcj hst hsrT hKL hKLs
    rw [← hr] at ht hct hx
    have hhs := conj_of_cjK hcj (prep_hP (by omega)) prep_t1 (prep_rep1 ht).1
    have hfib := t1_fib j hj
    rw [hKLs] at hfib
    exact scan_fibre (τP := PT1) (s := rep1P (getS t1SRep j)) prep_t1 heT1P_mem
      (prep_hP (by omega)) (prep_hPI (by omega)) (hP_mem (by omega)) hhs (prep_rep1 ht).2
      (Ts := t1Ts) (TIs := t1TIs) rfl
      (fun t ht j hj => ⟨(t1_cent_chain.1 t ht j hj).1, (t1_cent_chain.1 t ht j hj).2.1⟩)
      (fun t ht j hj => tree_shr (by norm_num) (by norm_num) (t1_tree t ht) j hj) t1_inv
      (rs := stkK t1Ts (getLs t1RT (getS t1SRep j)))
      (fun p => evK_rep (stkK_rep (n := 8330) (w := 14) rec1 ht t1_hrep) p) hct hKL hKent
      hKfac hKcomp hst hsrT (xrK_spec hx) hfib
  match j, hj with
  | 0, _ =>
    exact key 1 (Nat.eq_of_beq_eq_true s0) q1 ch7222ct1 x0 ch7222cj3 ch7222st0 ch7222srt0
      (chainK_sound ch7222kct0).1 rfl
  | 1, _ =>
    exact key 2 (Nat.eq_of_beq_eq_true s1) q2 ch7222ct2 x1 ch7222cj4 ch7222st1 ch7222srt1
      (chainK_sound ch7222kct1).1 rfl
  | 2, _ =>
    exact key 3 (Nat.eq_of_beq_eq_true s2) q3 ch7222ct3 x2 ch7222cj5 ch7222st2 ch7222srt2
      (chainK_sound ch7222kct2).1 rfl
  | 3, _ =>
    exact key 5 (Nat.eq_of_beq_eq_true s3) q5 ch7222ct5 x3 ch7222cj6 ch7222st3 ch7222srt3
      (chainK_sound ch7222kct3).1 rfl
  | 4, _ =>
    exact key 6 (Nat.eq_of_beq_eq_true s4) q6 ch7222ct6 x4 ch7222cj7 ch7222st4 ch7222srt4
      (chainK_sound ch7222kct4).1 rfl

theorem t1_hcls :
    ∀ y ∈ heP, HConcl heT1P y :=
  hconcl_of_entry (Hs := fun j => hP (3 + j)) t1_scan_entry fun j hj z hz =>
    t1_scan_fib j hj z hz

end CertificateChecks.KernelHe7222

end

module

public import Certificates.Kernel.Sporadic.Fi22.S2072Chk
public import Certificates.Kernel.Sporadic.Fi22.S2072Sift
public import Certificates.Kernel.Sporadic.Fi22.N2070Final
public import Certificates.Kernel.Sporadic.Fi22.C2079B
public import CFSG.Certificates.Kernel.Fi22Syl2072Sound
public import CFSG.Sporadic.FischerOddCore.Fi22SylowWit

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2072

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Syl2072 CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22X

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem unpack_get {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  unfold unpack
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

theorem ap_line {j : Nat} (hj : j < 306) (y : Fin 3510) :
    ap (Fi22CentT.L j) y = (fi22CentPerm j y : ℕ) := by
  rw [← rep_fi22CentPerm hj y, N2070.cent_eq hj, unpack_get y.2]
  rfl

theorem injK_line {j : Nat} (hj : j < 306) :
    CFSG.KS.PinvS.InjK 3510 12 (Fi22CentT.L j) := by
  refine ⟨fun i hi => ?_, fun a ha b hb e => ?_⟩
  · have h := ap_line hj ⟨i, hi⟩
    change pg 12 (mask 12) _ i = _ at h
    rw [h]
    exact (fi22CentPerm j _).2
  · have ea := ap_line hj ⟨a, ha⟩
    have eb := ap_line hj ⟨b, hb⟩
    change pg 12 (mask 12) _ a = _ at ea
    change pg 12 (mask 12) _ b = _ at eb
    rw [ea, eb] at e
    exact congrArg Fin.val ((fi22CentPerm j).injective (Fin.ext e))

theorem ap_pinv {j : Nat} (hj : j < 306) (y : Fin 3510) :
    ap (pinvS 3510 12 (mask 12) (Fi22CentT.L j)) y = ((fi22CentPerm j)⁻¹ y : ℕ) := by
  have h := CFSG.KS.PinvS.pg_pinvS (by norm_num) (injK_line hj) ((fi22CentPerm j)⁻¹ y).2
  have e := ap_line hj ((fi22CentPerm j)⁻¹ y)
  change pg 12 (mask 12) _ _ = _ at e
  have key : ∀ σ : Equiv.Perm (Fin 3510), σ (σ⁻¹ y) = y := fun σ => σ.apply_symm_apply y
  have e2 := key (fi22CentPerm j)
  rw [e, e2] at h
  exact h

theorem mem_of_memK
    {c kS kO BP lo k : Nat} {S SI LR ST : Nat → Nat} {D : List (List Int)} (hc : c < 5)
    (hb : Binds 3510 12 S kS 6 BP (fi22CentStrong c) #[0, 1, 2, 3, 6, 4])
    (hh : headK 3510 12 (mask 12) (3510 * 12) (pidn 3510 12) S SI kS kO D 6 BP = true)
    (ht : TreeOK 3510 12 S SI LR kS 6 BP) (hst : StepsOK 3510 12 S ST kS 6 BP)
    (hm : memK S SI LR ST kS BP lo k = true) (hl : lo + k ≤ 306) {j : Nat} (hj : j < k) :
    fi22CentPerm (lo + j) ∈ fi22H c := by
  have h := allN_spec hm j hj
  beta_reduce at h
  rw [strictB_eq'] at h
  obtain ⟨hcn, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hsp, hbk⟩ := (bAnd_iff _ _).1 h
  have hperm := Fi22E2065.perm (L := lo + j) (by omega)
  have hrep := (Fo22C.rep_of_perm hperm).1
  have e : fi22CentPerm (lo + j) = permOfArr 3510 (unpack 3510 12 (Fi22CentT.L (lo + j))) := by
    rw [fi22CentPerm, N2070.cent_eq (by omega)]
  rw [e]
  exact Fo22C.mem_H hc hb hh ht hst hrep (Fo22C.mem_P hcn hsp hperm) hbk

@[expose] def inR : Nat → Nat → Bool
  | 0, j => (decide (80 ≤ j) && decide (j < 83)) || (decide (108 ≤ j) && decide (j < 134))
  | 1, j => (decide (83 ≤ j) && decide (j < 88)) || (decide (134 ≤ j) && decide (j < 148))
  | 2, j => (decide (88 ≤ j) && decide (j < 94)) || (decide (148 ≤ j) && decide (j < 162))
  | 3, j => (decide (94 ≤ j) && decide (j < 103)) || (decide (162 ≤ j) && decide (j < 224))
  | 4, j => (decide (103 ≤ j) && decide (j < 108)) || (decide (224 ≤ j) && decide (j < 240))
  | _, _ => false

theorem inR_lt {c j : Nat} (h : inR c j = true) : j < 306 := by
  match c with
  | 0 | 1 | 2 | 3 | 4 =>
    simp only [inR, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  | _ + 5 => simp [inR] at h

theorem bH0 : Binds 3510 12 Fi22H0.S 19 6 Fi22H0.BP (fi22CentStrong 0) #[0, 1, 2, 3, 6, 4] :=
  Fo22C.bindsH Fi22CentB.text_eq (st := 0) (by norm_num) rfl rfl (by norm_num) Fi22C2066.b0
    Fi22C2066.p0
theorem bH1 : Binds 3510 12 Fi22H1.S 16 6 Fi22H1.BP (fi22CentStrong 1) #[0, 1, 2, 3, 6, 4] :=
  Fo22C.bindsH Fi22CentB.text_eq (st := 19) (by norm_num) rfl rfl (by norm_num) Fi22C2066.b1
    Fi22C2066.p1

theorem memLine
    {c j : Nat} (hc : c < 5) (h : inR c j = true) : fi22CentPerm j ∈ fi22H c := by
  have key : ∀ lo, lo ≤ j → (∀ d, fi22CentPerm (lo + d) ∈ fi22H c ∨ ¬ d = j - lo) →
      fi22CentPerm j ∈ fi22H c := by
    intro lo hlo hd
    rcases hd (j - lo) with h' | h'
    · rwa [Nat.add_sub_cancel' hlo] at h'
    · exact absurd rfl h'
  interval_cases c <;> simp only [inR, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine key 80 h1 fun d => ?_
      by_cases hd : d < 3
      · exact .inl (mem_of_memK (by norm_num) bH0 Fi22H0.head Fi22H0.tl Fi22H0.hst mc0s
          (by norm_num) hd)
      · exact .inr (by omega)
    · refine key 108 h1 fun d => ?_
      by_cases hd : d < 26
      · exact .inl (mem_of_memK (by norm_num) bH0 Fi22H0.head Fi22H0.tl Fi22H0.hst mc0w
          (by norm_num) hd)
      · exact .inr (by omega)
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine key 83 h1 fun d => ?_
      by_cases hd : d < 5
      · exact .inl (mem_of_memK (by norm_num) bH1 Fi22H1.head Fi22H1.tl Fi22H1.hst mc1s
          (by norm_num) hd)
      · exact .inr (by omega)
    · refine key 134 h1 fun d => ?_
      by_cases hd : d < 14
      · exact .inl (mem_of_memK (by norm_num) bH1 Fi22H1.head Fi22H1.tl Fi22H1.hst mc1w
          (by norm_num) hd)
      · exact .inr (by omega)
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine key 88 h1 fun d => ?_
      by_cases hd : d < 6
      · exact .inl (mem_of_memK (by norm_num) (Fo22C.bindsH2 Fi22CentB.text_eq) Fi22H2.head
          Fi22H2.tl Fi22H2.hst mc2s (by norm_num) hd)
      · exact .inr (by omega)
    · refine key 148 h1 fun d => ?_
      by_cases hd : d < 14
      · exact .inl (mem_of_memK (by norm_num) (Fo22C.bindsH2 Fi22CentB.text_eq) Fi22H2.head
          Fi22H2.tl Fi22H2.hst mc2w (by norm_num) hd)
      · exact .inr (by omega)
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine key 94 h1 fun d => ?_
      by_cases hd : d < 9
      · exact .inl (mem_of_memK (by norm_num) (Fo22C.bindsH3 Fi22CentB.text_eq) Fi22H3.head
          Fi22H3.tl Fi22H3.hst mc3s (by norm_num) hd)
      · exact .inr (by omega)
    · refine key 162 h1 fun d => ?_
      by_cases hd : d < 62
      · exact .inl (mem_of_memK (by norm_num) (Fo22C.bindsH3 Fi22CentB.text_eq) Fi22H3.head
          Fi22H3.tl Fi22H3.hst mc3w (by norm_num) hd)
      · exact .inr (by omega)
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine key 103 h1 fun d => ?_
      by_cases hd : d < 5
      · exact .inl (mem_of_memK (by norm_num) (Fo22C.bindsH4 Fi22CentB.text_eq) Fi22H4.head
          Fi22H4.tl Fi22H4.hst mc4s (by norm_num) hd)
      · exact .inr (by omega)
    · refine key 224 h1 fun d => ?_
      by_cases hd : d < 16
      · exact .inl (mem_of_memK (by norm_num) (Fo22C.bindsH4 Fi22CentB.text_eq) Fi22H4.head
          Fi22H4.tl Fi22H4.hst mc4w (by norm_num) hd)
      · exact .inr (by omega)

theorem ranges : ∀ s < 11, sf s 0 < 5 ∧ (∀ k < sf s 4, inR (sf s 0) (sf s 3 + k) = true) ∧
    ∀ w < sf s 7, inR (sf s 0) (wf (sf s 6 + w) 0) = true ∧
      inR (sf s 0) (wf (sf s 6 + w) 1) = true := by
  decide +kernel

theorem sepB
    {G : Equiv.Perm (Fin 3510)} (hG : G ∈ fi22P) (h : onB G 1) : G = 1 := by
  refine Fi22C2066.fi22P_sep hG fun t ht hb => ?_
  have ht6 : t < 6 := ht
  have e : (Fi22C2066.B)[t]! = bp t := by interval_cases t <;> decide +kernel
  have h' := h t ht6 (e ▸ hb)
  have e' : (⟨(Fi22C2066.B)[t]!, hb⟩ : Fin 3510) = ⟨bp t, e ▸ hb⟩ := Fin.ext e
  rw [e']
  exact h'

theorem recS_all (s : Nat) (hs : s < 11) : recS s = true := by
  interval_cases s
  exacts [recS0, recS1, recS2, recS3, recS4, recS5, recS6, recS7, recS8, recS9, recS10]

theorem sf_eq : sf = fi22CentSylowField := rfl
theorem wf_eq : wf = fi22CentWitField := rfl
theorem X_eq (s w : Nat) : X s w = Fi22CentT.L (fi22CentWitField (fi22CentSylowField s 6 + w) 0) :=
  rfl
theorem H_eq (s w : Nat) : H s w = Fi22CentT.L (fi22CentWitField (fi22CentSylowField s 6 + w) 1) :=
  rfl
theorem sylX_eq (s w : Nat) :
    fi22SylX s w = fi22CentPerm (fi22CentWitField (fi22CentSylowField s 6 + w) 0) := rfl
theorem sylH_eq (s w : Nat) :
    fi22SylH s w = fi22CentPerm (fi22CentWitField (fi22CentSylowField s 6 + w) 1) := rfl

theorem ranges' {s : Nat} (hs : s < 11) : fi22CentSylowField s 0 < 5 ∧
    (∀ k < fi22CentSylowField s 4,
      inR (fi22CentSylowField s 0) (fi22CentSylowField s 3 + k) = true) ∧
    ∀ w < fi22CentSylowField s 7,
      inR (fi22CentSylowField s 0) (fi22CentWitField (fi22CentSylowField s 6 + w) 0) = true ∧
      inR (fi22CentSylowField s 0) (fi22CentWitField (fi22CentSylowField s 6 + w) 1) = true := by
  have h := ranges s hs
  rwa [sf_eq, wf_eq] at h

theorem recS_parts {s : Nat} (hs : s < 11) :
    recK Fi22CentT.L CFSG.KD.Syl2072.D (X s) (fi22CentSylowField s 3) (fi22CentSylowField s 4)
      (off s) (fi22CentSylowField s 2) (fi22CentSylowField s 1) (fi22CentSylowField s 7)
      (root s) = true ∧
    ∀ w < fi22CentSylowField s 7,
      witK (Fi22CentT.L (fi22CentWitField (fi22CentSylowField s 6 + w) 0))
        (Fi22CentT.L (fi22CentWitField (fi22CentSylowField s 6 + w) 1))
        (pinvS 3510 12 (mask 12) (Fi22CentT.L (fi22CentWitField (fi22CentSylowField s 6 + w) 1)))
        (fi22CentSylowField s 1) (fi22CentWitField (fi22CentSylowField s 6 + w) 3) = true := by
  have hrS := recS_all s hs
  unfold recS at hrS
  obtain ⟨hrec, hwit⟩ := (bAnd_iff _ _).1 hrS
  rw [sf_eq] at hrec hwit
  refine ⟨hrec, fun w hw => ?_⟩
  have h := allN_spec hwit w hw
  beta_reduce at h
  rw [strictB_eq', X_eq, H_eq, wf_eq] at h
  exact h

theorem seeds_le
    {s : ℕ} (hs : s < 11) : fi22CentSylowSub s ≤ fi22H (fi22CentSylowField s 0) := by
  obtain ⟨hc, hR, -⟩ := ranges' hs
  rw [fi22CentSylowSub, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact memLine hc (hR k hk)

@[expose] noncomputable def gS (s k : ℕ) : Equiv.Perm (Fin 3510) :=
  fi22CentPerm (fi22CentSylowField s 3 + k)

theorem sub_eq (s : ℕ) :
    fi22CentSylowSub s = Subgroup.closure {σ | ∃ k < fi22CentSylowField s 4, gS s k = σ} := by
  unfold gS
  rfl

theorem hP_seeds
    {s : ℕ} (hs : s < 11) : ∀ k < fi22CentSylowField s 4, gS s k ∈ fi22P := by
  obtain ⟨hc, hR, -⟩ := ranges' hs
  intro k hk
  rw [gS]
  exact (fi22H_le hc (memLine hc (hR k hk))).1

theorem hP_wits
    {s : ℕ} (hs : s < 11) : ∀ w < fi22CentSylowField s 7, fi22SylX s w ∈ fi22P := by
  obtain ⟨hc, -, hW⟩ := ranges' hs
  intro w hw
  rw [sylX_eq]
  exact (fi22H_le hc (memLine hc (hW w hw).1)).1

theorem ap_seeds {s : ℕ} (hs : s < 11) :
    ∀ k < fi22CentSylowField s 4, ∀ y : Fin 3510,
      ap (Fi22CentT.L (fi22CentSylowField s 3 + k)) y = (gS s k y : ℕ) := by
  obtain ⟨-, hR, -⟩ := ranges' hs
  intro k hk y
  rw [gS]
  exact ap_line (inR_lt (hR k hk)) y

theorem ap_wits {s : ℕ} (hs : s < 11) :
    ∀ w < fi22CentSylowField s 7, ∀ y : Fin 3510, ap (X s w) y = (fi22SylX s w y : ℕ) := by
  obtain ⟨-, -, hW⟩ := ranges' hs
  intro w hw y
  rw [X_eq, sylX_eq]
  exact ap_line (inR_lt (hW w hw).1) y

theorem card_cover
    {s : ℕ} (hs : s < 11) :
    Nat.card (fi22CentSylowSub s) = fi22CentSylowField s 2 ∧
    (∀ g ∈ fi22CentSylowSub s, g ≠ 1 → g ^ fi22CentSylowField s 1 = 1 →
      ∃ w < fi22CentSylowField s 7, ∃ t ∈ fi22CentSylowSub s, ∃ j, 0 < j ∧
        j < fi22CentSylowField s 1 ∧ g = t * fi22SylX s w ^ j * t⁻¹) := by
  rw [sub_eq]
  exact rec_facts (N := 3510) (L := Fi22CentT.L) (D := CFSG.KD.Syl2072.D) (X := X s)
    (g := gS s) (x := fi22SylX s) (P := fi22P) (by norm_num) (fun G hG h => sepB hG h)
    (hP_seeds hs) (hP_wits hs) (recS_parts hs).1 (ap_seeds hs) (ap_wits hs)

theorem wits
    {s : ℕ} (hs : s < 11) : ∀ w < fi22CentSylowField s 7,
      fi22SylX s w ≠ 1 ∧ fi22SylX s w ^ fi22CentSylowField s 1 = 1 ∧
      fi22SylX s w ∈ fi22H (fi22CentSylowField s 0) ∧
      fi22SylH s w ∈ fi22H (fi22CentSylowField s 0) ∧
      ∃ k, (fi22SylX s w * fi22SylH s w * fi22SylX s w * (fi22SylH s w)⁻¹) ^ k ≠ 1 ∧
        ((fi22SylX s w * fi22SylH s w * fi22SylX s w * (fi22SylH s w)⁻¹) ^ k) ^ 2 = 1 := by
  obtain ⟨hc, -, hW⟩ := ranges' hs
  have hHP : fi22H (fi22CentSylowField s 0) ≤ fi22P := fun _ hg => (fi22H_le hc hg).1
  intro w hw
  rw [sylX_eq, sylH_eq]
  have hxH := memLine hc (hW w hw).1
  have hhH := memLine hc (hW w hw).2
  have hl1 := inR_lt (hW w hw).2
  obtain ⟨hx1, hxp, k, hk1, hk2⟩ := wit_facts (N := 3510) (P := fi22P) (by norm_num)
    (fun G hG h => sepB hG h) (hHP hxH) (hHP hhH) ((recS_parts hs).2 w hw)
    (ap_line (inR_lt (hW w hw).1)) (ap_line hl1) (ap_pinv hl1)
  exact ⟨hx1, hxp, hxH, hhH, k, hk1, hk2⟩

theorem facts
    {s : ℕ} (hs : s < 11) :
    fi22CentSylowSub s ≤ fi22H (fi22CentSylowField s 0) ∧
    Nat.card (fi22CentSylowSub s) = fi22CentSylowField s 2 ∧
    (∀ g ∈ fi22CentSylowSub s, g ≠ 1 → g ^ fi22CentSylowField s 1 = 1 →
      ∃ w < fi22CentSylowField s 7, ∃ t ∈ fi22CentSylowSub s, ∃ j, 0 < j ∧
        j < fi22CentSylowField s 1 ∧ g = t * fi22SylX s w ^ j * t⁻¹) ∧
    (∀ w < fi22CentSylowField s 7,
      fi22SylX s w ≠ 1 ∧ fi22SylX s w ^ fi22CentSylowField s 1 = 1 ∧
      fi22SylX s w ∈ fi22H (fi22CentSylowField s 0) ∧
      fi22SylH s w ∈ fi22H (fi22CentSylowField s 0) ∧
      ∃ k, (fi22SylX s w * fi22SylH s w * fi22SylX s w * (fi22SylH s w)⁻¹) ^ k ≠ 1 ∧
        ((fi22SylX s w * fi22SylH s w * fi22SylX s w * (fi22SylH s w)⁻¹) ^ k) ^ 2 = 1) := by
  obtain ⟨hcard, hcov⟩ := card_cover hs
  exact ⟨seeds_le hs, hcard, hcov, wits hs⟩

open CFSG.Sporadic.FischerOddCore in
theorem facts2072 :
 ∀ s < 11,
    fi22CentSylowSub s ≤ fi22H (fi22CentSylowField s 0) ∧
    Nat.card (fi22CentSylowSub s) = fi22CentSylowField s 2 ∧
    (∀ g ∈ fi22CentSylowSub s, g ≠ 1 → g ^ fi22CentSylowField s 1 = 1 →
      ∃ w < fi22CentSylowField s 7, ∃ t ∈ fi22CentSylowSub s, ∃ j, 0 < j ∧
        j < fi22CentSylowField s 1 ∧ g = t * fi22SylX s w ^ j * t⁻¹) ∧
    (∀ w < fi22CentSylowField s 7,
      fi22SylX s w ≠ 1 ∧ fi22SylX s w ^ fi22CentSylowField s 1 = 1 ∧
      fi22SylX s w ∈ fi22H (fi22CentSylowField s 0) ∧
      fi22SylH s w ∈ fi22H (fi22CentSylowField s 0) ∧
      ∃ k, (fi22SylX s w * fi22SylH s w * fi22SylX s w * (fi22SylH s w)⁻¹) ^ k ≠ 1 ∧
        ((fi22SylX s w * fi22SylH s w * fi22SylX s w * (fi22SylH s w)⁻¹) ^ k) ^ 2 = 1) :=
  fun _ hs => facts hs

end CertificateChecks.KernelSpor.S2072

end

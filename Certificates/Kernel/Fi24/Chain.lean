module

public import Certificates.Kernel.Fi24.Top
public import CFSG.Certificates.Kernel.BindSound
public import CFSG.Certificates.Kernel.Fi24.Data.F1_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F2_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F3_Sel
public import Certificates.Data.Kernel.BindRange
public import CFSG.Certificates.Kernel.Fi24.Data.F4_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F5_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F6_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F7_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F8_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F9_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F10_Sel
public import CFSG.Certificates.Kernel.Fi24.Data.F11_Sel
public import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Fi24.Slices.Bind

public section

namespace CertificateChecks.KernelFi24

open CFSG.KC CFSG.KC.LceS CFSG.KC.Bind CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2
  TauCeti TauCeti.Sporadic

theorem relsEq_spec {CRT PRT : ℕ → ℕ} {R PR Hs : ℕ} (h : relsEq CRT PRT R PR Hs = true) :
    ∀ r < R, ∃ q < PR, CRT r = PRT q := by
  induction R with
  | zero => intro r hr; omega
  | succ n ih =>
    intro r hr
    have h' : andB (relsEq CRT PRT n PR Hs)
      (andB (Nat.blt (hget Hs n) PR) (Nat.beq (CRT n) (PRT (hget Hs n)))) = true := h
    obtain ⟨h1, h2⟩ := KB.andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · exact ih h1 r hr
    · obtain ⟨h3, h4⟩ := KB.andB_true h2
      exact ⟨_, by simpa using h3, Nat.eq_of_beq_eq_true h4⟩

theorem lettersBelow_spec' {W n b : ℕ} (h : HO.lettersBelow W n b = true) : ∀ q < n, wLet W q < b := by
  induction n with
  | zero => intro q hq; omega
  | succ n ih =>
    intro q hq
    have h' : andB (HO.lettersBelow W n b) (Nat.blt (wLet W n) b) = true := h
    obtain ⟨h1, h2⟩ := KB.andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
    · exact ih h1 q hq
    · simpa using h2

theorem relsLet_spec {RT : ℕ → ℕ} {nR : ℕ} (h : BindS.relsLet RT nR = true) :
    ∀ r < nR, wLen (RT r) < 256 ∧ ∀ q < wLen (RT r), wLet (wWord (RT r)) q < 254 := by
  induction nR with
  | zero => intro r hr; omega
  | succ n ih =>
    intro r hr
    have h' : andB (BindS.relsLet RT n) (andB (Nat.blt (wLen (RT n)) (nat_lit 256))
      (HO.lettersBelow (wWord (RT n)) (wLen (RT n)) (nat_lit 254))) = true := h
    obtain ⟨h1, h2⟩ := KB.andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · exact ih h1 r hr
    · obtain ⟨h3, h4⟩ := KB.andB_true h2
      exact ⟨by simpa using h3, lettersBelow_spec' h4⟩

theorem bval_single {G : Type*} [Group G] (gen : ℕ → G) {e g : ℕ} (hl : wLen e = 1)
    (hw : wWord e = 2 * g) (hg : g < 128) : bval gen (wWord e) (wLen e) = gen g := by
  have e1 : 2 * g / 2 ^ (8 * 0) % 256 = 2 * g := by
    rw [Nat.mul_zero, pow_zero, Nat.div_one]
    omega
  rw [hl, hw, bval_succ, show bval gen (2 * g / 256) 0 = 1 from rfl, mul_one, wLet_eq, e1]
  unfold letV
  have e2 : ¬ 2 * g = 255 := by omega
  have e3 : 2 * g % 2 = 0 := by omega
  have e4 : 2 * g / 2 = g := by omega
  simp only [e2, e3, e4, ↓reduceIte]

theorem stmap_hM {G : Type*} [Group G] (pg : ℕ → G) {ST : ℕ → ℕ} {K M : ℕ}
    (hM : Nat.beq M (stMap ST K) = true) (h0 : M ≠ 0) (hK : K ≤ 127) :
    ∀ g < 128, mget M g < 255 → mget M g < 127 ∧
      (fun j => bval pg (wWord (ST j)) (wLen (ST j))) (mget M g) = pg g := by
  intro g hg hm
  obtain ⟨h1, h2, h3⟩ := BindS.stMap_sound (Nat.eq_of_beq_eq_true hM) h0 g hg hm
  exact ⟨by omega, bval_single pg h2 h3 hg⟩

noncomputable abbrev cg2 : ℕ → Fi24AutomorphismGroup :=
  fun j => bval g0 (wWord (CFSG.KD.F1.selST j)) (wLen (CFSG.KD.F1.selST j))
noncomputable abbrev cg3 : ℕ → Fi24AutomorphismGroup :=
  fun j => bval cg2 (wWord (CFSG.KD.F2.selST j)) (wLen (CFSG.KD.F2.selST j))
noncomputable abbrev cg4 : ℕ → Fi24AutomorphismGroup :=
  fun j => bval cg3 (wWord (CFSG.KD.F3.selST j)) (wLen (CFSG.KD.F3.selST j))
noncomputable abbrev cg5 : ℕ → Fi24AutomorphismGroup :=
  fun j => bval cg4 (wWord (CFSG.KD.F4.selST j)) (wLen (CFSG.KD.F4.selST j))
noncomputable abbrev cg6 : ℕ → Fi24AutomorphismGroup :=
  fun j => bval cg5 (wWord (CFSG.KD.F5.selST j)) (wLen (CFSG.KD.F5.selST j))
noncomputable abbrev cg7 : ℕ → Fi24AutomorphismGroup :=
  fun j => bval cg6 (wWord (CFSG.KD.F6.selST j)) (wLen (CFSG.KD.F6.selST j))
noncomputable abbrev cg8 : ℕ → Fi24AutomorphismGroup :=
  fun j => bval cg7 (wWord (CFSG.KD.F7.selST j)) (wLen (CFSG.KD.F7.selST j))
noncomputable abbrev cg9 : ℕ → Fi24AutomorphismGroup :=
  fun j => bval cg8 (wWord (CFSG.KD.F8.selST j)) (wLen (CFSG.KD.F8.selST j))
noncomputable abbrev cg10 : ℕ → Fi24AutomorphismGroup :=
  fun j => bval cg9 (wWord (CFSG.KD.F9.selST j)) (wLen (CFSG.KD.F9.selST j))
noncomputable abbrev cg11 : ℕ → Fi24AutomorphismGroup :=
  fun j => bval cg10 (wWord (CFSG.KD.F10.selST j)) (wLen (CFSG.KD.F10.selST j))

theorem r1 : ∀ r < 80, bval g0 (wWord (CFSG.KD.F1.selRT r)) (wLen (CFSG.KD.F1.selRT r)) = 1 := by
  intro r hr
  obtain ⟨q, hq, e⟩ := relsEq_spec CFSG.KD.Fi24B.bT1 r hr
  rw [e]
  exact top_val hq

theorem r2 : ∀ r < 66, bval cg2 (wWord (CFSG.KD.F2.selRT r)) (wLen (CFSG.KD.F2.selRT r)) = 1 :=
  BindS.relsF_sound g0 cg2 CFSG.KD.Fi24B.bF2 CFSG.KD.Fi24B.bSF
    (fun s hs => by
      change s < 1 at hs
      interval_cases s
      decide)
    (stmap_hM g0 CFSG.KD.Fi24B.bMF1 (by decide) (by decide)) r1 (relsLet_spec (by quickRfl))

theorem r3 : ∀ r < 55, bval cg3 (wWord (CFSG.KD.F3.selRT r)) (wLen (CFSG.KD.F3.selRT r)) = 1 :=
  BindS.relsSub_sound cg2 cg3 CFSG.KD.Fi24B.bF3 (stmap_hM cg2 CFSG.KD.Fi24B.bMF2 (by decide) (by decide))
    r2 (fun r hr => (relsLet_spec (by quickRfl) r hr).2)

theorem r4 : ∀ r < 45, bval cg4 (wWord (CFSG.KD.F4.selRT r)) (wLen (CFSG.KD.F4.selRT r)) = 1 :=
  BindS.relsSub_sound cg3 cg4 CFSG.KD.Fi24B.bF4 (stmap_hM cg3 CFSG.KD.Fi24B.bMF3 (by decide) (by decide))
    r3 (fun r hr => (relsLet_spec (by quickRfl) r hr).2)

theorem r5 : ∀ r < 36, bval cg5 (wWord (CFSG.KD.F5.selRT r)) (wLen (CFSG.KD.F5.selRT r)) = 1 :=
  BindS.relsSub_sound cg4 cg5 CFSG.KD.Fi24B.bF5 (stmap_hM cg4 CFSG.KD.Fi24B.bMF4 (by decide) (by decide))
    r4 (fun r hr => (relsLet_spec (by quickRfl) r hr).2)

theorem r6 : ∀ r < 21, bval cg6 (wWord (CFSG.KD.F6.selRT r)) (wLen (CFSG.KD.F6.selRT r)) = 1 :=
  BindS.relsSub_sound cg5 cg6 CFSG.KD.Fi24B.bF6 (stmap_hM cg5 CFSG.KD.Fi24B.bMF5 (by decide) (by decide))
    r5 (fun r hr => (relsLet_spec (by quickRfl) r hr).2)

theorem r7 : ∀ r < 15, bval cg7 (wWord (CFSG.KD.F7.selRT r)) (wLen (CFSG.KD.F7.selRT r)) = 1 :=
  BindS.relsSub_sound cg6 cg7 CFSG.KD.Fi24B.bF7 (stmap_hM cg6 CFSG.KD.Fi24B.bMF6 (by decide) (by decide))
    r6 (fun r hr => (relsLet_spec (by quickRfl) r hr).2)

theorem r8 : ∀ r < 10, bval cg8 (wWord (CFSG.KD.F8.selRT r)) (wLen (CFSG.KD.F8.selRT r)) = 1 :=
  BindS.relsSub_sound cg7 cg8 CFSG.KD.Fi24B.bF8 (stmap_hM cg7 CFSG.KD.Fi24B.bMF7 (by decide) (by decide))
    r7 (fun r hr => (relsLet_spec (by quickRfl) r hr).2)

theorem r9 : ∀ r < 6, bval cg9 (wWord (CFSG.KD.F9.selRT r)) (wLen (CFSG.KD.F9.selRT r)) = 1 :=
  BindS.relsSub_sound cg8 cg9 CFSG.KD.Fi24B.bF9 (stmap_hM cg8 CFSG.KD.Fi24B.bMF8 (by decide) (by decide))
    r8 (fun r hr => (relsLet_spec (by quickRfl) r hr).2)

theorem r10 : ∀ r < 3, bval cg10 (wWord (CFSG.KD.F10.selRT r)) (wLen (CFSG.KD.F10.selRT r)) = 1 :=
  BindS.relsSub_sound cg9 cg10 CFSG.KD.Fi24B.bF10 (stmap_hM cg9 CFSG.KD.Fi24B.bMF9 (by decide) (by decide))
    r9 (fun r hr => (relsLet_spec (by quickRfl) r hr).2)

theorem r11 : ∀ r < 1, bval cg11 (wWord (CFSG.KD.F11.selRT r)) (wLen (CFSG.KD.F11.selRT r)) = 1 :=
  BindS.relsSub_sound cg10 cg11 CFSG.KD.Fi24B.bF11
    (stmap_hM cg10 CFSG.KD.Fi24B.bMF10 (by decide) (by decide))
    r10 (fun r hr => (relsLet_spec (by quickRfl) r hr).2)

abbrev Tab {G : Type*} [Group G] (gen : ℕ → G) (ST : ℕ → ℕ) (nS L a : ℕ) : Prop :=
  (Subgroup.closure ((fun j => bval gen (wWord (ST j)) (wLen (ST j))) '' {j | j < nS})).relIndex
      (Subgroup.closure (gen '' {g | 2 * g < L})) ≠ 0 ∧
    (Subgroup.closure ((fun j => bval gen (wWord (ST j)) (wLen (ST j))) '' {j | j < nS})).relIndex
      (Subgroup.closure (gen '' {g | 2 * g < L})) ≤ a

end CertificateChecks.KernelFi24

end

module

public import Certificates.Kernel.UnitarySix.Sec3.E3600Chk
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum

theorem loop_of_blocks {LR TR : ℕ → ℕ} {f : List ℕ → Bool} {d B N : ℕ}
    (hc : rcnt (LR 0) = N * B)
    (h : ∀ s < N, allN B (fun j => prodLazyK 693 (693 * 10) LR TR f d 1
      [TR (roff 693 (693 * 10) (LR 0) + (s * B + j))]) = true) :
    prodLazyK 693 (693 * 10) LR TR f (d + 1) 0 [] = true := by
  rw [prodLazyK_succ, hc]
  exact allN_blocks h

@[expose] noncomputable def sIntRun (lo cnt : ℕ) : Bool :=
  strictB (wK wu₂) fun u2 => strictB (pinvS 693 10 (mask 10) u2) fun u2i =>
  strictB (wK wu₁) fun u1 => strictB (pinvS 693 10 (mask 10) u1) fun u1i =>
  strictB (wK ww₀) fun w0 => strictB (pinvS 693 10 (mask 10) w0) fun w0i =>
  allN cnt fun j => prodLazyK 693 (693 * 10) CS.LR CS.TR (sIntL u2 u2i u1 u1i w0 w0i) 2 1
    [CS.TR (roff 693 (693 * 10) (CS.LR 0) + (lo + j))]

@[expose] noncomputable def sIntRun0 (lo cnt : ℕ) : Bool :=
  strictB (wK wu₂) fun u2 => strictB (pinvS 693 10 (mask 10) u2) fun u2i =>
  strictB (wK wu₁) fun u1 => strictB (pinvS 693 10 (mask 10) u1) fun u1i =>
  strictB (wK ww₀) fun w0 => strictB (pinvS 693 10 (mask 10) w0) fun w0i =>
  allN cnt fun j => prodLazyK 693 (693 * 10) CS.LR CS.TR (sIntL u2 u2i u1 u1i w0 w0i) 1 2
    [CS.TR (roff 693 (693 * 10) (CS.LR 1) + (lo + j)), CS.TR (roff 693 (693 * 10) (CS.LR 0) + 0)]

theorem cS_sizes : rcnt (CS.LR 0) = 512 ∧ rcnt (CS.LR 1) = 32 := by decide +kernel

theorem sInt_all (h0 : ∀ s < 8, sIntRun0 (s * 4) 4 = true) (h1 : sIntRun 1 15 = true)
    (h2 : ∀ s < 31, sIntRun (16 + s * 16) 16 = true) :
    prodLazyK 693 (693 * 10) CS.LR CS.TR
      (sIntL (wK wu₂) (wKI wu₂) (wK wu₁) (wKI wu₁) (wK ww₀) (wKI ww₀)) 3 0 [] = true := by
  rw [prodLazyK_succ, cS_sizes.1]
  refine allN_of_forall₀ fun a ha => ?_
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · rw [prodLazyK_succ, cS_sizes.2]
    have hb : (32 : ℕ) = 8 * 4 := rfl
    rw [hb]
    refine allN_blocks fun s hs => ?_
    have := h0 s hs
    unfold sIntRun0 at this
    simp only [strictB_eq₀] at this
    exact this
  · by_cases hlt : a < 16
    · have := h1
      unfold sIntRun at this
      simp only [strictB_eq₀] at this
      have h := allN_spec this (a - 1) (by omega)
      have e : 1 + (a - 1) = a := by omega
      rw [e] at h
      exact h
    · have := h2 (a / 16 - 1) (by omega)
      unfold sIntRun at this
      simp only [strictB_eq₀] at this
      have h := allN_spec this (a % 16) (Nat.mod_lt a (by norm_num))
      have e : 16 + (a / 16 - 1) * 16 + a % 16 = a := by omega
      rw [e] at h
      exact h

@[expose] noncomputable def t2L (p pi q qi r ri : ℕ) (L : List ℕ) : Bool :=
  strictB (prodL 693 10 (mask 10) L) (t2IntK p pi q qi r ri)

@[expose] noncomputable def t2Run (lo cnt : ℕ) : Bool :=
  strictB (wK wab) fun p => strictB (pinvS 693 10 (mask 10) p) fun pi =>
  strictB (wK wba) fun q => strictB (pinvS 693 10 (mask 10) q) fun qi =>
  strictB (wK waba) fun r => strictB (pinvS 693 10 (mask 10) r) fun ri =>
  allN cnt fun j => prodLazyK 693 (693 * 10) CT2.LR CT2.TR (t2L p pi q qi r ri) 1 1
    [CT2.TR (roff 693 (693 * 10) (CT2.LR 0) + (lo + j))]

theorem t2_all (h : ∀ s < 4, t2Run (s * 4) 4 = true) :
    prodLazyK 693 (693 * 10) CT2.LR CT2.TR
      (t2L (wK wab) (wKI wab) (wK wba) (wKI wba) (wK waba) (wKI waba)) 2 0 [] = true :=
  loop_of_blocks (N := 4) (B := 4) (by decide +kernel) fun s hs => by
    have := h s hs
    unfold t2Run at this
    simp only [strictB_eq₀] at this
    exact this

@[expose] noncomputable def t1L (p pi : ℕ) (L : List ℕ) : Bool :=
  strictB (prodL 693 10 (mask 10) L) (t1IntK p pi)

@[expose] noncomputable def t1Run (lo cnt : ℕ) : Bool :=
  strictB (wK wbcb) fun p => strictB (pinvS 693 10 (mask 10) p) fun pi =>
  allN cnt fun j => prodLazyK 693 (693 * 10) CT1.LR CT1.TR (t1L p pi) 1 1
    [CT1.TR (roff 693 (693 * 10) (CT1.LR 0) + (lo + j))]

theorem t1_all (h : ∀ s < 2, t1Run (s * 16) 16 = true) :
    prodLazyK 693 (693 * 10) CT1.LR CT1.TR (t1L (wK wbcb) (wKI wbcb)) 2 0 [] = true :=
  loop_of_blocks (N := 2) (B := 16) (by decide +kernel) fun s hs => by
    have := h s hs
    unfold t1Run at this
    simp only [strictB_eq₀] at this
    exact this

@[expose] noncomputable def ka1L (L : List ℕ) : Bool := strictB (prodL 693 10 (mask 10) L) ka1K

@[expose] noncomputable def ka1Run (lo cnt : ℕ) : Bool :=
  allN cnt fun j => prodLazyK 693 (693 * 10) CA1.LR CA1.TR ka1L 0 1
    [CA1.TR (roff 693 (693 * 10) (CA1.LR 0) + (lo + j))]

theorem ka1_all (h : ∀ s < 4, ka1Run (s * 128) 128 = true) :
    prodLazyK 693 (693 * 10) CA1.LR CA1.TR ka1L 1 0 [] = true :=
  loop_of_blocks (N := 4) (B := 128) (by decide +kernel) h

@[expose] noncomputable def ka2L (u2 u2i : ℕ) (L : List ℕ) : Bool :=
  strictB (prodL 693 10 (mask 10) L) (ka2K u2 u2i)

@[expose] noncomputable def ka2Run (lo cnt : ℕ) : Bool :=
  strictB (wK wu₂) fun u2 => strictB (pinvS 693 10 (mask 10) u2) fun u2i =>
  allN cnt fun j => prodLazyK 693 (693 * 10) CA2.LR CA2.TR (ka2L u2 u2i) 2 1
    [CA2.TR (roff 693 (693 * 10) (CA2.LR 0) + (lo + j))]

theorem ka2_all (h : ∀ s < 16, ka2Run (s * 2) 2 = true) :
    prodLazyK 693 (693 * 10) CA2.LR CA2.TR (ka2L (wK wu₂) (wKI wu₂)) 3 0 [] = true :=
  loop_of_blocks (N := 16) (B := 2) (by decide +kernel) fun s hs => by
    have := h s hs
    unfold ka2Run at this
    simp only [strictB_eq₀] at this
    exact this

@[expose] noncomputable def normRun (lo cnt : ℕ) : Bool :=
  allN cnt fun j => prodLazyK 693 (693 * 10) CK1.LR CK1.TR normL 2 1
    [CK1.TR (roff 693 (693 * 10) (CK1.LR 0) + (lo + j))]

theorem norm_all (h : ∀ s < 30, normRun (s * 4) 4 = true) :
    prodLazyK 693 (693 * 10) CK1.LR CK1.TR normL 3 0 [] = true :=
  loop_of_blocks (N := 30) (B := 4) (by decide +kernel) h

end CertificateChecks.KernelU6.Sec3

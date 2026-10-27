module

public import Certificates.Data.D4HexLineChar
public import Certificates.Kernel.S63K.KChecks
public import Certificates.Kernel.S63K.L4234
public import CFSG.Certificates.Kernel.S63K.SortSound

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelS63.K4239

open CFSG.D4Hex CFSG.LargeExtraspecial.S63 CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.KC.Enum CFSG.KS
  CFSG.KS.SporSch.M24 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CertificateChecks.KernelS63
  CertificateChecks.KernelS63.HD CertificateChecks.KernelS63.GD

theorem el {x : ℕ} (hx : x < 819) : (ElG ID.ZP 819)[x]! = unpackR 24 (ID.ZP x) := elG_get hx

theorem klein : lineKleinOK (ElG ID.ZP 819) = true := by
  unfold lineKleinOK
  rw [allLt_iff]
  intro l hl
  obtain ⟨p1, p2, p3⟩ := G4235.pts_parts l hl
  have h := MatL.allN_iff.1 KK.ch4239L l hl
  unfold KK.kleinAt at h
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
  rw [L4234.lnPt0, L4234.lnPt1, L4234.lnPt2, el (x := LTf (3 * l)) (by omega),
    el (x := LTf (3 * l + 1)) (by omega), el (x := LTf (3 * l + 2)) p3, mulR_unpackR,
    mulR_unpackR, beq_unpackR, beq_unpackR]
  simp only [Bool.and_eq_true]
  exact ⟨h.1, h.2⟩

theorem hP : ∀ i < 819, ID.ZP i < 2 ^ 576 := (bfsDistK_sound I21111.zdist).1

theorem kline : kleinLineOK (CkG ID.ZP LK.PAR LK.LAB 819) = true := by
  unfold kleinLineOK
  simp only [CkG]
  rw [allLt_iff]
  intro q hq
  have h := MatL.allN_iff.1 KK.ch4239Q q hq
  unfold KK.klAt at h
  rcases rec_true h with ⟨h0, -⟩ | ⟨h0, h1⟩
  · obtain rfl : q = 0 := Nat.eq_of_beq_eq_true h0
    simp
  rw [el (x := 0) (by norm_num), el hq, mulR_unpackR, mulR_unpackR, beq_unpackR]
  simp only [MatL.strictB_eq] at h1
  rcases rec_true h1 with ⟨hb, h2⟩ | ⟨hb, -⟩
  · have hb' : Nat.beq (CFSG.KC.F2W.mulW 24 (ID.ZP 0) (ID.ZP q) % 2 ^ 576)
        (CFSG.KC.F2W.mulW 24 (ID.ZP q) (ID.ZP 0) % 2 ^ 576) = true := hb
    rw [hb']
    rcases rec_true h2 with ⟨hm, -⟩ | ⟨-, h3⟩
    · have hz := memS_zero I21111.zdist (Nat.eq_of_beq_eq_true hm)
      have hmem : memR (ElG ID.ZP 819) (lookup (mkIdx (ElG ID.ZP 819)))
          (unpackR 24 (CFSG.KC.F2W.mulW 24 (ID.ZP 0) (ID.ZP q))) = false := by
        rw [Bool.eq_false_iff]
        intro hm'
        unfold memR at hm'
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm'
        obtain ⟨hk, he⟩ := hm'
        have hk' : lookup (mkIdx (ElG ID.ZP 819))
            (unpackR 24 (CFSG.KC.F2W.mulW 24 (ID.ZP 0) (ID.ZP q))) < 819 := by
          simpa [ElG] using hk
        rw [el hk', unpackR_inj, Nat.mod_eq_of_lt (hP _ hk')] at he
        exact hz _ hk' he
      rw [hmem]
      simp
    · simp only [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h3
      obtain ⟨hr, hzr, hany⟩ := h3
      generalize ID.ZS (CFSG.KC.S63K.bsK ID.ZP ID.ZS
        (Nat.mod (CFSG.KC.F2W.mulW 24 (ID.ZP 0) (ID.ZP q)) (2 ^ 576)) 32 0 819) = r at hr hzr hany
      have hzr' : ID.ZP r = CFSG.KC.F2W.mulW 24 (ID.ZP 0) (ID.ZP q) % 2 ^ 576 :=
        Nat.eq_of_beq_eq_true hzr
      have hidx : lookup (mkIdx (ElG ID.ZP 819))
          (unpackR 24 (CFSG.KC.F2W.mulW 24 (ID.ZP 0) (ID.ZP q))) = r := by
        rw [unpackR_mod, ← hzr', idx_of_C L4234.hK hr]
      have hmem : memR (ElG ID.ZP 819) (lookup (mkIdx (ElG ID.ZP 819)))
          (unpackR 24 (CFSG.KC.F2W.mulW 24 (ID.ZP 0) (ID.ZP q))) = true := by
        unfold memR
        rw [hidx, el hr, unpackR_mod (CFSG.KC.F2W.mulW 24 (ID.ZP 0) (ID.ZP q)), ← hzr']
        simp [ElG, hr]
      rw [hmem, hidx]
      obtain ⟨k, hk, hl⟩ := List.any_eq_true.1 hany
      have hk9 := List.mem_range.1 hk
      have hlt : KK.pl0 k < 2457 := by
        have := (G4235.inc_parts.1 0 (by norm_num) k hk9).1
        rw [Nat.mul_zero, Nat.zero_add] at this
        exact this
      unfold KK.lineIs at hl
      simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hl
      simp only [Bool.or_eq_true]
      right
      refine List.any_eq_true.2 ⟨KK.pl0 k, List.mem_range.2 hlt, ?_⟩
      rw [L4234.lnPt0, L4234.lnPt1, L4234.lnPt2]
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨hl.1, hl.2.1⟩, hl.2.2⟩
  · have hb' : Nat.beq (CFSG.KC.F2W.mulW 24 (ID.ZP 0) (ID.ZP q) % 2 ^ 576)
        (CFSG.KC.F2W.mulW 24 (ID.ZP q) (ID.ZP 0) % 2 ^ 576) = false := hb
    rw [hb']
    simp

open Certificates in
theorem c4239 : CFSG.D4Hex.lineCharCheck = true := by
  unfold lineCharCheck lineCharOn
  rw [L4234.cz_eq, Bool.and_eq_true]
  exact ⟨klein, kline⟩

end CertificateChecks.KernelS63.K4239

end


module

public import Certificates.Kernel.Sporadic.Fi24Ext.Links
import Certificates.Kernel.Sporadic.Fi24Ext.F0
import Certificates.Kernel.Sporadic.Fi24Ext.F1
import Certificates.Kernel.Sporadic.Fi24Ext.F2
import Certificates.Kernel.Sporadic.Fi24Ext.F3
import Certificates.Kernel.Sporadic.Fi24Ext.RQ
import Certificates.Kernel.Sporadic.Fi24Ext.Seeds
import Certificates.Kernel.Sporadic.Fi24Fix.Init

public section

namespace CertificateChecks.KernelFi24Ext

open CFSG.KC.Ord CFSG.KS.Mat3 CFSG.KD.Fi24Ext CFSG.KC.Fi24Ext CFSG.KC.Fi24ExtS
  CFSG.Sporadic.Fi24.Native CertificateChecks.KernelSpor.Fi24Rels

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local irreducible] CFSG.KD.Fi24Ext.MX CFSG.KD.BrFi24.MT CFSG.KD.Fi24Fix.MX
  CFSG.KD.Fi24Ext.M3 CFSG.KD.BrFi24.ONE

theorem LO_eq : CFSG.KD.BrFi24.LO = 2 ^ 609961 - 1 := pow_sub_one_eq 609961

theorem lo_testBit (X p : ℕ) (hp : p < 609961) :
    (Nat.land X CFSG.KD.BrFi24.LO).testBit p = X.testBit p := by
  change (X &&& CFSG.KD.BrFi24.LO).testBit p = _
  rw [Nat.testBit_and, LO_eq, Nat.testBit_two_pow_sub_one]
  simp [hp]

theorem hi_testBit (X p : ℕ) : (Nat.shiftRight X 609961).testBit p = X.testBit (609961 + p) := by
  change (X >>> 609961).testBit p = _
  rw [Nat.testBit_shiftRight]

theorem bv_val (v : ℕ) (hv : v < 3) : bv (decide (v = 1)) (decide (v = 2)) = (v : ZMod 3) :=
  CFSG.KC.Fi24FixS.bv_trit v hv

theorem mt_dig {X : ℕ} {CT : ℕ → ℕ} {c0 w r : ℕ} {id : Bool}
    (hrows : ∀ i < r, ∀ j < 781,
      (Nat.land X CFSG.KD.BrFi24.LO).testBit (781 * i + j) = decide (digV CT c0 w id i j = 1) ∧
        (Nat.shiftRight X 609961).testBit (781 * i + j) = decide (digV CT c0 w id i j = 2))
    (hzero : ∀ i, r ≤ i → i < 781 → ∀ j < 781,
      (Nat.land X CFSG.KD.BrFi24.LO).testBit (781 * i + j) = false ∧
        (Nat.shiftRight X 609961).testBit (781 * i + j) = false)
    (i j : Fin 781) :
    Mt X i j = if i.val < r then ((digV CT c0 w id i.val j.val : ℕ) : ZMod 3) else 0 := by
  have hp : 781 * i.val + j.val < 609961 := by omega
  change bv (X.testBit (781 * i.val + j.val)) (X.testBit (609961 + (781 * i.val + j.val))) = _
  rw [← lo_testBit X _ hp, ← hi_testBit]
  by_cases hi : i.val < r
  · obtain ⟨a, b⟩ := hrows i.val hi j.val j.isLt
    rw [a, b, if_pos hi]
    apply bv_val
    rw [digV_eq]
    split_ifs <;> omega
  · obtain ⟨a, b⟩ := hzero i.val (by omega) i.isLt j.val j.isLt
    rw [a, b, if_neg hi]
    rfl

theorem dig_entry {s : String} {cs : List Char} {CT : ℕ → ℕ} {len t : ℕ} (hcs : s = String.ofList cs)
    (hd : CFSG.KC.Fi24FixK.digitsOK CT len cs 0 = true) (ht : t / 4 < cs.length) :
    (decode81 s)[t]?.getD 0 = CT (t / 4) / 3 ^ (t % 4) % 3 := by
  obtain ⟨-, hCT⟩ := CFSG.KC.Fi24FixS.digitsOK_spec cs 0 hd
  simp only [Nat.zero_add] at hCT
  have e : t = 4 * (t / 4) + t % 4 := by omega
  rw [Array.getElem?_toList.symm.trans rfl, CFSG.KC.Fi24FixS.decode81_toList, hcs,
    String.toList_ofList, e, CFSG.KC.Fi24FixS.flatMap_dig4 cs _ _ ht (Nat.mod_lt _ (by norm_num)),
    Option.getD_some, ← e, hCT _ ht]

theorem FA_len : FA.chars.length = 152491 := by
  have := (CFSG.KC.Fi24FixS.digitsOK_spec FA.chars 0 form_digits).1
  rw [Nat.zero_add] at this
  exact this

theorem QA_len : QA.chars.length = 16003 := by
  have := (CFSG.KC.Fi24FixS.digitsOK_spec QA.chars 0 basis_digits).1
  rw [Nat.zero_add] at this
  exact this

theorem IA_len : CFSG.KD.Fi24Fix.IA.chars.length = 33396 := by
  have := (CFSG.KC.Fi24FixS.digitsOK_spec CFSG.KD.Fi24Fix.IA.chars 0 CFSG.KD.Fi24Fix.init_digits).1
  rw [Nat.zero_add] at this
  exact this

theorem f0' : digRowsOK (Nat.land F CFSG.KD.BrFi24.LO) (Nat.shiftRight F 609961) CTF 0 781 false
    0 196 4 = true := f0
theorem f1' : digRowsOK (Nat.land F CFSG.KD.BrFi24.LO) (Nat.shiftRight F 609961) CTF 0 781 false
    196 196 4 = true := f1
theorem f2' : digRowsOK (Nat.land F CFSG.KD.BrFi24.LO) (Nat.shiftRight F 609961) CTF 0 781 false
    392 196 4 = true := f2
theorem f3' : digRowsOK (Nat.land F CFSG.KD.BrFi24.LO) (Nat.shiftRight F 609961) CTF 0 781 false
    588 193 4 = true := f3
theorem rr' : digRowsOK (Nat.land Rr CFSG.KD.BrFi24.LO) (Nat.shiftRight Rr 609961)
    CFSG.KD.Fi24Fix.CT 253 528 true 0 253 4 = true := rr
theorem rz' : zeroFromOK (Nat.land Rr CFSG.KD.BrFi24.LO) (Nat.shiftRight Rr 609961) 253 = true := rz
theorem qd' : digRowsOK (Nat.land Q CFSG.KD.BrFi24.LO) (Nat.shiftRight Q 609961) CTQ 0 253 false
    0 253 4 = true := qd
theorem qz' : zeroFromOK (Nat.land Q CFSG.KD.BrFi24.LO) (Nat.shiftRight Q 609961) 253 = true := qz

theorem digRows_join {X : ℕ} {CT : ℕ → ℕ} {c0 w : ℕ} {id : Bool}
    (h0 : digRowsOK (Nat.land X CFSG.KD.BrFi24.LO) (Nat.shiftRight X 609961) CT c0 w id 0 196 4 = true)
    (h1 : digRowsOK (Nat.land X CFSG.KD.BrFi24.LO) (Nat.shiftRight X 609961) CT c0 w id 196 196 4 = true)
    (h2 : digRowsOK (Nat.land X CFSG.KD.BrFi24.LO) (Nat.shiftRight X 609961) CT c0 w id 392 196 4 = true)
    (h3 : digRowsOK (Nat.land X CFSG.KD.BrFi24.LO) (Nat.shiftRight X 609961) CT c0 w id 588 193 4 = true) :
    ∀ i < 781, ∀ j < 781,
      (Nat.land X CFSG.KD.BrFi24.LO).testBit (781 * i + j) = decide (digV CT c0 w id i j = 1) ∧
        (Nat.shiftRight X 609961).testBit (781 * i + j) = decide (digV CT c0 w id i j = 2) := by
  intro i hi
  rcases Nat.lt_or_ge i 196 with a | a
  · exact digRowsOK_spec h0 (by norm_num) i (by omega) (by omega)
  rcases Nat.lt_or_ge i 392 with b | b
  · exact digRowsOK_spec h1 (by norm_num) i a (by omega)
  rcases Nat.lt_or_ge i 588 with c | c
  · exact digRowsOK_spec h2 (by norm_num) i b (by omega)
  · exact digRowsOK_spec h3 (by norm_num) i c (by omega)

theorem F_mt : Mt F = matW 781 781 (matF ()) := by
  ext i j
  rw [mt_dig (r := 781) (digRows_join f0' f1' f2' f3') (fun i h1 h2 => absurd h2 (by omega)),
    if_pos i.isLt, matW_apply, rowW_matF_val i.isLt j.isLt, digV_eq, if_neg (by omega),
    if_pos (by omega), Nat.sub_zero,
    dig_entry FA.eq form_digits (by rw [FA_len]; omega)]

theorem Rr_mt : Mt Rr = matW 781 781 (initRows ()) := by
  ext i j
  rw [mt_dig (r := 253) (fun i hi => digRowsOK_spec rr' (by norm_num) i (Nat.zero_le _) (by omega))
    (fun i h1 h2 j hj => zeroFromOK_spec rz' _ (by omega)), matW_apply]
  by_cases hi : i.val < 253
  · rw [if_pos hi, CFSG.KC.Fi24FixS.rowW_initRows_val hi j.isLt, digV_eq]
    by_cases hj : j.val < 253
    · rw [if_pos hj, if_pos hj]
      by_cases e : i.val = j.val
      · rw [if_pos ⟨rfl, e⟩, if_pos e.symm]
      · rw [if_neg (fun h => e h.2), if_neg (Ne.symm e)]
    · rw [if_neg hj, if_neg hj, if_pos (by omega)]
      rw [dig_entry CFSG.KD.Fi24Fix.IA.eq CFSG.KD.Fi24Fix.init_digits (by rw [IA_len]; omega)]
  · rw [if_neg hi, CFSG.Sporadic.Fi24.Native.zeroFrom_initRows_rows _ (by omega)]

theorem Q_mt : Mt Q = matW 781 781 (basisRows ()) := by
  ext i j
  rw [mt_dig (r := 253) (fun i hi => digRowsOK_spec qd' (by norm_num) i (Nat.zero_le _) (by omega))
    (fun i h1 h2 j hj => zeroFromOK_spec qz' _ (by omega)), matW_apply]
  by_cases hi : i.val < 253
  · rw [if_pos hi, rowW_basisRows_val hi, digV_eq, if_neg (by omega)]
    by_cases hj : j.val < 253
    · rw [if_pos hj, if_pos (by omega), Nat.sub_zero,
        dig_entry QA.eq basis_digits (by rw [QA_len]; omega)]
    · rw [if_neg hj, if_neg (by omega)]; rfl
  · rw [if_neg hi, rowW_ge (by rw [basisRows_size]; omega), W.val_zero]

theorem Rt_mt : Mt CFSG.KD.Fi24Fix.R = (matW 781 781 (initRows ())).transpose := by
  obtain ⟨hlen, hCT⟩ := CFSG.KC.Fi24FixS.digitsOK_spec _ 0 CFSG.KD.Fi24Fix.init_digits
  simp only [Nat.zero_add] at hlen hCT
  have hcol := CFSG.KC.Fi24FixS.colsOK_spec CFSG.KD.Fi24Fix.init_cols
  have hrow := CFSG.KC.Fi24FixS.rowsZOK_spec CFSG.KD.Fi24Fix.init_rows
  ext j i
  rw [Matrix.transpose_apply, matW_apply]
  have hp : 781 * j.val + i.val < 609961 := by omega
  change bv (CFSG.KD.Fi24Fix.R.testBit (781 * j.val + i.val))
    (CFSG.KD.Fi24Fix.R.testBit (609961 + (781 * j.val + i.val))) = _
  rw [← lo_testBit _ _ hp, ← hi_testBit]
  change bv ((Nat.land CFSG.KD.Fi24Fix.R CFSG.KD.BrFi24.LO).testBit _)
    ((Nat.shiftRight CFSG.KD.Fi24Fix.R 609961).testBit _) = _
  change bv (CFSG.KD.Fi24Fix.R1.testBit _) (CFSG.KD.Fi24Fix.R2.testBit _) = _
  by_cases hi : i.val < 253
  · rw [CFSG.KC.Fi24FixS.rowW_initRows_val hi j.isLt]
    by_cases hj : j.val < 253
    · obtain ⟨a, b⟩ := (hrow j j.isLt i i.isLt).1 hj
      rw [a, b, if_pos hj]
      by_cases e : i.val = j.val
      · simp [e, bv]
      · simp [e, Ne.symm e, bv]
    · rw [if_neg hj]
      have hj' : j.val - 253 < 528 := by omega
      obtain ⟨a, b⟩ := hcol (j.val - 253) hj' i hi
      have e1 : 781 * (253 + (j.val - 253)) + i.val = 781 * j.val + i.val := by omega
      rw [e1] at a b
      have e2 : (528 * i.val + (j.val - 253)) / 4 = 132 * i.val + (j.val - 253) / 4 := by omega
      have e3 : (528 * i.val + (j.val - 253)) % 4 = (j.val - 253) % 4 := by omega
      rw [a, b, bv_val _ (Nat.mod_lt _ (by norm_num)),
        dig_entry CFSG.KD.Fi24Fix.IA.eq CFSG.KD.Fi24Fix.init_digits (by rw [IA_len]; omega), e2, e3]
  · rw [CFSG.Sporadic.Fi24.Native.zeroFrom_initRows_rows _ (by omega)]
    by_cases hj : j.val < 253
    · obtain ⟨a, b⟩ := (hrow j j.isLt i i.isLt).1 hj
      have e : i.val ≠ j.val := by omega
      rw [a, b]
      simp [e, bv]
    · obtain ⟨a, b⟩ := (hrow j j.isLt i i.isLt).2 (by omega) (by omega)
      rw [a, b]
      rfl

theorem consts253 : consts3OK 253 9 64009 LO3 RM3 CI3 ONE3 UP3 = true := consts3

theorem E253_mt : Mt E253 = pad 1 := by
  ext i j
  change mat3 781 609961 E253 i j = _
  rw [mat3_pad e253, (one3_sound consts253).2]
  rfl

theorem Y0_mt : Mt Y0 = matW 781 781 (rowsOfSeed 253 CFSG.Sporadic.Fi23.Native.seedA) := by
  have h := seed3_sound1 d1 d1_end consts253
    (CFSG.KS.Bytes.bytesEqK_of_runF (by decide) CFSG.KD.BrFi23.seed1_run) (by decide +kernel)
  rw [pw_pad (rowsOfSeed_size' 253 _) (zeroFrom_rowsOfSeed 253 (by norm_num) _),
    matW_rowsOfSeed' 253 (by norm_num), CFSG.KD.BrFi23.Fi23SeedA.eq, h]
  ext i j
  change mat3 781 609961 Y0 i j = _
  rw [mat3_pad y0pad]
  rfl

theorem Y1_mt : Mt Y1 = matW 781 781 (rowsOfSeed 253 CFSG.Sporadic.Fi23.Native.seedB) := by
  have h := seed3_sound1 d2 d2_end consts253
    (CFSG.KS.Bytes.bytesEqK_of_runF (by decide) CFSG.KD.BrFi23.seed2_run) (by decide +kernel)
  rw [pw_pad (rowsOfSeed_size' 253 _) (zeroFrom_rowsOfSeed 253 (by norm_num) _),
    matW_rowsOfSeed' 253 (by norm_num), CFSG.KD.BrFi23.Fi23SeedB.eq, h]
  ext i j
  change mat3 781 609961 Y1 i j = _
  rw [mat3_pad y1pad]
  rfl

theorem A_mt : Mt (CFSG.KD.BrFi24.RB 23) = matW 781 781 (matA ()) := by
  rw [CFSG.Sporadic.Fi24.matW_matA]
  exact mA_eq.symm

theorem B_mt : Mt (CFSG.KD.BrFi24.RB 24) = matW 781 781 (matB ()) := by
  rw [CFSG.Sporadic.Fi24.matW_matB]
  exact mB_eq.symm

end CertificateChecks.KernelFi24Ext

end

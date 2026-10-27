module

public import Certificates.Kernel.M12Cover.T25P
public import CFSG.Certificates.Kernel.M12DecSound
public import CFSG.Certificates.Kernel.M12TransGen
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Data.List.Nodup

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelM12T

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.M12Dec CFSG.KC.M12Trans
open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.M12Cover.InternalSylow

theorem parArr_eq : parArr = unpack 1485 12 PAR := by
  unfold parArr
  rw [SPar.eq]
  exact decodeB64_sound (by quickRfl)

theorem letArr_eq : letArr = unpack 1485 6 LET := by
  unfold letArr
  rw [SLet.eq]
  exact decodeB64_sound (by quickRfl)

theorem act1Arr_eq : act1Arr = unpack 1485 12 AC1 := by
  unfold act1Arr
  rw [SAc1.eq]
  exact decodeB64_sound (by quickRfl)

theorem act2Arr_eq : act2Arr = unpack 1485 12 AC2 := by
  unfold act2Arr
  rw [SAc2.eq]
  exact decodeB64_sound (by quickRfl)

theorem wit1Arr_eq : wit1Arr = unpack 1485 6 WI1 := by
  unfold wit1Arr
  rw [SWi1.eq]
  exact decodeB64_sound (by quickRfl)

theorem wit2Arr_eq : wit2Arr = unpack 1485 6 WI2 := by
  unfold wit2Arr
  rw [SWi2.eq]
  exact decodeB64_sound (by quickRfl)

theorem aArr_eq : aArr = unpack 1485 6 AA := by
  unfold aArr
  rw [SA.eq]
  exact decodeB64_sound (by quickRfl)

theorem sigArr_eq : sigArr = unpack 1485 12 SIG := by
  unfold sigArr
  rw [SSig.eq]
  exact decodeB64_sound (by quickRfl)

theorem pArr_eq : pArr = unpack 95040 6 PP := by
  unfold pArr
  rw [SP.eq]
  exact decodeB64_sound (by quickRfl)

theorem ihArr_eq : ihArr = unpack 95040 12 IH := by
  unfold ihArr
  rw [SIh.eq]
  exact decodeB64_sound (by quickRfl)

theorem kPAR : Nat.beq (Nat.shiftRight PAR (1485 * 12)) 0 = true := by quickRfl
theorem kLET : Nat.beq (Nat.shiftRight LET (1485 * 6)) 0 = true := by quickRfl
theorem kAC1 : Nat.beq (Nat.shiftRight AC1 (1485 * 12)) 0 = true := by quickRfl
theorem kAC2 : Nat.beq (Nat.shiftRight AC2 (1485 * 12)) 0 = true := by quickRfl
theorem kWI1 : Nat.beq (Nat.shiftRight WI1 (1485 * 6)) 0 = true := by quickRfl
theorem kWI2 : Nat.beq (Nat.shiftRight WI2 (1485 * 6)) 0 = true := by quickRfl
theorem kAA : Nat.beq (Nat.shiftRight AA (1485 * 6)) 0 = true := by quickRfl
theorem kSIG : Nat.beq (Nat.shiftRight SIG (1485 * 12)) 0 = true := by quickRfl
theorem kPP : Nat.beq (Nat.shiftRight PP (95040 * 6)) 0 = true := by quickRfl
theorem kIH : Nat.beq (Nat.shiftRight IH (95040 * 12)) 0 = true := by quickRfl
theorem kRCP : Nat.beq (Nat.shiftRight RCP (17820 * 4)) 0 = true := by quickRfl
theorem kSGI : allN 1485 (fun i => Nat.beq (pg 12 (mask 12) SGI (pg 12 (mask 12) SIG i)) i) = true := by
  quickRfl

@[expose] noncomputable def tpK (i : Nat) : Nat := pg 12 (mask 12) PAR i

@[expose] noncomputable def tlK (i : Nat) : Nat := pg 6 (mask 6) LET i

@[expose] noncomputable def taK (l i : Nat) : Nat :=
  nIf(Nat.beq l 1, pg 12 (mask 12) AC1 i, pg 12 (mask 12) AC2 i)

@[expose] noncomputable def twK (l i : Nat) : Nat :=
  nIf(Nat.beq l 1, pg 6 (mask 6) WI1 i, pg 6 (mask 6) WI2 i)

@[expose] noncomputable def aiK (i : Nat) : Nat := pg 6 (mask 6) AA i

@[expose] noncomputable def sgK (i : Nat) : Nat := pg 12 (mask 12) SIG i

@[expose] noncomputable def ppK (i h : Nat) : Nat :=
  nIf(Nat.blt h 64, pg 6 (mask 6) (rowsOf 6 PP i) h, pg 6 (mask 6) PP (64 * i + h))

@[expose] noncomputable def ihK (i h : Nat) : Nat :=
  nIf(Nat.blt h 64, pg 12 (mask 12) (rowsOf 12 IH i) h, pg 12 (mask 12) IH (64 * i + h))

@[expose] noncomputable def rcK (k : Nat) : Nat := pg 4 (mask 4) RCP k

theorem tpar_eq : tpar = tpK := funext fun i => by
  unfold tpar
  rw [parArr_eq, unpack_get kPAR]
  rfl

theorem tlet_eq : tlet = tlK := funext fun i => by
  unfold tlet
  rw [letArr_eq, unpack_get kLET]
  rfl

theorem tact_eq : tact = taK := funext fun l => funext fun i => by
  unfold tact taK
  by_cases hl : l = 1
  · subst hl
    rw [ite_eq_left rfl, act1Arr_eq, unpack_get kAC1]
    rfl
  · have hb : Nat.beq l 1 = false := Bool.eq_false_iff.2 fun h => hl (Nat.eq_of_beq_eq_true h)
    rw [ite_eq_right hl, act2Arr_eq, unpack_get kAC2, hb]

theorem twit_eq : twit = twK := funext fun l => funext fun i => by
  unfold twit twK
  by_cases hl : l = 1
  · subst hl
    rw [ite_eq_left rfl, wit1Arr_eq, unpack_get kWI1]
    rfl
  · have hb : Nat.beq l 1 = false := Bool.eq_false_iff.2 fun h => hl (Nat.eq_of_beq_eq_true h)
    rw [ite_eq_right hl, wit2Arr_eq, unpack_get kWI2, hb]

theorem taIdx_eq : taIdx = aiK := funext fun i => by
  unfold taIdx
  rw [aArr_eq, unpack_get kAA]
  rfl

theorem tsig_eq : tsig = sgK := funext fun i => by
  unfold tsig
  rw [sigArr_eq, unpack_get kSIG]
  rfl

theorem nodup_sig : ((List.range 1485).map sgK).Nodup := by
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro x hx y hy hxy
  have e1 := Nat.eq_of_beq_eq_true (allN_spec kSGI x (List.mem_range.1 hx))
  have e2 := Nat.eq_of_beq_eq_true (allN_spec kSGI y (List.mem_range.1 hy))
  unfold sgK at hxy
  rw [← e1, ← e2, hxy]

theorem tp_eq : tp = ppK := funext fun i => funext fun h => by
  unfold tp ppK
  rw [pArr_eq, unpack_get kPP]
  by_cases hh : h < 64
  · have hb : Nat.blt h 64 = true := Nat.ble_eq_true_of_le hh
    rw [hb]
    refine (pg_sub ?_ ?_).symm
    · change 64 * 6 * i + 6 * h = 6 * (64 * i + h)
      omega
    · change 6 * h + 6 ≤ 64 * 6
      omega
  · have hb : Nat.blt h 64 = false := Bool.eq_false_iff.2 fun h' => hh (Nat.le_of_ble_eq_true h')
    rw [hb]

theorem tih_eq : tih = ihK := funext fun i => funext fun h => by
  unfold tih ihK
  rw [ihArr_eq, unpack_get kIH]
  by_cases hh : h < 64
  · have hb : Nat.blt h 64 = true := Nat.ble_eq_true_of_le hh
    rw [hb]
    refine (pg_sub ?_ ?_).symm
    · change 64 * 12 * i + 12 * h = 12 * (64 * i + h)
      omega
    · change 12 * h + 12 ≤ 64 * 12
      omega
  · have hb : Nat.blt h 64 = false := Bool.eq_false_iff.2 fun h' => hh (Nat.le_of_ble_eq_true h')
    rw [hb]

theorem r0_eq : r0CodeAux 1485 = r0K tpK tlK letterCode 1485 := funext fun i => funext fun p => by
  rw [r0CodeAux_eq, tpar_eq, tlet_eq]

theorem r0β_eq : r0βCodeAux 1485 = r0K tpK tlK letterCodeβ 1485 := funext fun i => funext fun p => by
  rw [r0βCodeAux_eq, tpar_eq, tlet_eq]

theorem rCodeArr_get (k : Nat) (hk : k < 17820) : rCodeArr[k]! = rCode (k / 12) (k % 12) := by
  unfold rCodeArr
  rw [getElem!_pos _ k (by simp; omega)]
  simp

theorem rCodeArr_size : rCodeArr.size = 17820 := by
  unfold rCodeArr
  simp

@[expose] noncomputable def fRC (k : Nat) : Bool :=
  Nat.beq (rcK k) (rCodeG (r0K tpK tlK letterCode 1485) (k / 12) (k % 12))

#lc_blocks RCB fRC 17820 256

theorem rc_eq : (fun k => rCodeArr[k]!) = rcK := funext fun k => by
  by_cases hk : k < 17820
  · rw [rCodeArr_get k hk, rCode_eq, r0_eq]
    exact (Nat.eq_of_beq_eq_true
      (CFSG.KC.Co3Bfs.cover_of_blocks (by decide) (by decide) RCB.all k hk)).symm
  · rw [getElem!_neg _ k (by rw [rCodeArr_size]; exact hk)]
    have h := unpack_get (i := k) kRCP
    rw [getElem!_neg _ k (by unfold unpack; rw [Array.size_ofFn]; exact hk)] at h
    exact h

end CertificateChecks.KernelM12T

end

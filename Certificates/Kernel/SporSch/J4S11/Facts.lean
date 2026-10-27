module

public import Certificates.Kernel.SporSch.J4S11.Checks
public import Certificates.Kernel.SporSch.J4S.Regs
public import CFSG.Certificates.Kernel.SporSch.J4S11Sound
public import CFSG.Sporadic.Schreier.J4SElevenData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4E7

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.KS.SporSch.J4E
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native

theorem hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6 := CertificateChecks.KernelJ4Q.hK

theorem eqP_eq {p q : Nat × Nat} (h : eqP p q = true) : p = q := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  have h' : andB (Nat.beq p1 q1) (Nat.beq p2 q2) = true := h
  cases h1 : Nat.beq p1 q1 <;> cases h2 : Nat.beq p2 q2 <;> rw [h1, h2] at h' <;>
    first | exact absurd h' Bool.false_ne_true | skip
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]

theorem pairOK_of {P : Pair} {p : Nat × Nat} {a b : Nat} (hP : PairOK P a b)
    (h : eqP p (a, b) = true) : PairOK P p.1 p.2 := by
  rw [eqP_eq h]
  exact hP

theorem prog_eq : max7Prog = CODES.map decodeK := by
  have hp := parseK_sound (eq_of_beq parse)
  rw [String.ofList_toList] at hp
  obtain ⟨p, hp1, hp2⟩ := Option.map_eq_some_iff.1 hp
  have hm : max7Prog = p := by
    unfold max7Prog
    rw [hp1]
    rfl
  rw [hm, ← hp2]
  simp only [List.map_map, Function.comp_def, decodeK_code, List.map_id']

theorem codes : max7Prog.map instrCode = CODES := by
  rw [prog_eq, List.map_map]
  decide +kernel

theorem lt9 : ∀ ins ∈ CODES.map decodeK, ins.lt 9 = true := by decide +kernel

theorem lt7 : ∀ ins ∈ CODES.map decodeK, ins.lt 7 = true := by decide +kernel

theorem regs9 : RegOK one (runProgN O (initRegsN O 9 An Bn) (CODES.map decodeK)) E9 := by
  have h := runPK_ok hK (CODES.map decodeK) CertificateChecks.KernelSporSch.J4Regs.init_ok lt9
  rwa [show CertificateChecks.KernelSporSch.J4Regs.INIT = INIT7 from rfl, eq_of_beq run] at h

theorem regs_agree : ∀ r < 7, (runProgN O (initRegsN O 9 An Bn) (CODES.map decodeK))[r]! =
    max7Regs[r]! := by
  rw [max7Regs, prog_eq]
  refine run_agree _ _ _ lt7 (by simp [initRegsN]) (by simp [initRegsN]) fun r hr => ?_
  rw [getElem!_pos _ r (by rw [initRegsN, Array.size_ofFn]; omega),
    getElem!_pos _ r (by rw [initRegsN, Array.size_ofFn]; omega)]
  simp [initRegsN]

theorem hH1 : PairOK H1n H1.1 H1.2 := by
  have h := regs9.2.2 1 (by omega)
  rw [regs_agree 1 (by omega)] at h
  have e1 : getN one E9 1 = H1.1 := Nat.eq_of_beq_eq_true (by quickRfl)
  have e2 : getN one E9 (9 + 1) = H1.2 := Nat.eq_of_beq_eq_true (by quickRfl)
  rw [e1, e2] at h
  exact h

theorem hH2 : PairOK H2n H2.1 H2.2 := by
  have h := regs9.2.2 2 (by omega)
  rw [regs_agree 2 (by omega)] at h
  have e1 : getN one E9 2 = H2.1 := Nat.eq_of_beq_eq_true (by quickRfl)
  have e2 : getN one E9 (9 + 2) = H2.2 := Nat.eq_of_beq_eq_true (by quickRfl)
  rw [e1, e2] at h
  exact h

theorem hXn : PairOK Xn XN.1 XN.2 := by
  have h1 : getN one M4 1 = getN one CertificateChecks.KernelSporSch.J4RG 1 :=
    Nat.eq_of_beq_eq_true (by quickRfl)
  have h2 : getN one M4 10 = getN one CertificateChecks.KernelSporSch.J4RG 10 :=
    Nat.eq_of_beq_eq_true (by quickRfl)
  have h := CertificateChecks.KernelSporSch.J4Regs.hX
  change PairOK Xn (getN one M4 1) (getN one M4 10)
  rw [h1, h2]
  exact h

theorem hYn : PairOK Yn YN.1 YN.2 := by
  have h1 : getN one M4 2 = getN one CertificateChecks.KernelSporSch.J4RG 2 :=
    Nat.eq_of_beq_eq_true (by quickRfl)
  have h2 : getN one M4 11 = getN one CertificateChecks.KernelSporSch.J4RG 11 :=
    Nat.eq_of_beq_eq_true (by quickRfl)
  have h := CertificateChecks.KernelSporSch.J4Regs.hY
  change PairOK Yn (getN one M4 2) (getN one M4 11)
  rw [h1, h2]
  exact h

theorem hS5 : PairOK S5n (V 0).1 (V 0).2 := pairOK_of (powP_ok hK hH2 8) d0

theorem hX0 : PairOK X0n (V 1).1 (V 1).2 :=
  pairOK_of (mulP_ok hK (mulP_ok hK (mulP_ok hK hS5 (invP_ok hH1)) (invP_ok hS5)) hH1) d1

theorem hY0 : PairOK Y0n (V 2).1 (V 2).2 :=
  pairOK_of (mulP_ok hK (mulP_ok hK (mulP_ok hK hS5 (mulP_ok hK hH1 hH2)) (invP_ok hS5))
    (invP_ok (mulP_ok hK hH1 hH2))) d2

theorem hQX : PairOK QXn (V 3).1 (V 3).2 := pairOK_of (mulP_ok hK hX0 (powP_ok hK hY0 7)) d3

theorem hQY : PairOK QYn (V 4).1 (V 4).2 := pairOK_of (powP_ok hK hY0 3) d4

theorem hQZ : PairOK QZn (V 5).1 (V 5).2 :=
  pairOK_of (mulP_ok hK (mulP_ok hK (mulP_ok hK hQX hQY) (invP_ok hQX)) (invP_ok hQY)) d5

theorem hU8 : PairOK U8n (V 6).1 (V 6).2 := pairOK_of (powP_ok hK hH2 5) d6

theorem hW2 : PairOK W2n (V 7).1 (V 7).2 :=
  pairOK_of (mulP_ok hK (mulP_ok hK (mulP_ok hK (powP_ok hK hQX 3) (powP_ok hK hQY 9)) hQZ)
    (wordP_ok' hK hH1 hH2 [1, 2, 1, 2, 2, 2, 2] (by decide))) d7

theorem hC23 : PairOK C23n (V 8).1 (V 8).2 :=
  pairOK_of (powP_okB hK (wordP_ok' hK hXn hYn [1, 2] (by decide)) (fuel := 25) (by norm_num)) d8

theorem hq (a b c : Nat) {k : Nat}
    (h : eqP (V k) (mP (mP (pP (V 3) a) (pP (V 4) b)) (pP (V 5) c)) = true) :
    PairOK (qWord a b c) (V k).1 (V k).2 :=
  pairOK_of (mulP_ok hK (mulP_ok hK (powP_ok hK hQX a) (powP_ok hK hQY b)) (powP_ok hK hQZ c)) h

theorem hQZ2 : PairOK (powP QZn 2) (V 13).1 (V 13).2 := pairOK_of (powP_ok hK hQZ 2) d13

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem conj_of {X Y W : Array Nat} {x y w : Nat} (hX : WfN X ∧ encN X = x) (hY : WfN Y ∧ encN Y = y)
    (hW : WfN W ∧ encN W = w) (h : Nat.beq (mulJ c rm x y) (mulJ c rm w x) = true) :
    O.conjOK X Y W = true := by
  obtain ⟨wX, rfl⟩ := hX
  obtain ⟨wY, rfl⟩ := hY
  obtain ⟨wW, rfl⟩ := hW
  exact eq_sound hK wX wY wW wX h

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native in
open CFSG.Sporadic.SmallF2.Native in
theorem facts : (max7Prog.map instrCode = [
      [0, 1, 2, 3], [0, 3, 2, 4], [0, 3, 4, 5], [0, 3, 5, 6], [0, 6, 4, 5], [2, 4, 4, 3],
      [2, 8, 5, 4], [1, 4, 5], [0, 5, 3, 6], [0, 6, 4, 3], [0, 1, 3, 4], [0, 4, 3, 5], [2, 3, 5, 6],
      [0, 4, 4, 5], [0, 6, 5, 3], [2, 6, 4, 5], [0, 5, 3, 4], [2, 20, 4, 3], [0, 3, 2, 5],
      [0, 2, 3, 6], [1, 6, 3], [0, 3, 5, 6], [2, 3, 6, 2], [0, 4, 2, 3], [0, 4, 3, 5], [2, 7, 5, 3],
      [1, 4, 5], [0, 5, 2, 6], [0, 2, 6, 5], [2, 8, 4, 2], [0, 2, 5, 6], [1, 6, 5], [0, 1, 4, 2],
      [0, 5, 3, 4], [0, 4, 6, 1]]
    )
    ∧ (max7Prog.all (Instr.lt 7) = true)
    ∧ (O.eq (O.mul QZn.1 QXn.1) (O.mul QXn.1 QZn.1) = true ∧
      O.eq (O.mul QZn.1 QYn.1) (O.mul QYn.1 QZn.1) = true ∧ O.vne (O.vmul (O.unit 0) QZn.1)
        (O.unit 0) = true
    )
    ∧ (expOK QXn.1 QYn.1 QZn.1 = true)
    ∧ (centerOK QXn.1 QYn.1 = true)
    ∧ (O.normalFormOK 11 [QXn.1, QYn.1, QZn.1] 0 = true)
    ∧ (O.conjOK H1n.1 QXn.1 (qWord 7 3 2).1 = true ∧
      O.conjOK H1n.1 QYn.1 (qWord 3 3 9).1 = true ∧ O.conjOK H1n.1 QZn.1 QZn.1 = true ∧
      O.conjOK H2n.1 QXn.1 (qWord 8 6 3).1 = true ∧ O.conjOK H2n.1 QYn.1 (qWord 10 5 8).1 = true ∧
      O.conjOK H2n.1 QZn.1 (O.pow QZn.1 2) = true
    )
    ∧ (fixDimOK QXn.1 fixP_qx fixPinv_qx fixR_qx 12 = true ∧
      fixDimOK QYn.1 fixP_qy fixPinv_qy fixR_qy 12 = true ∧
      fixDimOK QZn.1 fixP_qz fixPinv_qz fixR_qz 2 = true
    )
    ∧ (fixDimOK C23n.1 fixP_c23 fixPinv_c23 fixR_c23 2 = true)
    ∧ (O.eq (O.pow U8n.1 8) O.one = true ∧ O.eq (O.mul W2n.1 W2n.1) O.one = true ∧
      O.conjOK W2n.1 U8n.1 (O.pow U8n.1 3) = true ∧ sixteenOK U8n.1 W2n.1 = true
    )
    ∧ (∀ v : Fin 2 → ZMod 11, v ≠ 0 →
      evalW (fwdW v) ![1, 0] = v ∧ evalW (bwdW v) v = ![1, 0]
    ) := by
  obtain ⟨b1, b2, b3⟩ : _ ∧ _ ∧ _ := by
    have := basic
    simp only [andB_iff] at this
    exact this
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ := by
    have := conj
    simp only [andB_iff] at this
    exact this
  obtain ⟨s1, s2, s3, s4⟩ : _ ∧ _ ∧ _ ∧ _ := by
    have := six
    simp only [andB_iff] at this
    exact this
  have eX : encN QXn.1 = QX := hQX.1.2
  have eY : encN QYn.1 = QY := hQY.1.2
  have eZ : encN QZn.1 = QZ := hQZ.1.2
  refine ⟨codes, by rw [prog_eq]; exact lts, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← eX, ← eZ] at b1
    exact eq_sound hK hQZ.1.1 hQX.1.1 hQX.1.1 hQZ.1.1 b1
  · rw [← eY, ← eZ] at b2
    exact eq_sound hK hQZ.1.1 hQY.1.1 hQY.1.1 hQZ.1.1 b2
  · rw [← eZ] at b3
    exact vne_sound hK hQZ.1.1 b3
  · have h := exp
    rw [← eX, ← eY, ← eZ] at h
    exact expK_sound hK hQX.1.1 hQY.1.1 hQZ.1.1 h
  · have h := cen
    rw [← eX, ← eY] at h
    exact centerK_sound hK hQX.1.1 hQY.1.1 h
  · have h := nf
    rw [← eX, ← eY, ← eZ] at h
    exact distK_sound hK hQX.1.1 hQY.1.1 hQZ.1.1 h
  · exact conj_of hH1.1 hQX.1 (hq 7 3 2 d9).1 c1
  · exact conj_of hH1.1 hQY.1 (hq 3 3 9 d10).1 c2
  · exact conj_of hH1.1 hQZ.1 hQZ.1 c3
  · exact conj_of hH2.1 hQX.1 (hq 8 6 3 d11).1 c4
  · exact conj_of hH2.1 hQY.1 (hq 10 5 8 d12).1 c5
  · exact conj_of hH2.1 hQZ.1 hQZ2.1 c6
  · have h := fixX
    obtain ⟨wP, eP⟩ := pack_enc px
    obtain ⟨wI, eI⟩ := pack_enc ix
    obtain ⟨wR, eR⟩ := pack_enc rx
    rw [← eX, ← eP, ← eI, ← eR] at h
    exact fixK_sound hK hQX.1.1 wP wI wR (by norm_num) h
  · have h := fixY
    obtain ⟨wP, eP⟩ := pack_enc py
    obtain ⟨wI, eI⟩ := pack_enc iy
    obtain ⟨wR, eR⟩ := pack_enc ry
    rw [← eY, ← eP, ← eI, ← eR] at h
    exact fixK_sound hK hQY.1.1 wP wI wR (by norm_num) h
  · have h := fixZ
    obtain ⟨wP, eP⟩ := pack_enc pz
    obtain ⟨wI, eI⟩ := pack_enc iz
    obtain ⟨wR, eR⟩ := pack_enc rz
    rw [← eZ, ← eP, ← eI, ← eR] at h
    exact fixK_sound hK hQZ.1.1 wP wI wR (by norm_num) h
  · have h := fixC
    obtain ⟨wP, eP⟩ := pack_enc pc
    obtain ⟨wI, eI⟩ := pack_enc ic
    obtain ⟨wR, eR⟩ := pack_enc rc
    rw [← hC23.1.2, ← eP, ← eI, ← eR] at h
    exact fixK_sound hK hC23.1.1 wP wI wR (by norm_num) h
  · rw [← hU8.1.2] at s1
    exact pow_one_sound hK hU8.1.1 s1
  · rw [← hW2.1.2] at s2
    exact eq_one_sound hK hW2.1.1 hW2.1.1 s2
  · have m := pow_enc hK hU8.1.1 3
    exact conj_of hW2.1 hU8.1 ⟨m.1, m.2.trans (by rw [hU8.1.2])⟩ s3
  · rw [← hU8.1.2, ← hW2.1.2] at s4
    exact sixteenK_sound hK hU8.1.1 hW2.1.1 s4
  · decide +kernel

end CertificateChecks.KernelSporSch.J4E7

end

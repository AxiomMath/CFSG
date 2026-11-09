module

public import Certificates.Kernel.Ru4120.Fam
public import Certificates.Data.Kernel.Kc3DfsKB
import CFSG.Certificates.Kernel.Common.Harness

set_option maxHeartbeats 0

public section

namespace CFSG.KD.Ru4120

open CFSG.KC.Kc3K

@[expose] noncomputable def famSB (c : Nat) : Bool :=
  dfsKRB 687 pr NB NM (leafKB pr ct) (Nat.mul c 16) (min 16 (687 - Nat.mul c 16))

@[expose] noncomputable def famRt (r : Nat) : Bool := dfsKG 687 pr NB NM (leafKB pr ct) r

@[expose] noncomputable def famRJ (r j : Nat) : Bool :=
  !(g2B 687 pr r j) ||
    (fun K => (NB r).all fun k =>
      !(K.testBit k) || !(g3B 687 pr r j k) ||
        (fun L => (NB r).all fun l =>
          !(L.testBit l) || !(g4B 687 pr r j k l) || leafKB pr ct r j k l)
        (K &&& NM k &&& NM (pr r k) &&& NM (pr j k) &&& NM (pr (pr r j) k)))
    (NM r &&& NM j &&& NM (pr r j))

@[expose] noncomputable def famRc (r a b : Nat) : Bool := (((NB r).drop a).take b).all (famRJ r)

theorem famS0_eq (c : Nat) : famS0 c = famSB c :=
  dfsKR_eq 687 pr ct NB NM (Nat.mul c 16) (min 16 (687 - Nat.mul c 16))

theorem famRt_eq (r : Nat) : famRt r = (NB r).all (famRJ r) := rfl

theorem famRt_of_chunks (r b m : Nat) (hlen : (NB r).length ≤ m * b)
    (h : ∀ q < m, famRc r (q * b) b = true) : famRt r = true := by
  rw [famRt_eq, List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hc : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0
      rw [Nat.mul_zero] at hlen
      omega
    · exact h0
  have hj : i / b < m := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  have h1 := List.all_eq_true.1 (h (i / b) hj)
  apply h1
  have hmod : i % b < b := Nat.mod_lt _ hc
  have hi' : i / b * b + i % b = i := Nat.div_add_mod' i b
  have hlt : i % b < (((NB r).drop (i / b * b)).take b).length := by
    simp only [List.length_take, List.length_drop]
    omega
  rw [List.mem_iff_getElem]
  refine ⟨i % b, hlt, ?_⟩
  simp only [List.getElem_take, List.getElem_drop, hi']

theorem famSB_of_roots (c : Nat) (h : ∀ q < 16, famRt (Nat.mul c 16 + q) = true) :
    famSB c = true := by
  unfold famSB
  refine dfsKRB_of_singles fun q hq => h q ?_
  omega

namespace S0R

theorem r0 : famRt (nat_lit 0) = true := by quickRfl

theorem r1 : famRt (nat_lit 1) = true := by quickRfl

theorem r2 : famRt (nat_lit 2) = true := by quickRfl

theorem r3 : famRt (nat_lit 3) = true := by quickRfl

theorem r4 : famRt (nat_lit 4) = true := by quickRfl

theorem r5 : famRt (nat_lit 5) = true := by quickRfl

theorem r6 : famRt (nat_lit 6) = true := by quickRfl

theorem r7 : famRt (nat_lit 7) = true := by quickRfl

theorem r8 : famRt (nat_lit 8) = true := by quickRfl

theorem r9 : famRt (nat_lit 9) = true := by quickRfl

theorem r10 : famRt (nat_lit 10) = true := by quickRfl

theorem r11_0 : famRc (nat_lit 11) (nat_lit 0) (nat_lit 54) = true := by quickRfl

theorem r11_1 : famRc (nat_lit 11) (nat_lit 54) (nat_lit 54) = true := by quickRfl

theorem r11_2 : famRc (nat_lit 11) (nat_lit 108) (nat_lit 54) = true := by quickRfl

theorem r11_3 : famRc (nat_lit 11) (nat_lit 162) (nat_lit 54) = true := by quickRfl

theorem r11_4 : famRc (nat_lit 11) (nat_lit 216) (nat_lit 54) = true := by quickRfl

theorem r11_5 : famRc (nat_lit 11) (nat_lit 270) (nat_lit 54) = true := by quickRfl

theorem r11_6 : famRc (nat_lit 11) (nat_lit 324) (nat_lit 54) = true := by quickRfl

theorem r11_7 : famRc (nat_lit 11) (nat_lit 378) (nat_lit 54) = true := by quickRfl

theorem r11 : famRt (nat_lit 11) = true :=
  famRt_of_chunks _ 54 8 (Nat.le_of_ble_eq_true (by quickRfl)) fun q hq =>
    match q, hq with
    | 0, _ => r11_0
    | 1, _ => r11_1
    | 2, _ => r11_2
    | 3, _ => r11_3
    | 4, _ => r11_4
    | 5, _ => r11_5
    | 6, _ => r11_6
    | 7, _ => r11_7
    | _ + 8, h => absurd h (by omega)

theorem r12 : famRt (nat_lit 12) = true := by quickRfl

theorem r13 : famRt (nat_lit 13) = true := by quickRfl

theorem r14 : famRt (nat_lit 14) = true := by quickRfl

theorem r15 : famRt (nat_lit 15) = true := by quickRfl

theorem r16_0 : famRc (nat_lit 16) (nat_lit 0) (nat_lit 71) = true := by quickRfl

theorem r16_1 : famRc (nat_lit 16) (nat_lit 71) (nat_lit 71) = true := by quickRfl

theorem r16 : famRt (nat_lit 16) = true :=
  famRt_of_chunks _ 71 2 (Nat.le_of_ble_eq_true (by quickRfl)) fun q hq =>
    match q, hq with
    | 0, _ => r16_0
    | 1, _ => r16_1
    | _ + 2, h => absurd h (by omega)

theorem r17 : famRt (nat_lit 17) = true := by quickRfl

theorem r18 : famRt (nat_lit 18) = true := by quickRfl

theorem r19 : famRt (nat_lit 19) = true := by quickRfl

theorem r20 : famRt (nat_lit 20) = true := by quickRfl

theorem r21 : famRt (nat_lit 21) = true := by quickRfl

theorem r22 : famRt (nat_lit 22) = true := by quickRfl

theorem r23 : famRt (nat_lit 23) = true := by quickRfl

theorem r24 : famRt (nat_lit 24) = true := by quickRfl

theorem r25 : famRt (nat_lit 25) = true := by quickRfl

theorem r26 : famRt (nat_lit 26) = true := by quickRfl

theorem r27 : famRt (nat_lit 27) = true := by quickRfl

theorem r28 : famRt (nat_lit 28) = true := by quickRfl

theorem r29 : famRt (nat_lit 29) = true := by quickRfl

theorem r30_0 : famRc (nat_lit 30) (nat_lit 0) (nat_lit 47) = true := by quickRfl

theorem r30_1 : famRc (nat_lit 30) (nat_lit 47) (nat_lit 47) = true := by quickRfl

theorem r30 : famRt (nat_lit 30) = true :=
  famRt_of_chunks _ 47 2 (Nat.le_of_ble_eq_true (by quickRfl)) fun q hq =>
    match q, hq with
    | 0, _ => r30_0
    | 1, _ => r30_1
    | _ + 2, h => absurd h (by omega)

theorem r31 : famRt (nat_lit 31) = true := by quickRfl

theorem r32 : famRt (nat_lit 32) = true := by quickRfl

theorem r33 : famRt (nat_lit 33) = true := by quickRfl

theorem r34_0 : famRc (nat_lit 34) (nat_lit 0) (nat_lit 71) = true := by quickRfl

theorem r34_1 : famRc (nat_lit 34) (nat_lit 71) (nat_lit 71) = true := by quickRfl

theorem r34 : famRt (nat_lit 34) = true :=
  famRt_of_chunks _ 71 2 (Nat.le_of_ble_eq_true (by quickRfl)) fun q hq =>
    match q, hq with
    | 0, _ => r34_0
    | 1, _ => r34_1
    | _ + 2, h => absurd h (by omega)

theorem r35 : famRt (nat_lit 35) = true := by quickRfl

theorem r36 : famRt (nat_lit 36) = true := by quickRfl

theorem r37 : famRt (nat_lit 37) = true := by quickRfl

theorem r38 : famRt (nat_lit 38) = true := by quickRfl

theorem r39 : famRt (nat_lit 39) = true := by quickRfl

theorem r40 : famRt (nat_lit 40) = true := by quickRfl

theorem r41 : famRt (nat_lit 41) = true := by quickRfl

theorem r42 : famRt (nat_lit 42) = true := by quickRfl

theorem r43 : famRt (nat_lit 43) = true := by quickRfl

theorem r44 : famRt (nat_lit 44) = true := by quickRfl

theorem r45 : famRt (nat_lit 45) = true := by quickRfl

theorem r46 : famRt (nat_lit 46) = true := by quickRfl

theorem r47 : famRt (nat_lit 47) = true := by quickRfl

theorem r48 : famRt (nat_lit 48) = true := by quickRfl

theorem r49 : famRt (nat_lit 49) = true := by quickRfl

theorem r50 : famRt (nat_lit 50) = true := by quickRfl

theorem r51 : famRt (nat_lit 51) = true := by quickRfl

theorem r52 : famRt (nat_lit 52) = true := by quickRfl

theorem r53 : famRt (nat_lit 53) = true := by quickRfl

theorem r54 : famRt (nat_lit 54) = true := by quickRfl

theorem r55 : famRt (nat_lit 55) = true := by quickRfl

theorem r56 : famRt (nat_lit 56) = true := by quickRfl

theorem r57 : famRt (nat_lit 57) = true := by quickRfl

theorem r58 : famRt (nat_lit 58) = true := by quickRfl

theorem r59 : famRt (nat_lit 59) = true := by quickRfl

theorem r60 : famRt (nat_lit 60) = true := by quickRfl

theorem r61 : famRt (nat_lit 61) = true := by quickRfl

theorem r62 : famRt (nat_lit 62) = true := by quickRfl

theorem r63 : famRt (nat_lit 63) = true := by quickRfl

theorem r64 : famRt (nat_lit 64) = true := by quickRfl

theorem r65 : famRt (nat_lit 65) = true := by quickRfl

theorem r66 : famRt (nat_lit 66) = true := by quickRfl

theorem r67 : famRt (nat_lit 67) = true := by quickRfl

theorem r68 : famRt (nat_lit 68) = true := by quickRfl

theorem r69 : famRt (nat_lit 69) = true := by quickRfl

theorem r70 : famRt (nat_lit 70) = true := by quickRfl

theorem r71 : famRt (nat_lit 71) = true := by quickRfl

theorem r72 : famRt (nat_lit 72) = true := by quickRfl

theorem r73 : famRt (nat_lit 73) = true := by quickRfl

theorem r74 : famRt (nat_lit 74) = true := by quickRfl

theorem r75 : famRt (nat_lit 75) = true := by quickRfl

theorem r76 : famRt (nat_lit 76) = true := by quickRfl

theorem r77 : famRt (nat_lit 77) = true := by quickRfl

theorem r78 : famRt (nat_lit 78) = true := by quickRfl

theorem r79 : famRt (nat_lit 79) = true := by quickRfl

theorem r80_0 : famRc (nat_lit 80) (nat_lit 0) (nat_lit 103) = true := by quickRfl

theorem r80_1 : famRc (nat_lit 80) (nat_lit 103) (nat_lit 103) = true := by quickRfl

theorem r80 : famRt (nat_lit 80) = true :=
  famRt_of_chunks _ 103 2 (Nat.le_of_ble_eq_true (by quickRfl)) fun q hq =>
    match q, hq with
    | 0, _ => r80_0
    | 1, _ => r80_1
    | _ + 2, h => absurd h (by omega)

theorem r81 : famRt (nat_lit 81) = true := by quickRfl

theorem r82 : famRt (nat_lit 82) = true := by quickRfl

theorem r83 : famRt (nat_lit 83) = true := by quickRfl

theorem r84 : famRt (nat_lit 84) = true := by quickRfl

theorem r85 : famRt (nat_lit 85) = true := by quickRfl

theorem r86 : famRt (nat_lit 86) = true := by quickRfl

theorem r87 : famRt (nat_lit 87) = true := by quickRfl

theorem r88 : famRt (nat_lit 88) = true := by quickRfl

theorem r89 : famRt (nat_lit 89) = true := by quickRfl

theorem r90 : famRt (nat_lit 90) = true := by quickRfl

theorem r91 : famRt (nat_lit 91) = true := by quickRfl

theorem r92 : famRt (nat_lit 92) = true := by quickRfl

theorem r93 : famRt (nat_lit 93) = true := by quickRfl

theorem r94 : famRt (nat_lit 94) = true := by quickRfl

theorem r95 : famRt (nat_lit 95) = true := by quickRfl

theorem r96 : famRt (nat_lit 96) = true := by quickRfl

theorem r97 : famRt (nat_lit 97) = true := by quickRfl

theorem r98 : famRt (nat_lit 98) = true := by quickRfl

theorem r99 : famRt (nat_lit 99) = true := by quickRfl

theorem r100 : famRt (nat_lit 100) = true := by quickRfl

theorem r101_0 : famRc (nat_lit 101) (nat_lit 0) (nat_lit 103) = true := by quickRfl

theorem r101_1 : famRc (nat_lit 101) (nat_lit 103) (nat_lit 103) = true := by quickRfl

theorem r101 : famRt (nat_lit 101) = true :=
  famRt_of_chunks _ 103 2 (Nat.le_of_ble_eq_true (by quickRfl)) fun q hq =>
    match q, hq with
    | 0, _ => r101_0
    | 1, _ => r101_1
    | _ + 2, h => absurd h (by omega)

theorem r102 : famRt (nat_lit 102) = true := by quickRfl

theorem r103 : famRt (nat_lit 103) = true := by quickRfl

theorem r104 : famRt (nat_lit 104) = true := by quickRfl

theorem r105 : famRt (nat_lit 105) = true := by quickRfl

theorem r106 : famRt (nat_lit 106) = true := by quickRfl

theorem r107 : famRt (nat_lit 107) = true := by quickRfl

theorem r108 : famRt (nat_lit 108) = true := by quickRfl

theorem r109 : famRt (nat_lit 109) = true := by quickRfl

theorem r110 : famRt (nat_lit 110) = true := by quickRfl

theorem r111 : famRt (nat_lit 111) = true := by quickRfl

theorem r112 : famRt (nat_lit 112) = true := by quickRfl

theorem r113 : famRt (nat_lit 113) = true := by quickRfl

theorem r114 : famRt (nat_lit 114) = true := by quickRfl

theorem r115 : famRt (nat_lit 115) = true := by quickRfl

theorem r116 : famRt (nat_lit 116) = true := by quickRfl

theorem r117 : famRt (nat_lit 117) = true := by quickRfl

theorem r118 : famRt (nat_lit 118) = true := by quickRfl

theorem r119 : famRt (nat_lit 119) = true := by quickRfl

theorem r120 : famRt (nat_lit 120) = true := by quickRfl

theorem r121 : famRt (nat_lit 121) = true := by quickRfl

theorem r122 : famRt (nat_lit 122) = true := by quickRfl

theorem r123 : famRt (nat_lit 123) = true := by quickRfl

theorem r124 : famRt (nat_lit 124) = true := by quickRfl

theorem r125 : famRt (nat_lit 125) = true := by quickRfl

theorem r126 : famRt (nat_lit 126) = true := by quickRfl

theorem r127 : famRt (nat_lit 127) = true := by quickRfl

theorem r128 : famRt (nat_lit 128) = true := by quickRfl

theorem r129 : famRt (nat_lit 129) = true := by quickRfl

theorem r130 : famRt (nat_lit 130) = true := by quickRfl

theorem r131 : famRt (nat_lit 131) = true := by quickRfl

theorem r132 : famRt (nat_lit 132) = true := by quickRfl

theorem r133 : famRt (nat_lit 133) = true := by quickRfl

theorem r134 : famRt (nat_lit 134) = true := by quickRfl

theorem r135 : famRt (nat_lit 135) = true := by quickRfl

theorem r136 : famRt (nat_lit 136) = true := by quickRfl

theorem r137 : famRt (nat_lit 137) = true := by quickRfl

theorem r138 : famRt (nat_lit 138) = true := by quickRfl

theorem r139 : famRt (nat_lit 139) = true := by quickRfl

theorem r140 : famRt (nat_lit 140) = true := by quickRfl

theorem r141 : famRt (nat_lit 141) = true := by quickRfl

theorem r142 : famRt (nat_lit 142) = true := by quickRfl

theorem r143 : famRt (nat_lit 143) = true := by quickRfl

theorem r144 : famRt (nat_lit 144) = true := by quickRfl

theorem r145 : famRt (nat_lit 145) = true := by quickRfl

theorem r146 : famRt (nat_lit 146) = true := by quickRfl

theorem r147 : famRt (nat_lit 147) = true := by quickRfl

theorem r148 : famRt (nat_lit 148) = true := by quickRfl

theorem r149 : famRt (nat_lit 149) = true := by quickRfl

theorem r150 : famRt (nat_lit 150) = true := by quickRfl

theorem r151 : famRt (nat_lit 151) = true := by quickRfl

theorem r152 : famRt (nat_lit 152) = true := by quickRfl

theorem r153 : famRt (nat_lit 153) = true := by quickRfl

theorem r154 : famRt (nat_lit 154) = true := by quickRfl

theorem r155 : famRt (nat_lit 155) = true := by quickRfl

theorem r156 : famRt (nat_lit 156) = true := by quickRfl

theorem r157 : famRt (nat_lit 157) = true := by quickRfl

theorem r158 : famRt (nat_lit 158) = true := by quickRfl

theorem r159 : famRt (nat_lit 159) = true := by quickRfl

end S0R

namespace S0B

theorem c0 : famSB (nat_lit 0) = true :=
  famSB_of_roots _ fun q hq =>
    match q, hq with
    | 0, _ => S0R.r0
    | 1, _ => S0R.r1
    | 2, _ => S0R.r2
    | 3, _ => S0R.r3
    | 4, _ => S0R.r4
    | 5, _ => S0R.r5
    | 6, _ => S0R.r6
    | 7, _ => S0R.r7
    | 8, _ => S0R.r8
    | 9, _ => S0R.r9
    | 10, _ => S0R.r10
    | 11, _ => S0R.r11
    | 12, _ => S0R.r12
    | 13, _ => S0R.r13
    | 14, _ => S0R.r14
    | 15, _ => S0R.r15
    | _ + 16, h => absurd h (by omega)

theorem c1 : famSB (nat_lit 1) = true :=
  famSB_of_roots _ fun q hq =>
    match q, hq with
    | 0, _ => S0R.r16
    | 1, _ => S0R.r17
    | 2, _ => S0R.r18
    | 3, _ => S0R.r19
    | 4, _ => S0R.r20
    | 5, _ => S0R.r21
    | 6, _ => S0R.r22
    | 7, _ => S0R.r23
    | 8, _ => S0R.r24
    | 9, _ => S0R.r25
    | 10, _ => S0R.r26
    | 11, _ => S0R.r27
    | 12, _ => S0R.r28
    | 13, _ => S0R.r29
    | 14, _ => S0R.r30
    | 15, _ => S0R.r31
    | _ + 16, h => absurd h (by omega)

theorem c2 : famSB (nat_lit 2) = true :=
  famSB_of_roots _ fun q hq =>
    match q, hq with
    | 0, _ => S0R.r32
    | 1, _ => S0R.r33
    | 2, _ => S0R.r34
    | 3, _ => S0R.r35
    | 4, _ => S0R.r36
    | 5, _ => S0R.r37
    | 6, _ => S0R.r38
    | 7, _ => S0R.r39
    | 8, _ => S0R.r40
    | 9, _ => S0R.r41
    | 10, _ => S0R.r42
    | 11, _ => S0R.r43
    | 12, _ => S0R.r44
    | 13, _ => S0R.r45
    | 14, _ => S0R.r46
    | 15, _ => S0R.r47
    | _ + 16, h => absurd h (by omega)

theorem c3 : famSB (nat_lit 3) = true :=
  famSB_of_roots _ fun q hq =>
    match q, hq with
    | 0, _ => S0R.r48
    | 1, _ => S0R.r49
    | 2, _ => S0R.r50
    | 3, _ => S0R.r51
    | 4, _ => S0R.r52
    | 5, _ => S0R.r53
    | 6, _ => S0R.r54
    | 7, _ => S0R.r55
    | 8, _ => S0R.r56
    | 9, _ => S0R.r57
    | 10, _ => S0R.r58
    | 11, _ => S0R.r59
    | 12, _ => S0R.r60
    | 13, _ => S0R.r61
    | 14, _ => S0R.r62
    | 15, _ => S0R.r63
    | _ + 16, h => absurd h (by omega)

theorem c4 : famSB (nat_lit 4) = true :=
  famSB_of_roots _ fun q hq =>
    match q, hq with
    | 0, _ => S0R.r64
    | 1, _ => S0R.r65
    | 2, _ => S0R.r66
    | 3, _ => S0R.r67
    | 4, _ => S0R.r68
    | 5, _ => S0R.r69
    | 6, _ => S0R.r70
    | 7, _ => S0R.r71
    | 8, _ => S0R.r72
    | 9, _ => S0R.r73
    | 10, _ => S0R.r74
    | 11, _ => S0R.r75
    | 12, _ => S0R.r76
    | 13, _ => S0R.r77
    | 14, _ => S0R.r78
    | 15, _ => S0R.r79
    | _ + 16, h => absurd h (by omega)

theorem c5 : famSB (nat_lit 5) = true :=
  famSB_of_roots _ fun q hq =>
    match q, hq with
    | 0, _ => S0R.r80
    | 1, _ => S0R.r81
    | 2, _ => S0R.r82
    | 3, _ => S0R.r83
    | 4, _ => S0R.r84
    | 5, _ => S0R.r85
    | 6, _ => S0R.r86
    | 7, _ => S0R.r87
    | 8, _ => S0R.r88
    | 9, _ => S0R.r89
    | 10, _ => S0R.r90
    | 11, _ => S0R.r91
    | 12, _ => S0R.r92
    | 13, _ => S0R.r93
    | 14, _ => S0R.r94
    | 15, _ => S0R.r95
    | _ + 16, h => absurd h (by omega)

theorem c6 : famSB (nat_lit 6) = true :=
  famSB_of_roots _ fun q hq =>
    match q, hq with
    | 0, _ => S0R.r96
    | 1, _ => S0R.r97
    | 2, _ => S0R.r98
    | 3, _ => S0R.r99
    | 4, _ => S0R.r100
    | 5, _ => S0R.r101
    | 6, _ => S0R.r102
    | 7, _ => S0R.r103
    | 8, _ => S0R.r104
    | 9, _ => S0R.r105
    | 10, _ => S0R.r106
    | 11, _ => S0R.r107
    | 12, _ => S0R.r108
    | 13, _ => S0R.r109
    | 14, _ => S0R.r110
    | 15, _ => S0R.r111
    | _ + 16, h => absurd h (by omega)

theorem c7 : famSB (nat_lit 7) = true :=
  famSB_of_roots _ fun q hq =>
    match q, hq with
    | 0, _ => S0R.r112
    | 1, _ => S0R.r113
    | 2, _ => S0R.r114
    | 3, _ => S0R.r115
    | 4, _ => S0R.r116
    | 5, _ => S0R.r117
    | 6, _ => S0R.r118
    | 7, _ => S0R.r119
    | 8, _ => S0R.r120
    | 9, _ => S0R.r121
    | 10, _ => S0R.r122
    | 11, _ => S0R.r123
    | 12, _ => S0R.r124
    | 13, _ => S0R.r125
    | 14, _ => S0R.r126
    | 15, _ => S0R.r127
    | _ + 16, h => absurd h (by omega)

theorem c8 : famSB (nat_lit 8) = true :=
  famSB_of_roots _ fun q hq =>
    match q, hq with
    | 0, _ => S0R.r128
    | 1, _ => S0R.r129
    | 2, _ => S0R.r130
    | 3, _ => S0R.r131
    | 4, _ => S0R.r132
    | 5, _ => S0R.r133
    | 6, _ => S0R.r134
    | 7, _ => S0R.r135
    | 8, _ => S0R.r136
    | 9, _ => S0R.r137
    | 10, _ => S0R.r138
    | 11, _ => S0R.r139
    | 12, _ => S0R.r140
    | 13, _ => S0R.r141
    | 14, _ => S0R.r142
    | 15, _ => S0R.r143
    | _ + 16, h => absurd h (by omega)

theorem c9 : famSB (nat_lit 9) = true :=
  famSB_of_roots _ fun q hq =>
    match q, hq with
    | 0, _ => S0R.r144
    | 1, _ => S0R.r145
    | 2, _ => S0R.r146
    | 3, _ => S0R.r147
    | 4, _ => S0R.r148
    | 5, _ => S0R.r149
    | 6, _ => S0R.r150
    | 7, _ => S0R.r151
    | 8, _ => S0R.r152
    | 9, _ => S0R.r153
    | 10, _ => S0R.r154
    | 11, _ => S0R.r155
    | 12, _ => S0R.r156
    | 13, _ => S0R.r157
    | 14, _ => S0R.r158
    | 15, _ => S0R.r159
    | _ + 16, h => absurd h (by omega)

theorem c10 : famSB (nat_lit 10) = true := by quickRfl

end S0B

namespace S0

theorem c0 : famS0 (nat_lit 0) = true := (famS0_eq (nat_lit 0)).trans S0B.c0

theorem c1 : famS0 (nat_lit 1) = true := (famS0_eq (nat_lit 1)).trans S0B.c1

theorem c2 : famS0 (nat_lit 2) = true := (famS0_eq (nat_lit 2)).trans S0B.c2

theorem c3 : famS0 (nat_lit 3) = true := (famS0_eq (nat_lit 3)).trans S0B.c3

theorem c4 : famS0 (nat_lit 4) = true := (famS0_eq (nat_lit 4)).trans S0B.c4

theorem c5 : famS0 (nat_lit 5) = true := (famS0_eq (nat_lit 5)).trans S0B.c5

theorem c6 : famS0 (nat_lit 6) = true := (famS0_eq (nat_lit 6)).trans S0B.c6

theorem c7 : famS0 (nat_lit 7) = true := (famS0_eq (nat_lit 7)).trans S0B.c7

theorem c8 : famS0 (nat_lit 8) = true := (famS0_eq (nat_lit 8)).trans S0B.c8

theorem c9 : famS0 (nat_lit 9) = true := (famS0_eq (nat_lit 9)).trans S0B.c9

theorem c10 : famS0 (nat_lit 10) = true := (famS0_eq (nat_lit 10)).trans S0B.c10

theorem all : ∀ (i : Nat), i < 11 → famS0 i = true := fun i hi =>
  match i, hi with
  | 0, _ => c0
  | 1, _ => c1
  | 2, _ => c2
  | 3, _ => c3
  | 4, _ => c4
  | 5, _ => c5
  | 6, _ => c6
  | 7, _ => c7
  | 8, _ => c8
  | 9, _ => c9
  | 10, _ => c10
  | _ + 11, h => absurd h (by omega)

end S0

end CFSG.KD.Ru4120

end

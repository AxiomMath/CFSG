module

public import Certificates.Kernel.SporSch.Tits.Common
public import Certificates.Kernel.Sporadic.Tits.LocS
public import CFSG.Sporadic.Schreier.TitsQTCheckInputs
meta import CFSG.Sporadic.Schreier.TitsQTCheckInputs
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.TitsCentralCheck
meta import CFSG.Sporadic.Schreier.TitsCentralCheck

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelSporSch.TitsQX 11 CFSG.Sporadic.Schreier.TitsQT.conjXArr
#ks_perm CertificateChecks.KernelSporSch.TitsQY 11 CFSG.Sporadic.Schreier.TitsQT.conjYArr

namespace CertificateChecks.KernelSporSch.TitsQT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.Schreier.TitsQT CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsCommon

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def gP : Nat :=
  pc (pc (pc (pc (TitsD.SI 1) (TitsD.S 0)) (TitsD.SI 1)) (TitsD.S 0)) (TitsD.S 0)

@[expose] noncomputable def gIP : Nat :=
  pc (pc (pc (pc (TitsD.SI 0) (TitsD.SI 0)) (TitsD.S 1)) (TitsD.SI 0)) (TitsD.S 1)

theorem xK : Nat.beq (pc (pc gP TitsZ) gIP) TitsQX = true := by quickRfl
theorem yK : Nat.beq (pc (pc (TitsD.SI 0) TitsZ) (TitsD.S 0)) TitsQY = true := by quickRfl

abbrev C (p : Nat) : Prop := canonK 1755 11 (mask 11) (1755 * 11) p = true

theorem cc {p q : Nat} (hp : C p) (hq : C q) : C (pc p q) := canonK_pcomp hp hq

theorem cu {p q : Nat} (hp : C p) (hq : C q) :
    compA 1755 (unpack 1755 11 p) (unpack 1755 11 q) = unpack 1755 11 (pc p q) :=
  compA_unpack hp hq

theorem s0 : C (TitsD.S 0) := canonS (by norm_num)
theorem s1 : C (TitsD.S 1) := canonS (by norm_num)
theorem i0 : C (TitsD.SI 0) := canonSI (by norm_num)
theorem i1 : C (TitsD.SI 1) := canonSI (by norm_num)

theorem cg : C gP := cc (cc (cc (cc i1 s0) i1) s0) s0
theorem cgi : C gIP := cc (cc (cc (cc i0 i0) s1) i0) s1

theorem g_eq : conjGArr = unpack 1755 11 gP := by
  unfold conjGArr conjD1Inv conjD1 conjD0
  rw [derInv_eq (j := 1) (by norm_num), der_eq (j := 0) (by norm_num), cu i1 s0, cu (cc i1 s0) i1, cu (cc (cc i1 s0) i1) s0,
    cu (cc (cc (cc i1 s0) i1) s0) s0]
  rfl

theorem gi_eq : conjGInvArr = unpack 1755 11 gIP := by
  unfold conjGInvArr conjD0Inv conjD1 conjD0
  rw [derInv_eq (j := 0) (by norm_num), der_eq (j := 1) (by norm_num), cu i0 i0,
    cu (cc i0 i0) s1, cu (cc (cc i0 i0) s1) i0, cu (cc (cc (cc i0 i0) s1) i0) s1]
  rfl

theorem x_eq : conjXArr = unpack 1755 11 TitsQX := by
  unfold conjXArr
  rw [g_eq, gi_eq, z_eq, cu cg canonZ, cu (cc cg canonZ) cgi, Nat.eq_of_beq_eq_true xK]

theorem y_eq : conjYArr = unpack 1755 11 TitsQY := by
  unfold conjYArr conjD0Inv conjD0
  rw [derInv_eq (j := 0) (by norm_num), der_eq (j := 0) (by norm_num), z_eq, cu i0 canonZ,
    cu (cc i0 canonZ) s0, Nat.eq_of_beq_eq_true yK]

theorem cx : C TitsQX := by quickRfl
theorem cy : C TitsQY := by quickRfl

theorem sx : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsS.LR TitsS.TRI TitsS.BP 5 0
    TitsQX = true := by quickRfl
theorem sy : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsS.LR TitsS.TRI TitsS.BP 5 0
    TitsQY = true := by quickRfl
theorem pxy : Nat.beq (pg 11 (mask 11) (pc TitsQX TitsQY) 12) 115 = true := by quickRfl
theorem pyx : Nat.beq (pg 11 (mask 11) (pc TitsQY TitsQX) 12) 117 = true := by quickRfl

theorem hx : Nat.beq (Nat.shiftRight TitsQX (1755 * 11)) 0 = true := by quickRfl
theorem hy : Nat.beq (Nat.shiftRight TitsQY (1755 * 11)) 0 = true := by quickRfl

theorem facts : siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0 conjXArr = true ∧
    siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0 conjYArr = true ∧
    (compA 1755 conjXArr conjYArr)[12]! = 115 ∧
    (compA 1755 conjYArr conjXArr)[12]! = 117 := by
  refine ⟨siftK_soundR bindsS permS TitsS.hl x_eq (Nat.eq_of_beq_eq_true hx) (range_of_canonK cx)
      sx,
    siftK_soundR bindsS permS TitsS.hl y_eq (Nat.eq_of_beq_eq_true hy) (range_of_canonK cy) sy,
    ?_, ?_⟩
  · rw [x_eq, y_eq, cu cx cy, unpack_get (by norm_num)]
    exact Nat.eq_of_beq_eq_true pxy
  · rw [x_eq, y_eq, cu cy cx, unpack_get (by norm_num)]
    exact Nat.eq_of_beq_eq_true pyx

end CertificateChecks.KernelSporSch.TitsQT

end

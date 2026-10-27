
module

public import Certificates.Kernel.SporSch.J4S.KsK
public import Certificates.Kernel.SporSch.J4S.NoCPBase
public import Certificates.Kernel.J4Q.Mat
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4KsP

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11 CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native CFSG.SectionRank.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Eta
open CertificateChecks.KernelSporSch.J4NoCK CertificateChecks.KernelSporSch.J4KsK
open CertificateChecks.KernelSporSch.J4InvP CertificateChecks.KernelSporSch.J4NoCP

theorem matChecks_of (h : CFSG.Sporadic.J4.MatFacts) :
    CFSG.Sporadic.J4.Native.matChecks = true := by
  unfold CFSG.Sporadic.J4.Native.matChecks
  simp only [h.locFix]
  simp only [h.baseInv, h.locInv, h.locSize, h.stabSize, h.a2, h.a1, h.b4, h.b2, h.ab37,
    h.ab1, h.cinv, h.z43, h.z1, h.formA, h.formB]
  decide

theorem band_eq (a b : Bool) : (a && b) = Bool.rec (motive := fun _ => Bool) false b a := by
  cases a <;> rfl

theorem vmul_eq (v : Nat) (X : Array Nat) : O.vmul v X = vecMulN 112 X v := rfl

@[expose] def Enc (X : Array Nat) (P : Nat) : Prop := WfN X ∧ encN X = P

theorem sqK_eq : ∀ {xs : List (Array Nat)} {ps : List Nat}, List.Forall₂ Enc xs ps →
    xs.all (CFSG.Sporadic.GLQ.sqOK O) = sqK ps
  | [], [], _ => rfl
  | X :: xs, P :: ps, List.Forall₂.cons hX h => by
    rw [List.all_cons, sqK_eq h, band_eq]
    have m := mul_enc J4Real.hK hX.1 hX.1
    have e : CFSG.Sporadic.GLQ.sqOK O X = Nat.beq (mulJ c rm P P) one := by
      change (O.mul X X == idRows 112) = _
      have hI := CFSG.KS.SporSch.J4B.id_enc J4Real.hK
      rw [beq_enc m.1 hI.1, m.2, hI.2, hX.2]
    rw [e]
    rfl

theorem commK_eq {X : Array Nat} {P : Nat} (hX : Enc X P) :
    ∀ {xs : List (Array Nat)} {ps : List Nat}, List.Forall₂ Enc xs ps →
      xs.all (O.commOK X) = commK P ps
  | [], [], _ => rfl
  | Y :: xs, Q :: ps, List.Forall₂.cons hY h => by
    rw [List.all_cons, commK_eq hX h, band_eq]
    have m1 := mul_enc J4Real.hK hX.1 hY.1
    have m2 := mul_enc J4Real.hK hY.1 hX.1
    have e : O.commOK X Y = Nat.beq (mulJ c rm P Q) (mulJ c rm Q P) := by
      change (O.mul X Y == O.mul Y X) = _
      rw [beq_enc m1.1 m2.1, m1.2, m2.2, hX.2, hY.2]
    rw [e]
    rfl

theorem commsK_eq : ∀ {xs : List (Array Nat)} {ps : List Nat}, List.Forall₂ Enc xs ps →
    O.commsOK xs = commsK ps
  | [], [], _ => rfl
  | X :: xs, P :: ps, List.Forall₂.cons hX h => by
    rw [Ops.commsOK, commK_eq hX h, commsK_eq h, band_eq]
    rfl

theorem appBK_eq : ∀ {xs : List (Array Nat)} {ps : List Nat}, List.Forall₂ Enc xs ps →
    ∀ n v, O.appBase 2 xs n v = appBK ps n v
  | [], [], _, _, _ => rfl
  | X :: xs, P :: ps, List.Forall₂.cons hX h, n, v => by
    rw [Ops.appBase, appBK_eq h]
    change _ = appBK ps (n / 2)
      (Bool.rec (motive := fun _ => Nat) v (vecJ rm v P) (Nat.beq (n % 2) 1))
    have h2 : n % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases h1 : n % 2 = 1
    · rw [h1, beq_iff.2 rfl]
      congr 1
      rw [Ops.app, Ops.app, vmul_eq]
      rw [vec_enc J4Real.hK hX.1, hX.2]
    · have h0 : n % 2 = 0 := by omega
      rw [h0, beqF (by omega : (0 : Nat) ≠ 1)]
      rfl

theorem hU : List.Forall₂ Enc (List.ofFn fun j : Fin 11 => (Un j).1) UL := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [UL], fun k h1 h2 => ?_⟩
  simp only [UL, List.get_eq_getElem, List.getElem_ofFn]
  exact (pU _).1

theorem sq_ok : (List.ofFn fun j : Fin 11 => (Un j).1).all (CFSG.Sporadic.GLQ.sqOK O) = true := by
  rw [sqK_eq hU]
  exact sq

theorem comm_ok : O.commsOK (List.ofFn fun j : Fin 11 => (Un j).1) = true := by
  rw [commsK_eq hU]
  exact comm

theorem ker_ok : CFSG.Sporadic.GLQ.kerOK2 O (List.ofFn fun j : Fin 11 => (Un j).1) [0] = true := by
  unfold CFSG.Sporadic.GLQ.kerOK2
  rw [List.all_eq_true]
  intro n hn
  rw [List.length_ofFn, List.mem_range] at hn
  have hn' : n < 2047 := by simpa using hn
  rw [List.any_cons, List.any_nil, Bool.or_false, appBK_eq hU, vne_eq]
  exact allN_spec ker n hn'

theorem xc_get {j : Nat} (hj : j < 11) : xColumns[j]! = ent 11 J4X j := by
  rw [bindW_sound J4X.bind, unpackW_get hj]

theorem yc_get {j : Nat} (hj : j < 11) : yColumns[j]! = ent 11 J4Y j := by
  rw [bindW_sound J4Y.bind, unpackW_get hj]

theorem kv_eq : ksetVectors = tabA 11385 J4KV.T := by
  rw [ksetVectors, ksetSize, J4KV.eq, CFSG.KS.SporSch.tokK_sound J4KV.tok]
  exact natsK_sound pV

theorem ke_get {i k : Nat} (hi : i < 11385) (hk : k < 2) :
    (ksetEdges[i]!)[k]! = ent 14 (J4KE.T i) k := by
  rw [ksetEdges, ksetSize, J4KE.eq, CFSG.KS.SporSch.tokK_sound J4KE.tok, (permsK_sound pE).2 i hi,
    unpackW_get hk]

theorem kw_eq : O.vmul ksetVectors[0]! Zn.1 = kw := by
  rw [vmul_eq, vec_enc J4Real.hK pZ.1.1, pZ.1.2, kv_eq, tabA_get (by omega)]
  rfl

theorem facts : (rootCheck = true)
    ∧ (colsCheck = true)
    ∧ (elemCheck = true)
    ∧ (O.vmul ksetVectors[0]! Zn.1 < 2 ^ 112)
    ∧ (∀ i < ksetSize, ksetVectors[i]! < 2 ^ 112 ∧ (ksetEdges[i]!)[0]! < ksetSize ∧
      ksetVectors[(ksetEdges[i]!)[0]!]! = O.vmul ksetVectors[i]! Xn.1 ∧
      (ksetEdges[i]!)[1]! < ksetSize ∧
      ksetVectors[(ksetEdges[i]!)[1]!]! = O.vmul ksetVectors[i]! Yn.1 ∧
      ksetVectors[i]! ≠ O.vmul ksetVectors[0]! Zn.1)
    ∧ (CFSG.Sporadic.J4.Native.matChecks = true)
    ∧ (comp11 xColumns xInvColumns = CFSG.Sporadic.SmallF2.Native.idRows 11)
    ∧ (comp11 yColumns yInvColumns = CFSG.Sporadic.SmallF2.Native.idRows 11) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 5
  · exact matChecks_of CertificateChecks.KernelJ4Q.matFacts
  rotate_right 5
  · obtain ⟨r1, r⟩ := (bAnd_iff (Nat.beq (vecJ rm rootBits (R 1)) rootBits)
      (bAnd(Nat.beq (vecJ rm rootBits (R 2)) rootBits,
        Nat.beq (vecJ rm rootBits (E 1)) rootBits))).1 root
    obtain ⟨r2, r3⟩ := (bAnd_iff (Nat.beq (vecJ rm rootBits (R 2)) rootBits)
      (Nat.beq (vecJ rm rootBits (E 1)) rootBits)).1 r
    unfold rootCheck
    rw [vmul_eq, vmul_eq, vmul_eq, vec_enc J4Real.hK pX.1.1, vec_enc J4Real.hK pY.1.1,
      vec_enc J4Real.hK pZ.1.1, pX.1.2, pY.1.2, pZ.1.2, beq_iff.1 r1, beq_iff.1 r2, beq_iff.1 r3]
    simp
  · unfold colsCheck
    rw [List.all_eq_true]
    intro j _
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec cols j j.isLt)
    have px := mulP_ok J4Real.hK (mulP_ok J4Real.hK pX (pU j)) (invP_ok pX)
    have py := mulP_ok J4Real.hK (mulP_ok J4Real.hK pY (pU j)) (invP_ok pY)
    have ex := etaP_ok xColumns[j]!
    have ey := etaP_ok yColumns[j]!
    have xg : xColumns[j]! = ent 11 J4X j := xc_get j.isLt
    have yg : yColumns[j]! = ent 11 J4Y j := yc_get j.isLt
    have e1 : ∀ X Y : Array Nat, O.eq X Y = (X == Y) := fun _ _ => rfl
    rw [Bool.and_eq_true, e1, e1, beq_enc px.1.1 ex.1.1, beq_enc py.1.1 ey.1.1, px.1.2, ex.1.2,
      py.1.2, ey.1.2, xg, yg]
    exact ⟨h1, h2⟩
  · unfold elemCheck CFSG.Sporadic.GLQ.elem2OK
    rw [sq_ok, comm_ok, ker_ok]
    rfl
  · rw [kw_eq]
    exact blt_iff.1 ksw
  · intro i hi
    have hi' : i < 11385 := hi
    have h := slice_spec (k := 1024) (S := 12) (by omega) J4KSV.all i (by omega)
    unfold ksK at h
    rw [bIf_t (blt_iff.2 hi')] at h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h
    have l2 := blt_iff.1 h2
    have l4 := blt_iff.1 h4
    have vx : O.vmul ksetVectors[i]! Xn.1 = vecJ rm (J4KV.T i) (R 1) := by
      rw [vmul_eq, vec_enc J4Real.hK pX.1.1, pX.1.2, kv_eq, tabA_get hi']
    have vy : O.vmul ksetVectors[i]! Yn.1 = vecJ rm (J4KV.T i) (R 2) := by
      rw [vmul_eq, vec_enc J4Real.hK pY.1.1, pY.1.2, kv_eq, tabA_get hi']
    rw [vx, vy, kw_eq, ke_get hi' (by omega), ke_get hi' (by omega), ksetSize, kv_eq,
      tabA_get hi', tabA_get l2, tabA_get l4]
    refine ⟨blt_iff.1 h1, l2, beq_iff.1 h3, l4, beq_iff.1 h5, fun e => ?_⟩
    rw [e, beq_iff.2 rfl] at h6
    exact absurd h6 (by decide)
  · rw [bindW_sound J4X.bind, bindW_sound J4XI.bind]
    change comp11 (unpack11 J4X) (unpack11 J4XI) = _
    rw [comp_eq, CFSG.KS.SporSch.C11.id_eq, beq_iff.1 cx]
  · rw [bindW_sound J4Y.bind, bindW_sound J4YI.bind]
    change comp11 (unpack11 J4Y) (unpack11 J4YI) = _
    rw [comp_eq, CFSG.KS.SporSch.C11.id_eq, beq_iff.1 cy]

end CertificateChecks.KernelSporSch.J4KsP

end

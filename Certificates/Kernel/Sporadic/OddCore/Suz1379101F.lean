module

public import Certificates.Kernel.Sporadic.OddCore.Suz1379101J
public import Certificates.Kernel.Sporadic.OddCore.Suz26990F
public import Certificates.Data.SuzSylowFacts
import CFSG.Certificates.Kernel.Spor.BaseMaskGlue

public section

namespace CertificateChecks.KernelSpor.S1379101

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.Sporadic.SuzOddCore.SylowFacts CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

abbrev Cn (p : Nat) : Prop := canonK 1782 11 (mask 11) (1782 * 11) p = true

theorem ok_spec {p : Nat} (h : ok p = true) :
    Cn p ∧ Cn (pinv p) ∧ CFSG.KC.Enum.permOK 1782 11 (mask 11) (1782 * 11) p (pinv p) = true := by
  unfold ok cn at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem cpc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) := CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem compA_u {p q : Nat} (hp : Cn p) (hq : Cn q) :
    compA 1782 (unpack 1782 11 p) (unpack 1782 11 q) = unpack 1782 11 (pc p q) :=
  S26990.compA_u hp hq

theorem comp_u {p q : Nat} (hp : Cn p) (hq : Cn q) :
    comp 1782 (unpack 1782 11 p) (unpack 1782 11 q) = unpack 1782 11 (pc p q) := by
  rw [CFSG.KC.PermTool.comp_eq]
  exact compA_u hp hq

theorem inv_u {a : Array Nat} {P : Nat} (ha : a = unpack 1782 11 P)
    (h : CFSG.KC.Enum.permOK 1782 11 (mask 11) (1782 * 11) P (pinv P) = true) :
    invCand 1782 a = unpack 1782 11 (pinv P) ∧ isInvA 1782 a (invCand 1782 a) = true :=
  S26990.inv_u ha h

theorem idT : idTab 1782 = unpack 1782 11 e := by
  rw [CFSG.KC.PermTool.idTab_eq]
  exact S26990.hidA

theorem cE : Cn e := S26990.cE

theorem beq_u {p q : Nat} (hp : Cn p) (hq : Cn q) :
    (unpack 1782 11 p == unpack 1782 11 q) = Nat.beq p q := by
  by_cases h : p = q
  · subst h
    rw [Nat.beq_refl]
    exact beq_self_eq_true _
  · rw [Bool.eq_false_iff.2 fun hb => h (Nat.eq_of_beq_eq_true hb)]
    refine beq_eq_false_iff_ne.2 fun e' => h (Nat.eq_of_beq_eq_true ?_)
    rw [← S26990.eqA_u hp hq, ← e', S26990.eqA_u hp hp, Nat.beq_refl]

theorem mperm_of_ok {P : Nat} (h : ok P = true) :
    CFSG.Sporadic.SuzOddCore.permOK 1782 (unpack 1782 11 P) = true := by
  obtain ⟨-, -, hp⟩ := ok_spec h
  unfold CFSG.Sporadic.SuzOddCore.permOK
  rw [(inv_u rfl hp).2, CFSG.KC.L34KSnd.size_unpack]
  rfl

theorem commA_u {u v : Array Nat} {U V : Nat} (hu : u = unpack 1782 11 U)
    (hv : v = unpack 1782 11 V) (pu : ok U = true) (pv : ok V = true) :
    commA u v = unpack 1782 11 (CA U V) := by
  obtain ⟨cU, cUI, pU⟩ := ok_spec pu
  obtain ⟨cV, cVI, pV⟩ := ok_spec pv
  unfold commA
  rw [(inv_u hu pU).1, (inv_u hv pV).1, hu, hv, compA_u cU cV, compA_u (cpc cU cV) cUI,
    compA_u (cpc (cpc cU cV) cUI) cVI]
  rfl

theorem ofFn_get {α : Type} [Inhabited α] {m : Nat} (f : Fin m → α) {j : Nat} (hj : j < m) :
    (Array.ofFn f)[j]! = f ⟨j, hj⟩ := by
  rw [getElem!_pos (Array.ofFn f) j (by simpa using hj), Array.getElem_ofFn]

theorem map_get {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α) {j : Nat}
    (hj : j < a.size) : (a.map f)[j]! = f a[j]! := by
  rw [getElem!_pos (a.map f) j (by simpa using hj), Array.getElem_map, getElem!_pos a j hj]

theorem allB {m : Nat} {f : Nat → Bool} (h : ∀ i < m, f i = true) : allBelow m f = true :=
  CFSG.KS.BfsReplay.allBelow_iff.2 h

theorem tri0 : TRI 0 = Suz2306.B0 := by decide +kernel

theorem tri1 : TRI 1 = Suz2306.B1 := by decide +kernel

theorem tri2 : TRI 2 = Suz2306.V := by decide +kernel

theorem tri_bind : suzTriple.size = 3 ∧ ∀ j < 3, suzTriple[j]! = unpack 1782 11 (TRI j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · rw [tri0]
    simpa [suzTriple] using Suz2306.b0Arr_eq
  · rw [tri1]
    simpa [suzTriple] using Suz2306.b1Arr_eq
  · rw [tri2]
    simpa [suzTriple] using Suz2306.vArr_eq

theorem tri_p : ∀ j < 3, CFSG.KC.Enum.permOK 1782 11 (mask 11) (1782 * 11) (TRI j) (TRII j) = true :=
  fun j hj => by
    have h := kTriAll j hj
    unfold kTri at h
    simp only [Bool.and_eq_true] at h
    exact h.2.2

theorem ev_eq {wd : List Int} (hl : lettersK 3 wd = true) : ev wd = unpack 1782 11 (W3 wd) := by
  unfold ev W3
  have hi : suzTripleInv () = rawInvs 1782 suzTriple := rfl
  rw [hi]
  exact S26990.word_of tri_bind tri_p hl

theorem wEq_spec {wd : List Int} {X : Nat} (h : wEq wd X = true) :
    ev wd = unpack 1782 11 X ∧ ok X = true := by
  unfold wEq at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hl, hw, hX⟩ := h
  rw [ev_eq hl, Nat.eq_of_beq_eq_true hw]
  exact ⟨rfl, hX⟩

theorem rWords_eq : rWords = RW := by decide +kernel
theorem g2uWords_eq : g2uWords = G2U := by decide +kernel
theorem g2vWords_eq : g2vWords = G2V := by decide +kernel
theorem g3uWords_eq : g3uWords = G3U := by decide +kernel
theorem g3vWords_eq : g3vWords = G3V := by decide +kernel
theorem qWords_eq : suzQWords = QW := by decide +kernel
theorem cWords_eq : cWords = CWd := by decide +kernel
theorem waWord_eq : waWord = WA := by decide +kernel
theorem wbWord_eq : wbWord = WB := by decide +kernel

theorem rA_size : (rArrs ()).size = 4 := by unfold rArrs; simp

theorem rA_facts {j : Nat} (hj : j < 4) :
    (rArrs ())[j]! = unpack 1782 11 (RG j) ∧ ok (RG j) = true := by
  unfold rArrs
  rw [ofFn_get _ hj, rWords_eq]
  have h := kRWAll j hj
  unfold kRW at h
  exact wEq_spec h

theorem g2u_facts {j : Nat} (hj : j < 7) :
    (g2uArrs ())[j]! = unpack 1782 11 (fr j) ∧ ok (fr j) = true ∧ r32 FR j < 8192 := by
  unfold g2uArrs
  rw [ofFn_get _ hj, g2uWords_eq]
  have h := kU2All j hj
  unfold kU2 at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨(wEq_spec h.2).1, (wEq_spec h.2).2, h.1⟩

theorem g2v_facts {j : Nat} (hj : j < 7) :
    (g2vArrs ())[j]! = unpack 1782 11 (fr (7 + j)) ∧ ok (fr (7 + j)) = true ∧
      r32 FR (7 + j) < 8192 := by
  unfold g2vArrs
  rw [ofFn_get _ hj, g2vWords_eq]
  have h := kV2All j hj
  unfold kV2 at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨(wEq_spec h.2).1, (wEq_spec h.2).2, h.1⟩

theorem g3u_facts {k : Nat} (hk : k < 5) :
    (g3uArrs ())[k]! = unpack 1782 11 (fr (14 + k)) ∧ ok (fr (14 + k)) = true ∧
      r32 FR (14 + k) < 8192 := by
  unfold g3uArrs
  rw [ofFn_get _ hk, g3uWords_eq]
  have h := kU3All k hk
  unfold kU3 at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨(wEq_spec h.2).1, (wEq_spec h.2).2, h.1⟩

theorem g3v_facts {k : Nat} (hk : k < 5) :
    (g3vArrs ())[k]! = unpack 1782 11 (f2 k) ∧ ok (f2 k) = true ∧ r32 F2 k < 512 := by
  unfold g3vArrs
  rw [ofFn_get _ hk, g3vWords_eq]
  have h := kV3All k hk
  unfold kV3 at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨(wEq_spec h.2).1, (wEq_spec h.2).2, h.1⟩

theorem q_facts {i : Nat} (hi : i < 3) :
    (qArrs ())[i]! = unpack 1782 11 (QG i) ∧ ok (QG i) = true ∧ r32 FR (19 + i) < 8192 ∧
      QG i = fr (19 + i) := by
  unfold qArrs
  rw [ofFn_get _ hi, qWords_eq]
  have h := kQAll i hi
  unfold kQ at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨(wEq_spec h.2.1).1, (wEq_spec h.2.1).2, h.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem c_facts {i : Nat} (hi : i < 6) :
    (cArrs ())[i]! = unpack 1782 11 (CW i) ∧ ok (CW i) = true := by
  unfold cArrs
  rw [ofFn_get _ hi, cWords_eq]
  have h := kCwAll i hi
  unfold kCw at h
  exact wEq_spec h

theorem n2_facts {j : Nat} (hj : j < 7) :
    (n2Arrs ())[j]! = unpack 1782 11 (N2G j) ∧ ok (N2G j) = true := by
  have h := kG2All j hj
  unfold kG2 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨u1, u2, -⟩ := g2u_facts hj
  obtain ⟨v1, v2, -⟩ := g2v_facts hj
  unfold n2Arrs n2ArrOf
  rw [ofFn_get _ hj]
  refine ⟨?_, h.2⟩
  rw [commA_u u1 v1 u2 v2, Nat.eq_of_beq_eq_true h.1]

theorem n3_facts {k : Nat} (hk : k < 5) :
    (n3Arrs ())[k]! = unpack 1782 11 (N3G k) ∧ ok (N3G k) = true := by
  have h := kG3All k hk
  unfold kG3 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨u1, u2, -⟩ := g3u_facts hk
  obtain ⟨v1, v2, -⟩ := g3v_facts hk
  unfold n3Arrs n3ArrOf
  rw [ofFn_get _ hk]
  refine ⟨?_, h.2⟩
  rw [commA_u u1 v1 u2 v2, Nat.eq_of_beq_eq_true h.1]

theorem rI_get {j : Nat} (hj : j < 4) :
    ((rArrs ()).map (invCand 1782))[j]! = unpack 1782 11 (pinv (RG j)) := by
  rw [map_get _ _ (by rw [rA_size]; exact hj)]
  exact (inv_u (rA_facts hj).1 (ok_spec (rA_facts hj).2).2.2).1

theorem hdAll : (penumHdK e 8192 8192 RT RPL && (penumHdK e 512 512 N2T N2PL &&
    (penumHdK e 64 64 N3T N3PL && penumHdK e 8 8 QT QPL))) = true := kOne3

theorem hd_parts : penumHdK e 8192 8192 RT RPL = true ∧ penumHdK e 512 512 N2T N2PL = true ∧
    penumHdK e 64 64 N3T N3PL = true ∧ penumHdK e 8 8 QT QPL = true := by
  have h := hdAll
  simp only [Bool.and_eq_true] at h
  exact h

theorem ptR : ∀ i < 8192,
    penumPtK 1782 11 (mask 11) (1782 * 11) false RG RG 4 8192 RT RPL RPOS RSRT RSRI i = true :=
  fun i hi => CFSG.KS.BaseMask.penumSl_spec (rSlAll (i / 32) (by have : i / 32 < 256 := (by omega); exact this))
    (by change i / 32 * 32 ≤ i; omega) (by change i < i / 32 * 32 + 32; omega) hi

theorem pt2 : ∀ i < 512,
    penumPtK 1782 11 (mask 11) (1782 * 11) false N2G N2G 7 512 N2T N2PL N2POS N2SRT N2SRI i = true :=
  fun i hi => CFSG.KS.BaseMask.penumSl_spec (n2SlAll (i / 32) (by have : i / 32 < 16 := (by omega); exact this))
    (by change i / 32 * 32 ≤ i; omega) (by change i < i / 32 * 32 + 32; omega) hi

theorem pt3 : ∀ i < 64,
    penumPtK 1782 11 (mask 11) (1782 * 11) false N3G N3G 5 64 N3T N3PL N3POS N3SRT N3SRI i = true :=
  fun i hi => CFSG.KS.BaseMask.penumSl_spec (n3SlAll (i / 32) (by have : i / 32 < 2 := (by omega); exact this))
    (by change i / 32 * 32 ≤ i; omega) (by change i < i / 32 * 32 + 32; omega) hi

theorem ptQ : ∀ i < 8,
    penumPtK 1782 11 (mask 11) (1782 * 11) false QG QG 3 8 QT QPL QPOS QSRT QSRI i = true :=
  fun i hi => CFSG.KS.BaseMask.penumSl_spec (qSlAll 0 (by have : 0 < 1 := (by omega); exact this))
    (by change 0 * 32 ≤ i; omega) (by change i < 0 * 32 + 32; omega) hi

theorem encR : rEnum () = penumRec 1782 11 8192 RT RPL ∧
    enumOK 1782 (rArrs ()) (penumRec 1782 11 8192 RT RPL) = true :=
  penumK_left_sound S26990.hsz
    ⟨rA_size, fun j hj => ⟨(rA_facts hj).1, (ok_spec (rA_facts hj).2).1⟩⟩ hd_parts.1 ptR

theorem enc2 : n2Enum () = penumRec 1782 11 512 N2T N2PL ∧
    enumOK 1782 (n2Arrs ()) (penumRec 1782 11 512 N2T N2PL) = true :=
  penumK_left_sound S26990.hsz
    ⟨by unfold n2Arrs n2ArrOf; simp, fun j hj => ⟨(n2_facts hj).1, (ok_spec (n2_facts hj).2).1⟩⟩
    hd_parts.2.1 pt2

theorem enc3 : n3Enum () = penumRec 1782 11 64 N3T N3PL ∧
    enumOK 1782 (n3Arrs ()) (penumRec 1782 11 64 N3T N3PL) = true :=
  penumK_left_sound S26990.hsz
    ⟨by unfold n3Arrs n3ArrOf; simp, fun j hj => ⟨(n3_facts hj).1, (ok_spec (n3_facts hj).2).1⟩⟩
    hd_parts.2.2.1 pt3

theorem encQ : qEnum () = penumRec 1782 11 8 QT QPL ∧
    enumOK 1782 (qArrs ()) (penumRec 1782 11 8 QT QPL) = true :=
  penumK_left_sound S26990.hsz
    ⟨by unfold qArrs; simp, fun j hj => ⟨(q_facts hj).1, (ok_spec (q_facts hj).2.1).1⟩⟩
    hd_parts.2.2.2 ptQ

theorem rec_size (c : Nat) (T PL : Nat → Nat) : (penumRec 1782 11 c T PL).tabs.size = c := by
  simp [penumRec]

end CertificateChecks.KernelSpor.S1379101

end

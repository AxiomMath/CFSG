module

public import Certificates.Kernel.SporSch.J4S.Regs
public import CFSG.Certificates.Kernel.SporSch.J4SPairSound
meta import Certificates.Kernel.SporSch.J4S.EtaData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_pairs CertificateChecks.KernelSporSch.J4EP CertificateChecks.KernelSporSch.J4Eta.etaData

namespace CertificateChecks.KernelSporSch.J4Eta

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Regs

@[expose] noncomputable def R (r : Nat) : Nat := getN one J4RG r

@[expose] noncomputable def E (k : Nat) : Nat := getN one J4EP k

@[expose] noncomputable def d1 : Nat :=
  mulJ c rm (mulJ c rm (powJ c rm one (mulJ c rm (R 2) (R 1)) 4) (R 11)) (R 1)
@[expose] noncomputable def d2 : Nat :=
  mulJ c rm (R 10) (mulJ c rm (R 2) (powJ c rm one (mulJ c rm (R 10) (R 11)) 4))

@[expose] noncomputable def z1 : Nat :=
  powJ c rm one (mulJ c rm (mulJ c rm (mulJ c rm (R 2) (E 24)) (R 3)) (E 0)) 3
@[expose] noncomputable def z2 : Nat :=
  powJ c rm one (mulJ c rm (E 24) (mulJ c rm (R 12) (mulJ c rm (E 0) (R 11)))) 3

@[expose] def ncL : List (List Int) := List.ofFn normalConjugators

@[expose] noncomputable def cK (j : Nat) : Bool :=
  bAnd(Nat.beq (wFK c rm one (R 1) (R 10) (R 2) (R 11) (ncL.getD j []) one) (E (Nat.add 2 j)),
    Nat.beq (wSK c rm one (R 1) (R 10) (R 2) (R 11) (ncL.getD j []) one) (E (Nat.add 26 j)))

@[expose] noncomputable def uK (j : Nat) : Bool :=
  bAnd(Nat.beq (mulJ c rm (mulJ c rm (E (Nat.add 26 j)) (E 1)) (E (Nat.add 2 j))) (E (Nat.add 13 j)),
    Nat.beq (mulJ c rm (E (Nat.add 26 j)) (mulJ c rm (E 25) (E (Nat.add 2 j)))) (E (Nat.add 37 j)))

theorem dk : bAnd(Nat.beq d1 (E 0), Nat.beq d2 (E 24)) = true := by quickRfl
theorem zk : bAnd(Nat.beq z1 (E 1), Nat.beq z2 (E 25)) = true := by quickRfl
theorem ck : allN 11 cK = true := by quickRfl
theorem uk : allN 11 uK = true := by quickRfl

theorem nc_get (j : Fin 11) : ncL.getD j.val [] = normalConjugators j := by
  rw [ncL, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

theorem lettersC : ∀ j : Fin 11, ∀ l ∈ normalConjugators j, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by
  decide +kernel

theorem ofEq {P : Pair} {a b a' b' : Nat} (h : PairOK P a b) (ha : a = a') (hb : b = b') :
    PairOK P a' b' := by
  rw [← ha, ← hb]
  exact h

theorem pX : PairOK Xn (R 1) (R 10) := hX
theorem pY : PairOK Yn (R 2) (R 11) := hY
theorem pT : PairOK Tn (R 3) (R 12) := hT

theorem pD : PairOK Dn (E 0) (E 24) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff (Nat.beq d1 (E 0)) (Nat.beq d2 (E 24))).1 dk
  exact ofEq (mulP_ok J4Real.hK (mulP_ok J4Real.hK (powP_ok J4Real.hK
    (mulP_ok J4Real.hK pY pX) 4) (invP_ok pY)) pX)
    (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)

theorem pZ : PairOK Zn (E 1) (E 25) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff (Nat.beq z1 (E 1)) (Nat.beq z2 (E 25))).1 zk
  exact ofEq (powP_ok J4Real.hK (mulP_ok J4Real.hK (mulP_ok J4Real.hK (mulP_ok J4Real.hK pY
    (invP_ok pD)) pT) pD) 3) (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)

theorem pC (j : Fin 11) : PairOK (Cn j) (E (2 + j.val)) (E (26 + j.val)) := by
  have h := allN_spec ck j.val j.isLt
  unfold cK at h
  rw [nc_get] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ofEq (wordP_ok' J4Real.hK pX pY (normalConjugators j) (lettersC j))
    (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)

theorem pU (j : Fin 11) : PairOK (Un j) (E (13 + j.val)) (E (37 + j.val)) := by
  have h := allN_spec uk j.val j.isLt
  unfold uK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ofEq (mulP_ok J4Real.hK (mulP_ok J4Real.hK (invP_ok (pC j)) pZ) (pC j))
    (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)

@[expose] noncomputable def ef (i : Nat) : List Nat :=
  List.ofFn fun j : Fin 11 => if i.testBit j.val then E (13 + j.val) else one
@[expose] noncomputable def es (i : Nat) : List Nat :=
  List.ofFn fun j : Fin 11 => if i.testBit j.val then E (37 + j.val) else one

theorem etaP_ok (i : Nat) :
    PairOK (etaP i) (prodFK c rm one (ef i)) (prodSK c rm one (es i)) := by
  refine prodP_ok J4Real.hK _ _ _ (by simp [ef]) (by simp [es]) fun k hk => ?_
  have hk' : k < 11 := by simpa using hk
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_ofFn, ef, es,
    List.getElem!_eq_getElem?_getD, List.getElem?_ofFn, List.getElem!_eq_getElem?_getD,
    List.getElem?_ofFn]
  simp only [hk', ↓reduceDIte, Option.getD_some]
  split_ifs
  · exact pU ⟨k, hk'⟩
  · exact oneP_ok J4Real.hK

end CertificateChecks.KernelSporSch.J4Eta

end

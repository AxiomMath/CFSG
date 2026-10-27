module

public import CFSG.Sporadic.ONOddCore.NonextCheckInputs
public import Certificates.Kernel.Sporadic.OddCore.ON2120G

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2119

open CFSG.ONSchreier.Native hiding posArr
open CFSG.ONSchreier CFSG.Sporadic.ON.Native CFSG.Sporadic.ONOddCore
open CFSG.KS.TW CFSG.KS.PW CertificateChecks.KernelSpor.ON3 CFSG.KS
open CFSG.KC.Enum hiding pcomp

@[expose] def InvMaps (k : Nat) (G GI : Nat → Nat → Nat) : Prop :=
  ∀ i < k, ∀ y < 245520, G i y < 245520 ∧ GI i y < 245520 ∧ GI i (G i y) = y

theorem gsF_inv {k : Nat} {G GI : Nat → Nat → Nat} (h : InvMaps k G GI) (i : Nat) {y : Nat}
    (hy : y < 245520) : gsF k G i y < 245520 ∧ gsF k GI i (gsF k G i y) = y := by
  by_cases hi : i < k
  · rw [gsF_lt hi, gsF_lt hi]
    exact ⟨(h i hi y hy).1, (h i hi y hy).2.2⟩
  · rw [gsF_ge hi, gsF_ge hi]
    exact ⟨hy, rfl⟩

theorem wordF_inv {k : Nat} {G GI : Nat → Nat → Nat} (h : InvMaps k G GI) :
    ∀ (w : List Nat) (x : Nat), x < 245520 →
      wordF k G w x < 245520 ∧ wordF k GI w.reverse (wordF k G w x) = x
  | [], x, hx => ⟨hx, rfl⟩
  | l :: w, x, hx => by
    obtain ⟨h1, h2⟩ := wordF_inv h w x hx
    obtain ⟨h3, h4⟩ := gsF_inv h (Nat.sub l 1) h1
    have e1 : wordF k G (l :: w) x = gsF k G (Nat.sub l 1) (wordF k G w x) := rfl
    have e2 : ∀ y, wordF k GI (l :: w).reverse y = wordF k GI w.reverse (gsF k GI (Nat.sub l 1) y) :=
      fun y => by simp [wordF, List.reverse_cons, List.foldr_append]
    rw [e1, e2, h4]
    exact ⟨h3, h2⟩

theorem wordF_lt {k : Nat} {G GI : Nat → Nat → Nat} (h : InvMaps k G GI) (w : List Nat)
    {x : Nat} (hx : x < 245520) : wordF k GI w x < 245520 := by
  induction w with
  | nil => exact hx
  | cons l w ih =>
    change gsF k GI (Nat.sub l 1) (wordF k GI w x) < 245520
    by_cases hi : Nat.sub l 1 < k
    · rw [gsF_lt hi]
      exact (h _ hi _ ih).2.1
    · rw [gsF_ge hi]
      exact ih

section G


theorem good_posInv {gs : Array (Array Nat)} {G GI : Nat → Nat → Nat}
    (hg : ∀ i < gs.size, Good gs[i]! (G i)) (hi : InvMaps gs.size G GI) (w : List Nat) :
    Good (pinvCand nPts (posArr nPts gs w)) (wordF gs.size GI w.reverse) ∧
      pisInv nPts (posArr nPts gs w) (pinvCand nPts (posArr nPts gs w)) = true :=
  good_inv (good_posArr hg w) fun x hx =>
    ⟨wordF_lt hi w.reverse hx, (wordF_inv hi w x hx).2⟩

theorem good_conjArr {y yi x : Array Nat} {Y YI X : Nat → Nat} (hy : Good y Y) (hyi : Good yi YI)
    (hx : Good x X) : Good (conjArr y yi x) (fun p => Y (X (YI p))) :=
  good_pcomp hy (good_pcomp hx hyi)

theorem good_c : Good cArr CT := good_tab (good_word (by decide)) c_get

theorem good_ci : Good (pinvCand nPts cArr) CIT :=
  (good_inv good_c fun _ hx => ⟨(c_CI hx).2, (tab_facts hx).2.2.2.1⟩).1

theorem good_cConj {x : Array Nat} {X : Nat → Nat} (hx : Good x X) :
    Good (cConj x) (fun p => CT (X (CIT p))) :=
  good_conjArr good_c good_ci hx

theorem good_t : Good tArr (DT 0) := good_tab (good_word (by decide)) t_get

theorem good_z' : Good zArr ZT := good_tab (good_word (by decide)) z_get

theorem good_vArr : Good vArr (fun p => CIT (ZT (CT p))) := good_pcomp good_ci (good_pcomp good_z' good_c)

theorem good_d {j : Nat} (hj : j < 4) : Good (wordArrs Data.intersectionWords)[j]! (DT j) := by
  have hw : plettersOK 7 Data.intersectionWords[j]! = true := by interval_cases j <;> decide
  have h := good_word hw
  have hs : Data.intersectionWords.size = 4 := by decide +kernel
  rw [← wordArrs_get (by rw [hs]; exact hj)] at h
  exact good_tab h (d_get hj)

theorem good_dConj {j : Nat} (hj : j < 4) : Good dConj[j]! (fun p => CIT (DT j (CT p))) := by
  have e : dConj[j]! = pcomp nPts (pinvCand nPts cArr) (pcomp nPts (wordArrs Data.intersectionWords)[j]! cArr) := by
    unfold dConj
    rw [getElem!_pos _ j (by simp [wordArrs, CFSG.ONSchreier.pwords_eq]; exact hj), Array.getElem_map,
      ← getElem!_pos _ j (by simp [wordArrs, CFSG.ONSchreier.pwords_eq]; exact hj)]
  rw [e]
  exact good_pcomp good_ci (good_pcomp (good_d hj) good_c)

@[expose] noncomputable def ambF (i x : Nat) : Nat := nIf(Nat.blt i 3, mG i x, CT (mG (i - 3) (CIT x)))

theorem amb_size : (ambArrs (wordArrs Data.MWords)).size = 6 := by
  simp [ambArrs, mwords_size]

theorem good_amb : ∀ i < (ambArrs (wordArrs Data.MWords)).size,
    Good (ambArrs (wordArrs Data.MWords))[i]! (ambF i) := by
  intro i hi
  rw [amb_size] at hi
  unfold ambArrs
  rw [getElem!_pos _ i (by simp [mwords_size]; omega)]
  by_cases h3 : i < 3
  · rw [Array.getElem_append_left (by rw [mwords_size]; exact h3),
      ← getElem!_pos _ i (by rw [mwords_size]; exact h3)]
    have e : ambF i = mG i := by
      funext x
      unfold ambF
      have hb : Nat.blt i 3 = true := by rw [Nat.blt_eq]; exact h3
      rw [hb]
    rw [e]
    exact good_hA h3
  · rw [Array.getElem_append_right (by rw [mwords_size]; omega)]
    simp only [Array.getElem_map, mwords_size]
    have e : ambF i = fun x => CT (mG (i - 3) (CIT x)) := by
      funext x
      unfold ambF
      have hb : Nat.blt i 3 = false := by
        cases hc : Nat.blt i 3 with
        | false => rfl
        | true => rw [Nat.blt_eq] at hc; exact absurd hc h3
      rw [hb]
    rw [e, ← getElem!_pos _ (i - 3) (by rw [mwords_size]; omega)]
    exact good_cConj (good_hA (by omega))

theorem hA_inv : InvMaps (wordArrs Data.MWords).size mG mGI := by
  rw [mwords_size]
  intro i hi y hy
  exact ⟨(mG_pair i hi y hy).1, (mG_pair i hi y hy).2.1, (mG_pair i hi y hy).2.2.1⟩

theorem good_liftArrs {e : LiftEntry} {j : Nat} (hj : j < e.words.length) :
    Good (liftArrs (wordArrs Data.MWords) e)[j]! (wordF 3 mG (e.words.getD j [])) := by
  unfold liftArrs
  rw [getElem!_pos _ j (by simpa using hj)]
  simp only [List.getElem_toArray, List.getElem_map]
  have eg : e.words.getD j [] = e.words[j] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  rw [← eg]
  have h := good_posArr (fun i hi => good_hA (by rwa [mwords_size] at hi)) (e.words.getD j [])
  rwa [mwords_size] at h

end G

end CertificateChecks.KernelSpor.ON2119

end

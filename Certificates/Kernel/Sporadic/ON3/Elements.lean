
module

public import Certificates.Kernel.Sporadic.ON3.Tabs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON3

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.KS.TW CFSG.KS.PW CFSG.KS.Words
open CertificateChecks.KernelSpor.ON (TT UU TT_lt UU_lt)
open CFSG.Sporadic.ON.Native (nPts)

theorem arr_of {k : Nat} (hk : k < 17) {T : Nat → Nat} (hT : ∀ x < 245520, T x = trW k x) :
    ∀ x < 245520, (wordArr (wordL.getD k []))[x]! = T x ∧ T x < 245520 := by
  intro x hx
  obtain ⟨e, hlt⟩ := wordArr_get (let7 hk) hx
  have et : T x = (wordL.getD k []).foldr (GZ TT UU) x := by
    rw [hT x hx, trW_eq, dec_eq (by omega)]
  rw [e, et]
  exact ⟨rfl, hlt⟩

theorem z_get : ∀ x < 245520, zArr[x]! = ZT x ∧ ZT x < 245520 :=
  arr_of (k := 0) (by norm_num) fun _ hx => (tab_facts hx).1

theorem q_get : ∀ x < 245520, qArr[x]! = QT x ∧ QT x < 245520 :=
  arr_of (k := 1) (by norm_num) fun _ hx => (tab_facts hx).2.1

theorem c_get : ∀ x < 245520, cArr[x]! = CT x ∧ CT x < 245520 :=
  arr_of (k := 2) (by norm_num) fun _ hx => (tab_facts hx).2.2.1

theorem d_get {j : Nat} (hj : j < 4) :
    ∀ x < 245520, ((wordArrs Data.intersectionWords)[j]!)[x]! = DT j x ∧ DT j x < 245520 := by
  intro x hx
  rw [wordArrs_get (Nat.lt_of_lt_of_eq hj rfl)]
  interval_cases j
  · exact arr_of (k := 3) (T := DT 0) (by norm_num) (fun y hy => (tab_facts hy).2.2.2.2.1) x hx
  · exact arr_of (k := 4) (T := DT 1) (by norm_num) (fun y hy => (tab_facts hy).2.2.2.2.2.1) x hx
  · exact arr_of (k := 5) (T := DT 2) (by norm_num) (fun y hy => (tab_facts hy).2.2.2.2.2.2.1) x hx
  · exact arr_of (k := 6) (T := DT 3) (by norm_num)
      (fun y hy => (tab_facts hy).2.2.2.2.2.2.2.1) x hx

theorem t_get : ∀ x < 245520, tArr[x]! = DT 0 x ∧ DT 0 x < 245520 := by
  intro x hx
  have e : tArr = (wordArrs Data.intersectionWords)[0]! := by
    rw [wordArrs_get (ws := Data.intersectionWords) (j := 0) (by decide)]
    rfl
  rw [e]
  exact d_get (by norm_num) x hx

theorem m_get {j : Nat} (hj : j < 3) :
    ∀ x < 245520, ((wordArrs Data.MWords)[j]!)[x]! = mG j x ∧ mG j x < 245520 := by
  intro x hx
  rw [wordArrs_get (Nat.lt_of_lt_of_eq hj rfl)]
  interval_cases j
  · exact z_get x hx
  · exact arr_of (k := 7) (by norm_num) (fun y hy => (tab_facts hy).2.2.2.2.2.2.2.2.1) x hx
  · exact arr_of (k := 8) (by norm_num) (fun y hy => (tab_facts hy).2.2.2.2.2.2.2.2.2.1) x hx

theorem l_get {j : Nat} (hj : j < 2) :
    ∀ x < 245520, ((wordArrs Data.LWords)[j]!)[x]! = lG j x ∧ lG j x < 245520 := by
  intro x hx
  rw [wordArrs_get (Nat.lt_of_lt_of_eq hj rfl)]
  interval_cases j
  · exact arr_of (k := 9) (by norm_num) (fun y hy => (tab_facts hy).2.2.2.2.2.2.2.2.2.2.1) x hx
  · exact arr_of (k := 10) (by norm_num)
      (fun y hy => (tab_facts hy).2.2.2.2.2.2.2.2.2.2.2.1) x hx

theorem c_CI {y : Nat} (hy : y < 245520) : CT (CIT y) = y ∧ CIT y < 245520 := by
  obtain ⟨x, hx, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range 245520)
    (t := Finset.range 245520) (fun x _ => CT x)
    (fun x hx => Finset.mem_range.2 (c_get x (Finset.mem_range.1 hx)).2)
    (fun a b ha hb hab => calc
      a = CIT (CT a) := ((tab_facts (Finset.mem_range.1 ha)).2.2.2.1).symm
      _ = CIT (CT b) := congrArg CIT hab
      _ = b := (tab_facts (Finset.mem_range.1 hb)).2.2.2.1)
    le_rfl y (Finset.mem_range.2 hy)
  have hx' : x < 245520 := Finset.mem_range.1 hx
  rw [e, (tab_facts hx').2.2.2.1]
  exact ⟨rfl, hx'⟩

theorem ci_get : ∀ y < 245520, (pinvCand nPts cArr)[y]! = CIT y ∧ CIT y < 245520 := by
  intro y hy
  have hs : cArr.size = 245520 := pword_size _
  rw [arr_ext hs fun x hx => (c_get x hx).1]
  exact ⟨CFSG.KS.CB.pinvCand_get (fun x hx => (c_get x hx).2)
    (fun x hx => (tab_facts hx).2.2.2.1) hy, (c_CI hy).2⟩

end CertificateChecks.KernelSpor.ON3

end
